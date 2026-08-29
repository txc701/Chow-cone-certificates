"""Candidate uniform nonnegative certificate for the k=4 divergence target.

The construction starts from an exact signed primitive identity involving
peel parameters 2, 3, and 4.  Every negative peel-4 move is then eliminated
by a finite sum of equal-endpoint path differences.  The resulting raw flow
uses only support-cover edges of peel width at most three.

This module is an executable transcription of the proposed all-d formula; its
finite checks are corroboration, not the symbolic proof.
"""

from __future__ import annotations

import argparse
from collections import defaultdict
from dataclasses import dataclass
import hashlib
import json
from pathlib import Path
from typing import DefaultDict, Iterator

from k4_certificates import EdgeKey, allowed_edge_keys
from k4_feature_analysis import g_value, variance_statistic
from k4_weights import support_w4
from support import support_compositions


RawFlow = dict[EdgeKey, int]


@dataclass(frozen=True)
class PrimitiveMove:
    parent: tuple[int, ...]
    block_index: int
    split: int
    child: tuple[int, ...]
    peel_parameter: int
    role: str

    @property
    def edge(self) -> EdgeKey:
        return self.parent, self.block_index, self.split


def _child(
    parent: tuple[int, ...], block_index: int, split: int
) -> tuple[int, ...]:
    block = parent[block_index]
    return (
        parent[:block_index]
        + (split, block - split)
        + parent[block_index + 1 :]
    )


def primitive_moves(
    parent: tuple[int, ...], peel_parameter: int
) -> Iterator[PrimitiveMove]:
    """Yield selected F_s moves, retaining coincident final multiplicities."""
    if peel_parameter not in {2, 3, 4}:
        raise ValueError("peel parameter must be 2, 3, or 4")
    final_index = len(parent) - 1
    for block_index, block in enumerate(parent):
        if block < peel_parameter + 2:
            continue
        split = peel_parameter
        yield PrimitiveMove(
            parent=parent,
            block_index=block_index,
            split=split,
            child=_child(parent, block_index, split),
            peel_parameter=peel_parameter,
            role=("final_left" if block_index == final_index else "nonfinal_left"),
        )
        if block_index == final_index:
            split = block - peel_parameter
            yield PrimitiveMove(
                parent=parent,
                block_index=block_index,
                split=split,
                child=_child(parent, block_index, split),
                peel_parameter=peel_parameter,
                role="final_right",
            )


def _add(flow: DefaultDict[EdgeKey, int], edge: EdgeKey, amount: int) -> None:
    if not isinstance(amount, int) or isinstance(amount, bool):
        raise TypeError("raw-flow changes must be integers")
    flow[edge] += amount


def _signed_primitive_flow(d: int) -> DefaultDict[EdgeKey, int]:
    """Return (30 V(child)+30N-12) F2 + 72 F3 - 48 F4."""
    total = d + 2
    flow: DefaultDict[EdgeKey, int] = defaultdict(int)
    for parent in support_compositions(d):
        for move in primitive_moves(parent, 2):
            child_variance = sum(variance_statistic(part) for part in move.child)
            coefficient = 30 * child_variance + 30 * total - 12
            _add(flow, move.edge, coefficient * g_value(move.child, d))
        for move in primitive_moves(parent, 3):
            _add(flow, move.edge, 72 * g_value(move.child, d))
        for move in primitive_moves(parent, 4):
            _add(flow, move.edge, -48 * g_value(move.child, d))
    return flow


def _left_peel4_correction(
    flow: DefaultDict[EdgeKey, int],
    move: PrimitiveMove,
    d: int,
) -> None:
    """Replace the negative A->(4,t) move by a width-two path square."""
    parent = move.parent
    index = move.block_index
    block = parent[index]
    tail = block - 4
    if move.split != 4 or tail < 2:
        raise ValueError("not a left peel-4 move")
    b = move.child
    c = parent[:index] + (2, tail + 2) + parent[index + 1 :]
    destination = parent[:index] + (2, 2, tail) + parent[index + 1 :]
    amount = 48 * g_value(b, d)
    edge_ab = move.edge
    edge_bd: EdgeKey = (b, index, 2)
    edge_ac: EdgeKey = (parent, index, 2)
    edge_cd: EdgeKey = (c, index + 1, 2)
    if _child(*edge_bd) != destination or _child(*edge_cd) != destination:
        raise AssertionError("left path-square endpoints disagree")
    _add(flow, edge_ab, amount)
    _add(flow, edge_bd, amount)
    _add(flow, edge_ac, -amount)
    _add(flow, edge_cd, -amount)


def _final_right_peel4_correction(
    flow: DefaultDict[EdgeKey, int],
    move: PrimitiveMove,
    d: int,
) -> None:
    """Cancel a final-right peel-4 move and cascade its right-peel deficit."""
    parent = move.parent
    index = move.block_index
    if index != len(parent) - 1 or move.role != "final_right":
        raise ValueError("not a final-right peel-4 move")
    block = parent[index]
    tail = block - 4
    if move.split != tail or tail < 2:
        raise ValueError("malformed final-right peel-4 move")
    b = move.child
    c = parent[:index] + (tail + 2, 2)
    destination = parent[:index] + (tail, 2, 2)
    amount = 48 * g_value(b, d)
    edge_ab = move.edge
    edge_bd: EdgeKey = (b, index + 1, 2)
    edge_ac: EdgeKey = (parent, index, tail + 2)
    edge_cd: EdgeKey = (c, index, tail)
    if _child(*edge_bd) != destination or _child(*edge_cd) != destination:
        raise AssertionError("right path-square endpoints disagree")
    _add(flow, edge_ab, amount)
    _add(flow, edge_bd, amount)
    _add(flow, edge_ac, -amount)
    _add(flow, edge_cd, -amount)

    # The remaining negative edge splits a nonfinal block x+2 as (x,2).
    # A path square shifts it two units downward until it coincides with a
    # selected F2 edge (x=2) or a selected F3 edge (x=3).
    x = tail
    current_parent = c
    current_index = index
    current_edge = edge_cd
    while x >= 4:
        via_right = _child(*current_edge)
        via_left = (
            current_parent[:current_index]
            + (2, x, 2)
            + current_parent[current_index + 2 :]
        )
        common = (
            current_parent[:current_index]
            + (2, x - 2, 2, 2)
            + current_parent[current_index + 2 :]
        )
        right_then_left: EdgeKey = (via_right, current_index, 2)
        left_first: EdgeKey = (current_parent, current_index, 2)
        next_right: EdgeKey = (via_left, current_index + 1, x - 2)
        if (
            _child(*right_then_left) != common
            or _child(*left_first) != via_left
            or _child(*next_right) != common
        ):
            raise AssertionError("cascade path-square endpoints disagree")
        _add(flow, current_edge, amount)
        _add(flow, right_then_left, amount)
        _add(flow, left_first, -amount)
        _add(flow, next_right, -amount)
        current_parent = via_left
        current_index += 1
        current_edge = next_right
        x -= 2
    if x not in {2, 3}:
        raise AssertionError("right-peel cascade did not terminate")


def candidate_flow(d: int) -> RawFlow:
    """Return the proposed all-d raw nonnegative peel-width-at-most-3 flow."""
    if not isinstance(d, int) or isinstance(d, bool) or d < 1:
        raise ValueError("dimension must be an integer at least one")
    if d == 1:
        return {}
    flow = _signed_primitive_flow(d)
    for parent in support_compositions(d):
        for move in primitive_moves(parent, 4):
            if move.role == "final_right":
                _final_right_peel4_correction(flow, move, d)
            else:
                _left_peel4_correction(flow, move, d)
    if d == 2:
        # The eventual Eulerian fourth-moment polynomial differs by 24 at
        # N=4.  There is one actual support edge, with two primitive labels.
        root = (4,)
        child = (2, 2)
        _add(flow, (root, 0, 2), 24 * g_value(child, d))
    return {edge: amount for edge, amount in flow.items() if amount}


def verify_candidate_flow(d: int) -> dict[str, int | bool]:
    flow = candidate_flow(d)
    allowed = set(allowed_edge_keys(d))
    unknown = set(flow) - allowed
    negative = {edge: amount for edge, amount in flow.items() if amount < 0}
    divergence = {composition: 0 for composition in support_compositions(d)}
    for edge, amount in flow.items():
        parent, block_index, split = edge
        child = _child(parent, block_index, split)
        divergence[parent] += amount
        divergence[child] -= amount
    target = support_w4(d)
    mismatches = {
        composition: (divergence[composition], target[composition])
        for composition in divergence
        if divergence[composition] != target[composition]
    }
    result: dict[str, int | bool] = {
        "verified": not unknown and not negative and not mismatches,
        "dimension": d,
        "states": len(divergence),
        "used_edges": len(flow),
        "unknown_edges": len(unknown),
        "negative_edges": len(negative),
        "divergence_mismatches": len(mismatches),
        "minimum_flow": min(flow.values(), default=0),
        "total_divergence": sum(divergence.values()),
    }
    return result


def _flow_records(flow: RawFlow) -> list[dict[str, object]]:
    return [
        {
            "parent": list(parent),
            "block_index": block_index,
            "split": split,
            "child": list(_child(parent, block_index, split)),
            "raw_flow": str(amount),
        }
        for (parent, block_index, split), amount in sorted(flow.items())
    ]


def _json_sha256(value: object) -> str:
    encoded = json.dumps(
        value, sort_keys=True, separators=(",", ":"), ensure_ascii=True
    ).encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()


def verification_document(maximum_dimension: int = 11) -> dict[str, object]:
    if (
        not isinstance(maximum_dimension, int)
        or isinstance(maximum_dimension, bool)
        or not 1 <= maximum_dimension <= 11
    ):
        raise ValueError("verification maximum must lie between 1 and 11")
    dimensions = []
    for d in range(1, maximum_dimension + 1):
        flow = candidate_flow(d)
        verification = verify_candidate_flow(d)
        if not verification["verified"]:
            raise AssertionError("candidate verification failed")
        records = _flow_records(flow)
        dimensions.append(
            {
                **verification,
                "flow_sha256": _json_sha256(records),
                "total_raw_flow": str(sum(flow.values())),
            }
        )
    return {
        "schema": "chow-cone/k4-uniform-peel3-certificate/v1",
        "scope": {
            "verified_dimensions": list(range(1, maximum_dimension + 1)),
            "finite_verification_is_not_the_proof": True,
            "proof_document": "PROOF_K4_FOURTH_MOMENT.md",
        },
        "construction": {
            "signed_identity": (
                "(30*V(child)+30*N-12)*F2 + 72*F3 - 48*F4"
            ),
            "negative_term_elimination": (
                "zero-divergence equal-endpoint path-square corrections"
            ),
            "surviving_maximum_peel_width": 3,
            "small_dimensions": {
                "d1": "zero flow",
                "d2": "raw flow 720 on (4)->(2,2)",
            },
        },
        "dimensions": dimensions,
        "verified": all(row["verified"] for row in dimensions),
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args(argv)
    document = verification_document()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    with args.output.open("w", encoding="utf-8", newline="\n") as stream:
        json.dump(document, stream, indent=2, sort_keys=True)
        stream.write("\n")
    print(json.dumps(document, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
