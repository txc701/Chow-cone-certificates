"""Standalone exact verifier for saved k=4 peel-width certificates.

Independence is intentional: this file imports neither the max-flow solver
nor ``run_k4``, ``k4_weights``, or ``support``.  It independently enumerates
support compositions and recomputes the Eulerian fourth moment, S4, U, G,
and w4 using only Python arbitrary-precision integers and ``Fraction``.
"""

from __future__ import annotations

import argparse
from fractions import Fraction
from functools import lru_cache
from math import factorial
import json
from pathlib import Path
from typing import Any


Composition = tuple[int, ...]
EdgeKey = tuple[Composition, int, int]

SCHEMA = "chow-cone/k4-peel-width-certificate/v1"
PEEL_WIDTH_MAX = 3
WEIGHT_SCALE = 720


class CertificateVerificationError(ValueError):
    """A certificate is malformed or fails an exact mathematical check."""


def support_compositions_independent(d: int) -> list[Composition]:
    """Compositions of d+2 with all parts >= 2, independently enumerated."""
    if not isinstance(d, int) or isinstance(d, bool) or d < 2:
        raise CertificateVerificationError("d must be an integer at least 2")
    out: list[Composition] = []

    def visit(remaining: int, prefix: Composition) -> None:
        if remaining == 0:
            out.append(prefix)
            return
        for part in range(2, remaining + 1):
            if remaining - part != 1:
                visit(remaining - part, prefix + (part,))

    visit(d + 2, ())
    return sorted(out)


@lru_cache(maxsize=None)
def b4_720_independent(d: int) -> int:
    """720 times the fourth central moment of descents on S_(d+1)."""
    eulerian = [1]
    for size in range(2, d + 2):
        next_row = [0] * size
        for descents in range(size):
            left = (
                (descents + 1) * eulerian[descents]
                if descents < len(eulerian)
                else 0
            )
            right = (
                (size - descents) * eulerian[descents - 1]
                if descents >= 1
                else 0
            )
            next_row[descents] = left + right
        eulerian = next_row
    total = sum(eulerian)
    mean = Fraction(d, 2)
    centered_sum = sum(
        Fraction(count) * (Fraction(k) - mean) ** 4
        for k, count in enumerate(eulerian)
    )
    fourth = centered_sum * Fraction(1, total)
    scaled = WEIGHT_SCALE * fourth
    if scaled.denominator != 1:
        raise CertificateVerificationError(
            f"nonintegral scaled Eulerian fourth moment at d={d}: {scaled}"
        )
    return scaled.numerator


def s4_independent(composition: Composition, d: int) -> int:
    if sum(composition) != d + 2 or any(part < 2 for part in composition):
        raise CertificateVerificationError(
            f"invalid support composition for d={d}: {composition!r}"
        )
    variance_terms = [part * (part - 2) for part in composition]
    quartic = 3 * sum(
        part * (part - 2) * (3 * part * part - 6 * part - 4)
        for part in composition
    )
    cross = 30 * sum(
        variance_terms[i] * variance_terms[j]
        for i in range(len(variance_terms))
        for j in range(i + 1, len(variance_terms))
    )
    return quartic + cross - b4_720_independent(d)


def u_independent(composition: Composition, d: int) -> int:
    numerator = composition[-1] * factorial(d + 1)
    denominator = 1
    for part in composition:
        denominator *= factorial(part)
    quotient, remainder = divmod(numerator, denominator)
    if remainder:
        raise CertificateVerificationError(
            f"nonintegral U value at d={d}, composition={composition!r}"
        )
    return quotient


def g_independent(composition: Composition, d: int) -> int:
    product = 1
    for part in composition:
        product *= part - 1
    return u_independent(composition, d) * product


def w4_independent(composition: Composition, d: int) -> int:
    return g_independent(composition, d) * s4_independent(composition, d)


def _child(parent: Composition, block: int, left: int) -> Composition:
    size = parent[block]
    return parent[:block] + (left, size - left) + parent[block + 1 :]


def allowed_edge_keys_independent(d: int) -> list[EdgeKey]:
    out = []
    for parent in support_compositions_independent(d):
        for block, size in enumerate(parent):
            for left in range(2, size - 1):
                if min(left, size - left) <= PEEL_WIDTH_MAX:
                    out.append((parent, block, left))
    return sorted(out)


def _require_plain_int(value: Any, field: str) -> int:
    if not isinstance(value, int) or isinstance(value, bool):
        raise CertificateVerificationError(f"{field} must be an integer")
    return value


def _parse_decimal_integer(value: Any, field: str) -> int:
    if not isinstance(value, str) or not value:
        raise CertificateVerificationError(
            f"{field} must be a canonical decimal integer string"
        )
    try:
        parsed = int(value, 10)
    except ValueError as error:
        raise CertificateVerificationError(
            f"{field} must be a canonical decimal integer string"
        ) from error
    if str(parsed) != value:
        raise CertificateVerificationError(
            f"{field} is not canonical decimal notation: {value!r}"
        )
    return parsed


def verify_certificate(document: Any) -> dict[str, Any]:
    """Verify a parsed certificate document and return an exact summary.

    Invalid documents raise ``CertificateVerificationError`` at the first
    concrete discrepancy.  Success means every listed flow is positive,
    every omitted allowed edge has flow zero, each used edge is a unique
    peel-width-at-most-3 cover, and divergence equals independently computed
    w4 at every support node.
    """
    if not isinstance(document, dict):
        raise CertificateVerificationError("certificate must be a JSON object")
    if document.get("schema") != SCHEMA:
        raise CertificateVerificationError(
            f"unsupported schema: {document.get('schema')!r}"
        )
    d = _require_plain_int(document.get("d"), "d")
    if d < 2:
        raise CertificateVerificationError("d must be at least 2")
    if document.get("peel_width_max") != PEEL_WIDTH_MAX:
        raise CertificateVerificationError("peel_width_max must equal 3")
    if document.get("weight_scale") != WEIGHT_SCALE:
        raise CertificateVerificationError("weight_scale must equal 720")
    generation = document.get("generation")
    if not isinstance(generation, dict):
        raise CertificateVerificationError("generation parameters are missing")
    for field in (
        "algorithm",
        "node_order",
        "edge_order",
        "edge_order_key",
        "source_sink_order",
        "cover_capacity",
        "flow_encoding",
    ):
        if not isinstance(generation.get(field), str) or not generation[field]:
            raise CertificateVerificationError(
                f"generation.{field} must be a nonempty string"
            )

    compositions = support_compositions_independent(d)
    composition_set = set(compositions)
    weights = {
        composition: w4_independent(composition, d)
        for composition in compositions
    }
    allowed_edges = allowed_edge_keys_independent(d)
    allowed_set = set(allowed_edges)
    total_supply = sum(weight for weight in weights.values() if weight > 0)

    declared_nodes = _require_plain_int(
        document.get("n_support_nodes"), "n_support_nodes"
    )
    declared_allowed = _require_plain_int(
        document.get("n_allowed_edges"), "n_allowed_edges"
    )
    declared_positive = _require_plain_int(
        document.get("n_positive_edges"), "n_positive_edges"
    )
    declared_supply = _parse_decimal_integer(
        document.get("total_supply"), "total_supply"
    )
    if declared_nodes != len(compositions):
        raise CertificateVerificationError(
            f"n_support_nodes mismatch: {declared_nodes} != {len(compositions)}"
        )
    if declared_allowed != len(allowed_edges):
        raise CertificateVerificationError(
            f"n_allowed_edges mismatch: {declared_allowed} != {len(allowed_edges)}"
        )
    if declared_supply != total_supply:
        raise CertificateVerificationError(
            f"total_supply mismatch: {declared_supply} != {total_supply}"
        )

    encoded_edges = document.get("edges")
    if not isinstance(encoded_edges, list):
        raise CertificateVerificationError("edges must be a list")
    if declared_positive != len(encoded_edges):
        raise CertificateVerificationError(
            f"n_positive_edges mismatch: {declared_positive} != {len(encoded_edges)}"
        )

    divergence = {composition: 0 for composition in compositions}
    seen: set[EdgeKey] = set()
    previous: EdgeKey | None = None
    for row_index, row in enumerate(encoded_edges):
        field = f"edges[{row_index}]"
        if not isinstance(row, list) or len(row) != 4:
            raise CertificateVerificationError(
                f"{field} must be [parent, block, left, flow]"
            )
        encoded_parent, encoded_block, encoded_left, encoded_flow = row
        if not isinstance(encoded_parent, list) or not encoded_parent:
            raise CertificateVerificationError(f"{field}.parent must be a list")
        parent_parts = []
        for part_index, part in enumerate(encoded_parent):
            parent_parts.append(
                _require_plain_int(part, f"{field}.parent[{part_index}]")
            )
        parent = tuple(parent_parts)
        block = _require_plain_int(encoded_block, f"{field}.block")
        left = _require_plain_int(encoded_left, f"{field}.left")
        flow = _parse_decimal_integer(encoded_flow, f"{field}.flow")
        if flow <= 0:
            raise CertificateVerificationError(
                f"{field}.flow must be positive in the sparse encoding"
            )
        if parent not in composition_set:
            raise CertificateVerificationError(
                f"{field}.parent is not a support composition"
            )
        if block < 0 or block >= len(parent):
            raise CertificateVerificationError(f"{field}.block is out of range")
        size = parent[block]
        if left < 2 or left > size - 2:
            raise CertificateVerificationError(
                f"{field} is not an all-parts-at-least-2 split"
            )
        if min(left, size - left) > PEEL_WIDTH_MAX:
            raise CertificateVerificationError(
                f"{field} has peel width greater than 3"
            )
        edge = (parent, block, left)
        if edge not in allowed_set:
            raise CertificateVerificationError(f"{field} is not an allowed edge")
        if edge in seen:
            raise CertificateVerificationError(f"duplicate edge: {edge!r}")
        if previous is not None and edge <= previous:
            raise CertificateVerificationError(
                "edges are not in canonical (parent, block, left) order"
            )
        seen.add(edge)
        previous = edge
        child = _child(parent, block, left)
        if child not in composition_set:
            raise CertificateVerificationError(
                f"{field} child is not a support composition"
            )
        divergence[parent] += flow
        divergence[child] -= flow

    mismatches = [
        (composition, divergence[composition], weights[composition])
        for composition in compositions
        if divergence[composition] != weights[composition]
    ]
    total_weight = sum(weights.values())
    total_divergence = sum(divergence.values())
    if total_weight != 0:
        raise CertificateVerificationError(
            f"independently computed weights sum to {total_weight}, not zero"
        )
    if total_divergence != 0:
        raise CertificateVerificationError(
            f"certificate divergence sums to {total_divergence}, not zero"
        )
    if mismatches:
        composition, actual, expected = mismatches[0]
        raise CertificateVerificationError(
            "divergence mismatch at "
            f"{composition!r}: actual={actual}, expected={expected}; "
            f"{len(mismatches)} node(s) mismatched"
        )

    return {
        "schema": SCHEMA,
        "d": d,
        "edge_order": generation["edge_order"],
        "n_support_nodes": len(compositions),
        "n_allowed_edges": len(allowed_edges),
        "n_positive_edges": len(encoded_edges),
        "n_zero_edges": len(allowed_edges) - len(encoded_edges),
        "total_supply": str(total_supply),
        "total_weight": str(total_weight),
        "total_divergence": str(total_divergence),
        "divergence_mismatches": 0,
        "all_flows_nonnegative": True,
        "all_used_edges_allowed": True,
        "all_used_edges_unique": True,
        "verified": True,
    }


def verify_certificate_file(path: str | Path) -> dict[str, Any]:
    with Path(path).open("r", encoding="utf-8") as stream:
        document = json.load(stream)
    return verify_certificate(document)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("certificates", nargs="+", type=Path)
    args = parser.parse_args()
    summaries = [
        verify_certificate_file(path)
        for path in args.certificates
    ]
    print(json.dumps({"all_verified": True, "certificates": summaries}, indent=2))


if __name__ == "__main__":
    main()
