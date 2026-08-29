from __future__ import annotations

from fractions import Fraction
import inspect
import json
from pathlib import Path

import pytest

from k4_feature_analysis import g_value, variance_statistic
from k4_uniform_certificate import (
    _child,
    _signed_primitive_flow,
    candidate_flow,
    primitive_moves,
    verification_document,
    verify_candidate_flow,
)
from k4_weights import b4_720, support_w4
from support import support_compositions


ROOT = Path(__file__).resolve().parents[1]


Poly = dict[int, Fraction]


def _add(*polynomials: Poly) -> Poly:
    result: Poly = {}
    for polynomial in polynomials:
        for exponent, coefficient in polynomial.items():
            value = result.get(exponent, Fraction(0)) + coefficient
            if value:
                result[exponent] = value
            elif exponent in result:
                del result[exponent]
    return result


def _scale(scale: Fraction | int, polynomial: Poly) -> Poly:
    return {
        exponent: Fraction(scale) * coefficient
        for exponent, coefficient in polynomial.items()
        if scale * coefficient
    }


def _multiply(first: Poly, second: Poly) -> Poly:
    terms: Poly = {}
    for first_exponent, first_coefficient in first.items():
        for second_exponent, second_coefficient in second.items():
            terms = _add(
                terms,
                {
                    first_exponent + second_exponent:
                    first_coefficient * second_coefficient
                },
            )
    return terms


def _tau_polynomials() -> tuple[Poly, Poly, Poly, Poly]:
    n = {1: Fraction(1)}
    v = _multiply(n, _add(n, {0: Fraction(-2)}))
    tau2 = _scale(Fraction(1, 2), _multiply(n, _add(n, {0: Fraction(-3)})))
    tau3 = _scale(
        Fraction(1, 3),
        _multiply(n, _multiply(_add(n, {0: Fraction(-2)}), _add(n, {0: Fraction(-4)}))),
    )
    tau4 = _scale(
        Fraction(1, 8),
        _multiply(
            n,
            _multiply(
                _add(n, {0: Fraction(-2)}),
                _multiply(_add(n, {0: Fraction(-3)}), _add(n, {0: Fraction(-5)})),
            ),
        ),
    )
    return v, tau2, tau3, tau4


def _raw_divergence(d: int, flow: dict[tuple, int]) -> dict[tuple[int, ...], int]:
    divergence = {composition: 0 for composition in support_compositions(d)}
    for edge, amount in flow.items():
        parent, block_index, split = edge
        child = _child(parent, block_index, split)
        divergence[parent] += amount
        divergence[child] -= amount
    return divergence


def test_formal_one_variable_primitive_identities() -> None:
    v, tau2, tau3, tau4 = _tau_polynomials()
    n_minus_two = {1: Fraction(1), 0: Fraction(-2)}
    assert _scale(-4, _multiply(n_minus_two, tau2)) == _add(
        _scale(-6, tau3), _scale(-2, v)
    )
    assert _add(_multiply(v, v), _scale(-9, v)) == _add(
        _scale(8, tau4), _scale(18, tau3)
    )


def test_primitive_move_multiplicities_and_small_boundary() -> None:
    final_f2 = list(primitive_moves((4,), 2))
    final_f3 = list(primitive_moves((6,), 3))
    final_f4 = list(primitive_moves((8,), 4))
    assert len(final_f2) == len(final_f3) == len(final_f4) == 2
    assert final_f2[0].edge == final_f2[1].edge
    assert final_f3[0].edge == final_f3[1].edge
    assert final_f4[0].edge == final_f4[1].edge
    assert candidate_flow(1) == {}
    assert candidate_flow(2) == {((4,), 0, 2): 720}
    assert b4_720(2) == 240


@pytest.mark.parametrize("d", range(3, 12))
def test_signed_primitive_identity_before_rerouting(d: int) -> None:
    signed = dict(_signed_primitive_flow(d))
    assert _raw_divergence(d, signed) == support_w4(d)


@pytest.mark.parametrize("d", range(1, 12))
def test_uniform_candidate_exact_nonnegative_and_width_three(d: int) -> None:
    result = verify_candidate_flow(d)
    assert result["verified"]
    assert result["negative_edges"] == 0
    assert result["unknown_edges"] == 0
    assert result["divergence_mismatches"] == 0
    assert result["total_divergence"] == 0
    assert all(
        min(split, parent[block_index] - split) <= 3
        for parent, block_index, split in candidate_flow(d)
    )


def test_final_eight_double_peel_four_is_fully_eliminated() -> None:
    assert ((8,), 0, 4) not in candidate_flow(6)


def test_exact_collision_and_capacity_bounds() -> None:
    # These are the exact inequalities used in the symbolic proof.  The
    # geometric estimates are deliberately rational, with no float fitting.
    assert Fraction(1) + Fraction(1, 2) / (1 - Fraction(1, 9)) == Fraction(25, 16)
    assert Fraction(1) + Fraction(1, 5) / (1 - Fraction(1, 14)) == Fraction(79, 65)
    assert Fraction(79, 65) < Fraction(5, 4)
    for block in range(6, 80):
        assert 18 * block * block - 66 * block + 69 > 0
        assert 18 * block * block - 42 * block - 36 > 0
        assert 6 * block * block + 18 * block - 12 > 0


def test_general_flow_coefficient_is_manifestly_positive() -> None:
    for d in range(3, 12):
        total = d + 2
        for composition in support_compositions(d):
            for move in primitive_moves(composition, 2):
                child_variance = sum(
                    variance_statistic(part) for part in move.child
                )
                assert 30 * child_variance + 30 * total - 12 > 0
                assert g_value(move.child, d) > 0


def test_certificate_source_uses_no_floating_point_arithmetic() -> None:
    import k4_uniform_certificate

    source = inspect.getsource(k4_uniform_certificate)
    assert "float(" not in source
    assert "numpy" not in source
    assert "scipy" not in source


def test_saved_verification_artifact_matches_generator() -> None:
    saved = json.loads(
        (ROOT / "results" / "k4_uniform_certificate" / "verification.json").read_text()
    )
    assert saved == verification_document()
