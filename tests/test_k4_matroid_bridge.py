"""Exact symbolic checks for the new Chow-polynomial/matroid bridge only.

These tests do not construct or verify the frozen k=4 flow.  They check the
new coefficient identification between Cheng--Lin flag summands and the
already frozen divergence target.
"""

from __future__ import annotations

from fractions import Fraction
from math import prod

import pytest

from k4_weights import b4_720, s4, u_value
from weights_bitmask import composition_of


Polynomial = dict[int, int]


def _multiply(first: Polynomial, second: Polynomial) -> Polynomial:
    result: Polynomial = {}
    for first_degree, first_coefficient in first.items():
        for second_degree, second_coefficient in second.items():
            degree = first_degree + second_degree
            result[degree] = (
                result.get(degree, 0)
                + first_coefficient * second_coefficient
            )
    return result


def _flag_polynomial(parts: tuple[int, ...]) -> Polynomial:
    """P_J=x^(-1) product_i(x+...+x^(n_i-1)), coefficientwise."""
    polynomial: Polynomial = {0: 1}
    for block in parts:
        polynomial = _multiply(
            polynomial,
            {degree: 1 for degree in range(1, block)},
        )
    return {degree - 1: coefficient for degree, coefficient in polynomial.items()}


def _eulerian_row(order: int) -> tuple[int, ...]:
    row = [1]
    for size in range(2, order + 1):
        following = [0] * size
        for descents in range(size):
            left = (
                (descents + 1) * row[descents]
                if descents < len(row)
                else 0
            )
            right = (
                (size - descents) * row[descents - 1]
                if descents >= 1
                else 0
            )
            following[descents] = left + right
        row = following
    return tuple(row)


@pytest.mark.parametrize("block", range(2, 15))
def test_centered_uniform_block_moments(block: int) -> None:
    values = tuple(range(1, block))
    center = Fraction(block, 2)
    variance = sum(
        ((Fraction(value) - center) ** 2 for value in values),
        Fraction(0),
    ) / len(values)
    fourth = sum(
        ((Fraction(value) - center) ** 4 for value in values),
        Fraction(0),
    ) / len(values)
    v = block * (block - 2)
    assert variance == Fraction(v, 12)
    assert fourth == Fraction(
        v * (3 * block * block - 6 * block - 4),
        240,
    )


@pytest.mark.parametrize("d", range(1, 7))
def test_flag_summand_gives_the_derived_fourth_moment_coefficient(d: int) -> None:
    center = Fraction(d, 2)
    for mask in range(1 << d):
        parts = composition_of(mask, d)
        polynomial = _flag_polynomial(parts)
        value_at_one = sum(polynomial.values())
        assert value_at_one == prod(block - 1 for block in parts)

        first_centered_sum = sum(
            (
                coefficient * (Fraction(degree) - center)
                for degree, coefficient in polynomial.items()
            ),
            Fraction(0),
        )
        assert first_centered_sum == 0

        fourth_centered_sum = sum(
            (
                coefficient * (Fraction(degree) - center) ** 4
                for degree, coefficient in polynomial.items()
            ),
            Fraction(0),
        )
        derived_coefficient = (
            720 * fourth_centered_sum
            - b4_720(d) * value_at_one
        )
        assert derived_coefficient == value_at_one * s4(parts)


@pytest.mark.parametrize("d", range(1, 7))
def test_boolean_flag_expansion_and_derived_conservation(d: int) -> None:
    reconstructed: Polynomial = {}
    total_fourth_weight = 0
    for mask in range(1 << d):
        parts = composition_of(mask, d)
        boolean_flags = u_value(parts, d)
        for degree, coefficient in _flag_polynomial(parts).items():
            reconstructed[degree] = (
                reconstructed.get(degree, 0)
                + boolean_flags * coefficient
            )
        total_fourth_weight += (
            boolean_flags
            * prod(block - 1 for block in parts)
            * s4(parts)
        )

    assert reconstructed == {
        degree: coefficient
        for degree, coefficient in enumerate(_eulerian_row(d + 1))
    }
    assert total_fourth_weight == 0


@pytest.mark.parametrize("d", range(1, 10))
def test_boolean_fourth_moment_and_exceptional_constants(d: int) -> None:
    row = _eulerian_row(d + 1)
    center = Fraction(d, 2)
    direct = Fraction(
        sum(
            coefficient * (Fraction(degree) - center) ** 4
            for degree, coefficient in enumerate(row)
        ),
        sum(row),
    )
    if d == 1:
        expected = Fraction(1, 16)
    elif d == 2:
        expected = Fraction(1, 3)
    else:
        expected = Fraction((d + 2) * (5 * d + 8), 240)
    assert direct == expected
    assert 720 * direct == b4_720(d)
