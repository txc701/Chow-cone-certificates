"""Implementation 1 of the Cheng-Lin weights (arXiv:2603.21680v3, Conjecture 3.30).

Subset/bitmask representation.  For d >= 1 and J = {j_1 < ... < j_m} <= [d]
(encoded as a bitmask with bit (j-1) set iff j in J), set j_0 = 0 and define
the composition of d+2

    n_i = j_i - j_{i-1}  (1 <= i <= m),      n_{m+1} = d + 2 - j_m.

Then
    U_J = n_{m+1} * (d+1)! / prod_i n_i!
    a_J = prod_i (n_i - 1) * ( (1/2) * sum_i n_i (n_i - 3) )
    w_J = U_J * a_J.

Exact integer arithmetic only.  Every division is checked for exactness and
raises AssertionError otherwise (tests fail loudly).
"""

from math import factorial


def composition_of(mask: int, d: int) -> tuple[int, ...]:
    """The composition (n_1, ..., n_{m+1}) of d+2 associated with subset mask."""
    assert d >= 1
    assert 0 <= mask < (1 << d)
    parts = []
    prev = 0
    for j in range(1, d + 1):
        if (mask >> (j - 1)) & 1:
            parts.append(j - prev)
            prev = j
    parts.append(d + 2 - prev)
    return tuple(parts)


def uaw_from_composition(parts: tuple[int, ...], d: int) -> tuple[int, int, int]:
    """(U, a, w) for a composition (n_1,...,n_{m+1}) of d+2."""
    assert sum(parts) == d + 2, (parts, d)
    assert all(p >= 1 for p in parts)
    assert parts[-1] >= 2  # n_{m+1} = d+2-j_m >= 2 since j_m <= d

    num = parts[-1] * factorial(d + 1)
    den = 1
    for p in parts:
        den *= factorial(p)
    assert num % den == 0, ("U not integral", parts, d)
    u = num // den

    prod = 1
    for p in parts:
        prod *= p - 1
    s = sum(p * (p - 3) for p in parts)
    assert s % 2 == 0, ("a not integral", parts, d)
    a = prod * (s // 2)

    return u, a, u * a


def weight_map(d: int) -> dict[int, tuple[int, int, int]]:
    """Full map {mask: (U_J, a_J, w_J)} over all 2^d subsets of [d]."""
    return {
        mask: uaw_from_composition(composition_of(mask, d), d)
        for mask in range(1 << d)
    }
