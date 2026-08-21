"""k=4 (fourth central moment) analogue of the Cheng-Lin weights.

DERIVATION (Branch B research; see K4_NOTES.md).

From the paper's flag decomposition CH_M(x) = sum_J N_J P_J(x) with
P_J(x) = (1/x) prod_i f_{n_i}(x), f_n(x) = x + ... + x^{n-1}: the formal
variable F_J is a sum of independent uniforms Y_i on {1..n_i-1} (shifted by
-1), and EVERY F_J has mean d/2.  Hence for any k,

    E[(X_M - d/2)^k] * CH_M(1) = sum_J N_J P_J(1) mu_k(F_J),

with P_J(1) = prod (n_i - 1) and mu_k the k-th central moment.  For k = 4,
independence gives

    mu4(F_J) = sum_i mu4(Y_i) + 6 sum_{i<j} var(Y_i) var(Y_j),
    var(Y)  = n(n-2)/12                      (uniform on n-1 points),
    mu4(Y)  = n(n-2)(3n^2 - 6n - 4)/240.

The Boolean matroid value (X_d = descents on S_{d+1}, Eulerian) is
computed EXACTLY per d from Eulerian numbers.  Finding: it equals
(d+2)(5d+8)/240 for d >= 3 but NOT for d in {1, 2} (values 1/16 and 1/3)
— a 1-dependence boundary effect with no k=2 counterpart (the variance
(d+2)/12 is polynomial for ALL d).  We use the exact value so that
sum_J w4_J = 0 holds identically.

The k=4 analogue of the Corollary-3.28 coefficient (scaled by 720 to clear
denominators, keeping exact integers) is

    a4_J = prod_i (n_i - 1) * S4(c),   w4_J = U_J * a4_J,
    S4(c) = 3*sum_i n_i(n_i-2)(3n_i^2-6n_i-4)
          + 30*sum_{i<j} n_i(n_i-2) n_j(n_j-2)
          - B4_720(d),        B4_720(d) := 720 * mu4(X_d)  (exact integer;
                              = 3(d+2)(5d+8) for d >= 3).

sum_J w4_J = 0 holds by construction (the Boolean matroid realizes
N_J = U_J), and the k=4 flag inequality  sum_J a4_J N_J <= 0  would be the
statement E[(X_M-d/2)^4] <= B4(d).  Whether it admits a Cheng-Lin-style
certificate (nonneg flow with divergence w4) is the Branch-B question.

All exact integer arithmetic.
"""

from fractions import Fraction
from functools import lru_cache
from math import factorial


@lru_cache(maxsize=None)
def b4_720(d: int) -> int:
    """720 * (fourth central moment of descents on S_{d+1}), exact."""
    n = d + 1
    A = [1]
    for m in range(2, n + 1):
        B = [0] * m
        for k in range(m):
            left = (k + 1) * A[k] if k < len(A) else 0
            right = (m - k) * A[k - 1] if k - 1 >= 0 else 0
            B[k] = left + right
        A = B
    tot = sum(A)
    mean = Fraction(d, 2)
    mu4 = sum(Fraction(a) * (Fraction(k) - mean) ** 4
              for k, a in enumerate(A)) / tot
    val = 720 * mu4
    assert val.denominator == 1, (d, val)
    return int(val)


def s4(parts: tuple[int, ...]) -> int:
    """720 * (mu4(F_J) - B4(d)) as an exact integer."""
    n = sum(parts)  # = d + 2
    d = n - 2
    quart = 3 * sum(m * (m - 2) * (3 * m * m - 6 * m - 4) for m in parts)
    v = [m * (m - 2) for m in parts]
    tot = sum(v)
    cross_twice = tot * tot - sum(x * x for x in v)  # 2 * sum_{i<j} v_i v_j
    assert cross_twice % 2 == 0
    cross = 30 * (cross_twice // 2)
    return quart + cross - b4_720(d)


def u_value(parts: tuple[int, ...], d: int) -> int:
    num = parts[-1] * factorial(d + 1)
    den = 1
    for m in parts:
        den *= factorial(m)
    assert num % den == 0
    return num // den


def w4_value(parts: tuple[int, ...], d: int) -> int:
    """w4 = U * prod(n_i - 1) * S4  (exact integer, x720 scaling)."""
    prod = 1
    for m in parts:
        prod *= m - 1
    return u_value(parts, d) * prod * s4(parts)


def support_w4(d: int) -> dict[tuple[int, ...], int]:
    """w4 over the all-parts>=2 support (same support factor prod(n_i-1))."""
    import os
    import sys
    sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
    from support import support_compositions

    return {c: w4_value(c, d) for c in support_compositions(d)}
