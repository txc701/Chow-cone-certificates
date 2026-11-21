"""Stage 1 validation: the two independent weight implementations agree,
weights are exact integers, sum to zero, and match hand calculations."""

import io
import tokenize

import pytest

import weights_bitmask as impl1
import weights_recursive as impl2

AGREE_RANGE = range(1, 12)  # full 2^d maps; d<=11 keeps the suite fast


@pytest.mark.parametrize("d", AGREE_RANGE)
def test_implementations_agree(d):
    m1 = impl1.weight_map(d)
    m2 = impl2.weight_map(d)
    assert m1 == m2, f"weight maps differ at d={d}"


@pytest.mark.parametrize("d", AGREE_RANGE)
def test_integrality_and_types(d):
    for mask, (u, a, w) in impl1.weight_map(d).items():
        assert type(u) is int and type(a) is int and type(w) is int
        assert u > 0
        assert w == u * a


@pytest.mark.parametrize("d", AGREE_RANGE)
def test_sum_zero(d):
    assert sum(w for (_, _, w) in impl1.weight_map(d).values()) == 0


def test_hand_calculations():
    # d=1: compositions (3) and (1,2); both weights vanish.
    assert impl1.weight_map(1) == {0: (1, 0, 0), 1: (2, 0, 0)}
    # d=2: hand-computed in RESEARCH_NOTES.md.
    assert impl1.weight_map(2) == {
        0b00: (1, 6, 6),     # (4):    U=4*3!/4!=1,  a=3*(4*1/2)=6
        0b01: (3, 0, 0),     # (1,3):  factor (1-1)=0
        0b10: (3, -2, -6),   # (2,2):  U=2*3!/(2!2!)=3, a=1*1*(-1-1)=-2
        0b11: (6, 0, 0),     # (1,1,2)
    }
    # d=3
    assert impl1.weight_map(3) == {
        0b000: (1, 20, 20),   # (5):   U=5*4!/5!=1, a=4*(5*2/2)=20
        0b001: (4, 0, 0),     # (1,4)
        0b010: (6, -2, -12),  # (2,3): U=3*4!/(2!3!)=6, a=1*2*((-2+0)/2)=-2
        0b100: (4, -2, -8),   # (3,2): U=2*4!/(3!2!)=4, a=2*1*((0-2)/2)=-2
        0b011: (12, 0, 0),    # (1,1,3)
        0b101: (12, 0, 0),    # (1,2,2)
        0b110: (12, 0, 0),    # (2,1,2)
        0b111: (24, 0, 0),    # (1,1,1,2)
    }


# One audited exception to the ban on "/".  src/k4_weights.py line 63 divides a sum of
# Fractions by an int: exact rational arithmetic, not floating point.  The SHA-256 of that
# file is recorded in the source_provenance of two frozen manifests
# (results/k4_degree4_decision, results/k4_width3_discovery), so the file is kept
# byte-identical instead of being rewritten (tests/test_source_provenance.py).  The
# exception is tied to the exact line text, it must be used, and the exactness of the
# value it computes is tested in test_the_allowed_division_is_exact_rational_arithmetic.
ALLOWED_TRUE_DIVISIONS = {
    ("k4_weights.py", 63): "for k, a in enumerate(A)) / tot",
}


def test_no_floating_point_in_sources():
    """No float literals, no float() calls and no true division in src/, apart
    from the audited exact-rational division in ALLOWED_TRUE_DIVISIONS."""
    import os

    src = os.path.join(os.path.dirname(__file__), "..", "src")
    used = set()
    for fname in sorted(os.listdir(src)):
        if not fname.endswith(".py"):
            continue
        with open(os.path.join(src, fname), "rb") as f:
            toks = list(tokenize.tokenize(f.readline))
        for tok in toks:
            if tok.type == tokenize.OP and tok.string in ("/", "/="):
                key = (fname, tok.start[0])
                assert tok.string == "/", (fname, tok)
                assert ALLOWED_TRUE_DIVISIONS.get(key) == tok.line.strip(), (fname, tok)
                used.add(key)
            if tok.type == tokenize.NUMBER:
                assert "." not in tok.string and "e" not in tok.string.lower(), (
                    fname,
                    tok,
                )
            if tok.type == tokenize.NAME:
                assert tok.string != "float", (fname, tok)
    # an exception that is no longer needed must be removed, not left behind
    assert used == set(ALLOWED_TRUE_DIVISIONS)


def test_the_allowed_division_is_exact_rational_arithmetic():
    """b4_720(d) = 720 * (fourth central moment of descents on S_{d+1}) is
    recomputed with integers only and must agree, as an int, for 1 <= d <= 30."""
    from math import factorial

    from k4_weights import b4_720

    for d in range(1, 31):
        row = [1]                       # Eulerian numbers A(d+1, k), own recurrence
        for m in range(2, d + 2):
            row = [(k + 1) * (row[k] if k < len(row) else 0)
                   + (m - k) * (row[k - 1] if k >= 1 else 0) for k in range(m)]
        assert sum(row) == factorial(d + 1)
        num = 720 * sum(a * (2 * k - d) ** 4 for k, a in enumerate(row))
        den = 16 * factorial(d + 1)
        assert num % den == 0
        value = b4_720(d)
        assert type(value) is int and value == num // den
