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


def test_no_floating_point_in_sources():
    """No float literals, no true division, no float() calls in src/."""
    import os

    src = os.path.join(os.path.dirname(__file__), "..", "src")
    for fname in sorted(os.listdir(src)):
        if not fname.endswith(".py"):
            continue
        with open(os.path.join(src, fname), "rb") as f:
            toks = list(tokenize.tokenize(f.readline))
        for tok in toks:
            if tok.type == tokenize.OP:
                assert tok.string not in ("/", "/="), (fname, tok)
            if tok.type == tokenize.NUMBER:
                assert "." not in tok.string and "e" not in tok.string.lower(), (
                    fname,
                    tok,
                )
            if tok.type == tokenize.NAME:
                assert tok.string != "float", (fname, tok)
