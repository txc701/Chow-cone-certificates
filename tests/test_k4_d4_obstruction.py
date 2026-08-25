"""Exact tests for the bounded d=4 degree-four obstruction analysis."""

from fractions import Fraction

from k4_degree4_decision import (
    build_decision_system,
    mirror_edge_key,
    normalized_flow_row,
)
from k4_feature_analysis import edge_features
from k4_weights import b4_720, s4


WITNESS = {
    (2, 2, 2): -1,
    (2, 4): 2,
    (4, 2): -2,
}

BALANCED_COLUMNS = (
    "s2:balanced:invariant:00",
    "s2:balanced:invariant:01",
    "s2:balanced:invariant:03",
    "s2:balanced:invariant:07",
    "s2:balanced:invariant:14",
)

ORIENTED_COLUMNS = (
    "s2:oriented:invariant:00",
    "s2:oriented:invariant:02",
    "s2:oriented:invariant:07",
    "s2:oriented:invariant:16",
    "s2:oriented:invariant:34",
)


def _obstruction_rows():
    system = build_decision_system((4,))
    rows = {
        composition: row
        for (_, composition), row in zip(system.row_labels, system.rows)
        if composition in WITNESS
    }
    rhs = {
        composition: value
        for (_, composition), value in zip(system.row_labels, system.rhs)
        if composition in WITNESS
    }
    return system, rows, rhs


def _named_row(system, row):
    return {system.parameter_names[column]: value for column, value in row.items()}


def test_the_three_obstruction_equations_have_the_complete_exact_expansion():
    system, rows, rhs = _obstruction_rows()
    powers = (1, 2, 4, 8, 16)
    balanced = dict(zip(BALANCED_COLUMNS, powers))
    oriented = dict(zip(ORIENTED_COLUMNS, powers))

    assert b4_720(4) == 504
    assert {composition: s4(composition) for composition in WITNESS} == {
        (2, 2, 2): -504,
        (2, 4): -24,
        (4, 2): -24,
    }
    assert rhs == {
        (2, 2, 2): Fraction(-504),
        (2, 4): Fraction(-24),
        (4, 2): Fraction(-24),
    }
    assert _named_row(system, rows[(2, 2, 2)]) == {
        name: Fraction(-2 * value) for name, value in balanced.items()
    }
    assert _named_row(system, rows[(2, 4)]) == {
        **{name: Fraction(value) for name, value in balanced.items()},
        **{name: Fraction(-value) for name, value in oriented.items()},
    }
    assert _named_row(system, rows[(4, 2)]) == {
        **{name: Fraction(2 * value) for name, value in balanced.items()},
        **{name: Fraction(-value) for name, value in oriented.items()},
    }

    visible = set().union(*(row.keys() for row in rows.values()))
    visible_names = {system.parameter_names[column] for column in visible}
    assert len(system.parameter_names) == 156
    assert visible_names == set(BALANCED_COLUMNS + ORIENTED_COLUMNS)
    assert len(visible) == 10
    assert len(set(range(156)) - visible) == 146
    names = system.parameter_names
    assert sum(name.startswith("s3:") for name in names) == 78
    assert sum(name.startswith("s2:oriented:anti:") for name in names) == 25
    assert (
        sum(name.startswith("s2:oriented:invariant:") for name in names)
        - len(ORIENTED_COLUMNS)
        == 30
    )
    assert (
        sum(name.startswith("s2:balanced:invariant:") for name in names)
        - len(BALANCED_COLUMNS)
        == 13
    )


def test_witness_cancels_every_one_of_the_156_columns_but_leaves_504():
    system, rows, rhs = _obstruction_rows()
    for column in range(len(system.parameter_names)):
        assert sum(
            Fraction(multiplier) * rows[composition].get(column, Fraction(0))
            for composition, multiplier in WITNESS.items()
        ) == 0
    assert sum(
        Fraction(multiplier) * rhs[composition]
        for composition, multiplier in WITNESS.items()
    ) == 504


def test_cancellation_is_exactly_equality_on_the_two_mirror_edge_pairs():
    features = {feature.edge: feature for feature in edge_features(4)}
    inner_final = features[((2, 4), 1, 2)]
    inner_first = features[((4, 2), 0, 2)]
    outer_left = features[((6,), 0, 2)]
    outer_right = features[((6,), 0, 4)]

    assert mirror_edge_key(inner_final) == inner_first.edge
    assert mirror_edge_key(outer_left) == outer_right.edge
    assert normalized_flow_row(inner_final) == normalized_flow_row(inner_first)
    assert normalized_flow_row(outer_left) == normalized_flow_row(outer_right)
    assert (inner_final.ratio, inner_first.ratio) == (1, 2)


def test_one_g_covariant_boundary_column_breaks_the_witness_exactly():
    """The local child-first-block column has witness value 4."""
    features = edge_features(4)
    assert len(features) == 5
    by_edge = {feature.edge: feature for feature in features}

    def boundary_column(feature):
        if feature.peel_width == 2 and feature.peel_side in {"left", "right"}:
            return Fraction(feature.child[0])
        return Fraction(0)

    outer_left = by_edge[((6,), 0, 2)]
    outer_right = by_edge[((6,), 0, 4)]
    assert (
        outer_left.child,
        outer_left.G_child,
        boundary_column(outer_left),
    ) == ((2, 4), 30, 2)
    assert (
        outer_right.child,
        outer_right.G_child,
        boundary_column(outer_right),
    ) == ((4, 2), 15, 4)

    for feature in features:
        mirrored = by_edge[mirror_edge_key(feature)]
        assert boundary_column(feature) >= 0
        assert (
            feature.G_child * boundary_column(feature)
            == mirrored.G_child * boundary_column(mirrored)
        )

    divergence = {composition: Fraction(0) for composition in WITNESS}
    for feature in features:
        value = boundary_column(feature)
        if feature.parent in divergence:
            divergence[feature.parent] += feature.ratio * value
        if feature.child in divergence:
            divergence[feature.child] -= value

    assert divergence == {
        (2, 2, 2): Fraction(0),
        (2, 4): Fraction(-2),
        (4, 2): Fraction(-4),
    }
    witness_value = sum(
        Fraction(multiplier) * divergence[composition]
        for composition, multiplier in WITNESS.items()
    )
    assert witness_value == 4
    assert 126 * witness_value == 504
