"""Bounded deterministic orchestration tests for the k=4 discovery run."""

import hashlib
import json

import pytest

from k4_certificates import COST_PROFILES, allowed_edge_keys
from run_k4_discovery import (
    DEFAULT_OBJECTIVES,
    DiscoveryPlan,
    FEATURE_TABLE_SCHEMA,
    MANIFEST_SCHEMA,
    NONUNIQUENESS_SCHEMA,
    RANGE_SCHEMA,
    VERIFICATION_SCHEMA,
    main,
    run_discovery,
)
from verify_k4_certificates import verify_certificate_file


SMALL_PLAN = DiscoveryPlan(
    primary_dimensions=(2, 3, 4, 5),
    objective_dimensions=(4,),
    range_dimensions=(2, 3, 4, 5),
    objectives=DEFAULT_OBJECTIVES,
)


def _sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _snapshot(root):
    return {
        path.relative_to(root).as_posix(): path.read_bytes()
        for path in sorted(root.rglob("*"))
        if path.is_file()
    }


def test_small_plan_writes_verified_hashed_byte_reproducible_tree(tmp_path):
    output = tmp_path / "discovery"
    first_manifest = run_discovery(output, plan=SMALL_PLAN)

    assert first_manifest["schema"] == MANIFEST_SCHEMA
    assert first_manifest["plan"] == {
        "primary_dimensions": [2, 3, 4, 5],
        "primary_edge_order": "lex",
        "objective_dimensions": [4],
        "objectives": sorted(COST_PROFILES),
        "range_dimensions": [2, 3, 4, 5],
    }
    assert (output / "primary").is_dir()
    assert (output / "objectives").is_dir()
    assert (output / "ranges").is_dir()

    expected_primary = {
        f"primary/d{d:02d}_lex.json" for d in range(2, 6)
    }
    expected_objectives = {
        f"objectives/d04_{objective}.json" for objective in COST_PROFILES
    }
    expected_ranges = {
        f"ranges/d{d:02d}_ranges.json" for d in range(2, 6)
    }
    expected_features = {
        f"features/d{d:02d}_features.jsonl" for d in range(2, 6)
    }
    expected_analysis = {
        "ansatz_results.json",
        "features/schema.json",
        "interval_witnesses.json",
        "interval_witnesses_d03_d10.json",
        "nonuniqueness_summary.json",
    }
    listed = {entry["path"] for entry in first_manifest["files"]}
    assert listed == (
        expected_primary
        | expected_objectives
        | expected_ranges
        | expected_features
        | expected_analysis
        | {"verification_summary.json"}
    )
    for entry in first_manifest["files"]:
        path = output / entry["path"]
        assert path.is_file()
        assert entry["sha256"] == _sha256(path)

    for relative in expected_primary | expected_objectives:
        assert verify_certificate_file(output / relative)["verified"]

    feature_schema = json.loads(
        (output / "features/schema.json").read_text(encoding="utf-8")
    )
    assert feature_schema["schema"] == FEATURE_TABLE_SCHEMA
    assert [row["d"] for row in feature_schema["files"]] == [2, 3, 4, 5]
    for row in feature_schema["files"]:
        lines = (output / row["path"]).read_text(encoding="utf-8").splitlines()
        assert len(lines) == row["n_rows"]
        assert all(json.loads(line)["d"] == row["d"] for line in lines)

    nonuniqueness = json.loads(
        (output / "nonuniqueness_summary.json").read_text(encoding="utf-8")
    )
    assert nonuniqueness["schema"] == NONUNIQUENESS_SCHEMA
    assert [row["d"] for row in nonuniqueness["representative_dimensions"]] == [4]

    verification = json.loads(
        (output / "verification_summary.json").read_text(encoding="utf-8")
    )
    assert verification["schema"] == VERIFICATION_SCHEMA
    assert verification["all_verified"]
    assert verification["n_certificates"] == len(
        expected_primary | expected_objectives
    )
    assert all(
        row["verification"]["verified"]
        for row in verification["certificates"]
    )

    for d in range(2, 6):
        document = json.loads(
            (output / f"ranges/d{d:02d}_ranges.json").read_text(
                encoding="utf-8"
            )
        )
        assert document["schema"] == RANGE_SCHEMA
        assert document["d"] == d
        assert document["method"]["cutoff"]["maximum_dimension"] == 10
        assert len(document["edges"]) == len(allowed_edge_keys(d))
        assert sum(document["classification_counts"].values()) == len(
            document["edges"]
        )
        encoded_keys = [
            (tuple(row["parent"]), row["block"], row["left"])
            for row in document["edges"]
        ]
        assert encoded_keys == allowed_edge_keys(d)
        for row in document["edges"]:
            minimum = int(row["minimum"])
            current = int(row["current"])
            maximum = int(row["maximum"])
            assert str(minimum) == row["minimum"]
            assert str(current) == row["current"]
            assert str(maximum) == row["maximum"]
            assert 0 <= minimum <= current <= maximum

    first_snapshot = _snapshot(output)
    second_manifest = run_discovery(output, plan=SMALL_PLAN)
    second_snapshot = _snapshot(output)
    assert second_manifest == first_manifest
    assert second_snapshot == first_snapshot


def test_dimension_guard_rejects_d_above_16_before_writing(tmp_path):
    output = tmp_path / "forbidden"
    plan = DiscoveryPlan(
        primary_dimensions=(2, 17),
        objective_dimensions=(),
        range_dimensions=(),
        objectives=(),
    )
    with pytest.raises(ValueError, match="above 16|d=17"):
        run_discovery(output, plan=plan)
    assert not output.exists()


def test_cli_accepts_an_explicit_bounded_plan(tmp_path, capsys):
    output = tmp_path / "cli"
    assert main(
        [
            "--output-dir",
            str(output),
            "--primary-dimensions",
            "2",
            "--objective-dimensions",
            "",
            "--range-dimensions",
            "",
            "--objectives",
            "",
        ]
    ) == 0
    report = json.loads(capsys.readouterr().out)
    assert report["manifest"] == str(output / "manifest.json")
    assert (output / "primary/d02_lex.json").is_file()
    assert json.loads((output / "manifest.json").read_text())[
        "plan"
    ]["primary_dimensions"] == [2]
