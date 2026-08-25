"""Standalone exact verifier for the k=4 degree-four decision artifacts.

The verifier consumes the persisted basis, sparse matrix, prefix solution,
inconsistency witness, and decision result.  It does not import the generator
or any max-flow implementation.  Its top-level ``verified`` flag means that
these serialized artifacts pass the exact internal checks below; it does not
mean that the verifier independently reconstructs the sparse matrix from the
composition model.  Matrix construction is covered separately by the exact
generator and its focused tests.
"""

from __future__ import annotations

import argparse
from fractions import Fraction
import json
from pathlib import Path
from typing import Any, Mapping


BASIS_SCHEMA = "chow-cone/k4-degree4-basis/v1"
SYSTEM_SCHEMA = "chow-cone/k4-degree4-training-system/v1"
WITNESS_SCHEMA = "chow-cone/k4-degree4-inconsistency-witness/v1"
SOLUTION_SCHEMA = "chow-cone/k4-degree4-prefix-solution/v1"
RESULT_SCHEMA = "chow-cone/k4-degree4-decision/v1"

VARIABLE_NAMES = ("z", "L", "R", "VL", "VR", "QL", "QR")
VARIABLE_WEIGHTS = (1, 1, 1, 2, 2, 4, 4)
MIRROR_VARIABLE_INDEX = (0, 2, 1, 4, 3, 6, 5)


class DecisionVerificationError(ValueError):
    """A persisted decision artifact is malformed or mathematically invalid."""


def _plain_int(value: Any, field: str) -> int:
    if not isinstance(value, int) or isinstance(value, bool):
        raise DecisionVerificationError(f"{field} must be an integer")
    return value


def _decimal(value: Any, field: str) -> int:
    if not isinstance(value, str) or not value:
        raise DecisionVerificationError(f"{field} must be a decimal string")
    try:
        parsed = int(value, 10)
    except ValueError as error:
        raise DecisionVerificationError(
            f"{field} must be a decimal string"
        ) from error
    if str(parsed) != value:
        raise DecisionVerificationError(f"{field} is not canonical decimal")
    return parsed


def _fraction(record: Any, field: str) -> Fraction:
    if not isinstance(record, dict) or set(record) != {"num", "den"}:
        raise DecisionVerificationError(f"{field} must be a rational record")
    numerator = _decimal(record["num"], f"{field}.num")
    denominator = _decimal(record["den"], f"{field}.den")
    if denominator <= 0:
        raise DecisionVerificationError(f"{field}.den must be positive")
    value = Fraction(numerator, denominator)
    if value.numerator != numerator or value.denominator != denominator:
        raise DecisionVerificationError(f"{field} is not reduced")
    return value


def _mirror_exponent(exponent: tuple[int, ...]) -> tuple[int, ...]:
    return tuple(exponent[index] for index in MIRROR_VARIABLE_INDEX)


def _weighted_degree(exponent: tuple[int, ...]) -> int:
    return sum(
        power * weight
        for power, weight in zip(exponent, VARIABLE_WEIGHTS)
    )


def _enumerate_exponents_from(
    variable: int, remaining: int, prefix: tuple[int, ...]
) -> list[tuple[int, ...]]:
    if variable == len(VARIABLE_NAMES):
        return [prefix]
    weight = VARIABLE_WEIGHTS[variable]
    out = []
    for power in range(remaining // weight + 1):
        out.extend(
            _enumerate_exponents_from(
                variable + 1,
                remaining - power * weight,
                prefix + (power,),
            )
        )
    return out


def _expected_raw() -> tuple[tuple[int, ...], ...]:
    return tuple(
        sorted(
            _enumerate_exponents_from(0, 4, ()),
            key=lambda exponent: (_weighted_degree(exponent), exponent),
        )
    )


def _parse_polynomial(record: Any, field: str) -> dict[tuple[int, ...], int]:
    if not isinstance(record, list) or not record:
        raise DecisionVerificationError(f"{field} must be a nonempty list")
    polynomial = {}
    for index, term in enumerate(record):
        if not isinstance(term, dict) or set(term) != {"exponents", "coefficient"}:
            raise DecisionVerificationError(f"{field}[{index}] is malformed")
        exponents = term["exponents"]
        if not isinstance(exponents, list) or len(exponents) != len(VARIABLE_NAMES):
            raise DecisionVerificationError(f"{field}[{index}] exponents malformed")
        exponent = tuple(
            _plain_int(power, f"{field}[{index}].exponents")
            for power in exponents
        )
        if any(power < 0 for power in exponent) or _weighted_degree(exponent) > 4:
            raise DecisionVerificationError(f"{field}[{index}] degree invalid")
        coefficient = _plain_int(
            term["coefficient"], f"{field}[{index}].coefficient"
        )
        if not coefficient or exponent in polynomial:
            raise DecisionVerificationError(f"{field}[{index}] term invalid")
        polynomial[exponent] = coefficient
    return polynomial


def _mirrored_polynomial(
    polynomial: Mapping[tuple[int, ...], int]
) -> dict[tuple[int, ...], int]:
    return {
        _mirror_exponent(exponent): coefficient
        for exponent, coefficient in polynomial.items()
    }


def _negated_polynomial(
    polynomial: Mapping[tuple[int, ...], int]
) -> dict[tuple[int, ...], int]:
    return {exponent: -coefficient for exponent, coefficient in polynomial.items()}


def verify_basis(document: Any) -> dict[str, Any]:
    if not isinstance(document, dict) or document.get("schema") != BASIS_SCHEMA:
        raise DecisionVerificationError("unsupported basis schema")
    variables = document.get("variables")
    if not isinstance(variables, list) or [row.get("name") for row in variables] != list(VARIABLE_NAMES):
        raise DecisionVerificationError("basis variable order mismatch")
    if [row.get("weight") for row in variables] != list(VARIABLE_WEIGHTS):
        raise DecisionVerificationError("basis variable weights mismatch")

    raw_records = document.get("raw_monomials")
    if not isinstance(raw_records, list):
        raise DecisionVerificationError("raw monomial list missing")
    raw = []
    for index, record in enumerate(raw_records):
        if not isinstance(record, dict):
            raise DecisionVerificationError(f"raw_monomials[{index}] malformed")
        exponent = tuple(
            _plain_int(value, f"raw_monomials[{index}].exponents")
            for value in record.get("exponents", [])
        )
        if len(exponent) != len(VARIABLE_NAMES):
            raise DecisionVerificationError("raw exponent length mismatch")
        if record.get("weighted_degree") != _weighted_degree(exponent):
            raise DecisionVerificationError("raw weighted degree mismatch")
        if record.get("mirror_exponents") != list(_mirror_exponent(exponent)):
            raise DecisionVerificationError("raw mirror mismatch")
        raw.append(exponent)
    if tuple(raw) != _expected_raw() or document.get("raw_monomial_count") != 60:
        raise DecisionVerificationError("raw monomial enumeration is incomplete")

    invariant = [
        _parse_polynomial(record, f"invariant_basis[{index}]")
        for index, record in enumerate(document.get("invariant_basis", []))
    ]
    anti = [
        _parse_polynomial(record, f"anti_invariant_basis[{index}]")
        for index, record in enumerate(document.get("anti_invariant_basis", []))
    ]
    balanced = [
        _parse_polynomial(record, f"balanced_invariant_basis[{index}]")
        for index, record in enumerate(
            document.get("balanced_invariant_basis", [])
        )
    ]
    if len(invariant) != 35 or len(anti) != 25 or len(balanced) != 18:
        raise DecisionVerificationError("symmetry basis dimension mismatch")
    if any(_mirrored_polynomial(polynomial) != polynomial for polynomial in invariant):
        raise DecisionVerificationError("invariant basis contains a non-invariant")
    if any(
        _mirrored_polynomial(polynomial) != _negated_polynomial(polynomial)
        for polynomial in anti
    ):
        raise DecisionVerificationError("anti basis contains a non-anti element")
    if any(
        _mirrored_polynomial(polynomial) != polynomial
        or all(exponent[0] > 0 for exponent in polynomial)
        for polynomial in balanced
    ):
        raise DecisionVerificationError("balanced basis contains an invalid element")
    if document.get("parameter_count") != 156:
        raise DecisionVerificationError("parameter count mismatch")
    names = document.get("parameter_names")
    if not isinstance(names, list) or len(names) != 156 or len(set(names)) != 156:
        raise DecisionVerificationError("parameter names malformed")
    return {
        "verified": True,
        "raw_monomials": 60,
        "invariant_basis": 35,
        "anti_invariant_basis": 25,
        "balanced_invariant_basis": 18,
        "parameters": 156,
    }


def _parse_system(document: Any) -> dict[str, Any]:
    if not isinstance(document, dict) or document.get("schema") != SYSTEM_SCHEMA:
        raise DecisionVerificationError("unsupported system schema")
    n_parameters = _plain_int(document.get("n_parameters"), "n_parameters")
    if n_parameters != 156:
        raise DecisionVerificationError("system parameter count mismatch")
    parameter_names = document.get("parameter_names")
    if not isinstance(parameter_names, list) or len(parameter_names) != n_parameters:
        raise DecisionVerificationError("system parameter names malformed")
    rows = document.get("rows")
    if not isinstance(rows, list) or document.get("n_rows") != len(rows):
        raise DecisionVerificationError("system row count mismatch")
    if document.get("dimensions") != list(range(2, 13)):
        raise DecisionVerificationError("system dimensions are not d=2,...,12")
    if len(rows) != 607 or document.get("n_edges") != 1529:
        raise DecisionVerificationError("frozen system size mismatch")
    parsed_rows = []
    labels = []
    rhs_values = []
    previous_label = None
    for expected_index, record in enumerate(rows):
        if not isinstance(record, dict) or record.get("row") != expected_index:
            raise DecisionVerificationError("system row order mismatch")
        d = _plain_int(record.get("d"), f"rows[{expected_index}].d")
        composition_values = record.get("composition")
        if not isinstance(composition_values, list) or not composition_values:
            raise DecisionVerificationError("system composition malformed")
        composition = tuple(
            _plain_int(value, f"rows[{expected_index}].composition")
            for value in composition_values
        )
        label = (d, composition)
        if previous_label is not None and label <= previous_label:
            raise DecisionVerificationError("system labels not canonical")
        previous_label = label
        entries = record.get("entries")
        if not isinstance(entries, list):
            raise DecisionVerificationError("system entries malformed")
        row = {}
        previous_column = -1
        for entry_index, entry in enumerate(entries):
            if not isinstance(entry, list) or len(entry) != 3:
                raise DecisionVerificationError("system sparse entry malformed")
            column = _plain_int(entry[0], "entry column")
            if not previous_column < column < n_parameters:
                raise DecisionVerificationError("system columns not canonical")
            previous_column = column
            numerator = _decimal(entry[1], "entry numerator")
            denominator = _decimal(entry[2], "entry denominator")
            if denominator <= 0:
                raise DecisionVerificationError("entry denominator must be positive")
            value = Fraction(numerator, denominator)
            if not value or value.numerator != numerator or value.denominator != denominator:
                raise DecisionVerificationError("entry is zero or unreduced")
            row[column] = value
        parsed_rows.append(row)
        labels.append(label)
        rhs_values.append(_fraction(record.get("rhs"), "row rhs"))
    return {
        "dimensions": tuple(document.get("dimensions", [])),
        "parameter_names": tuple(parameter_names),
        "rows": tuple(parsed_rows),
        "labels": tuple(labels),
        "rhs": tuple(rhs_values),
        "n_edges": document.get("n_edges"),
    }


def verify_witness(system: Mapping[str, Any], document: Any) -> dict[str, Any]:
    if not isinstance(document, dict) or document.get("schema") != WITNESS_SCHEMA:
        raise DecisionVerificationError("unsupported witness schema")
    multipliers = document.get("multipliers")
    if not isinstance(multipliers, list) or not multipliers:
        raise DecisionVerificationError("witness multipliers missing")
    column_sums: dict[int, Fraction] = {}
    rhs_sum = Fraction(0)
    previous_row = -1
    for index, record in enumerate(multipliers):
        if not isinstance(record, dict):
            raise DecisionVerificationError("witness multiplier malformed")
        row_index = _plain_int(record.get("row"), f"multipliers[{index}].row")
        if not previous_row < row_index < len(system["rows"]):
            raise DecisionVerificationError("witness row order invalid")
        previous_row = row_index
        label = system["labels"][row_index]
        if record.get("d") != label[0] or record.get("composition") != list(label[1]):
            raise DecisionVerificationError("witness row label mismatch")
        multiplier = _decimal(record.get("multiplier"), "witness multiplier")
        if not multiplier:
            raise DecisionVerificationError("witness multiplier must be nonzero")
        for column, value in system["rows"][row_index].items():
            updated = column_sums.get(column, Fraction(0)) + multiplier * value
            if updated:
                column_sums[column] = updated
            elif column in column_sums:
                del column_sums[column]
        rhs_sum += multiplier * system["rhs"][row_index]
    if column_sums or not rhs_sum:
        raise DecisionVerificationError("witness does not prove inconsistency")
    declared = document.get("verification")
    if not isinstance(declared, dict) or _fraction(
        declared.get("rhs_sum"), "witness verification rhs"
    ) != rhs_sum:
        raise DecisionVerificationError("witness declared RHS mismatch")
    return {
        "verified": True,
        "n_nonzero_multipliers": len(multipliers),
        "n_nonzero_column_sums": 0,
        "rhs_sum": {"num": str(rhs_sum.numerator), "den": str(rhs_sum.denominator)},
    }


def verify_prefix_solution(system: Mapping[str, Any], document: Any) -> dict[str, Any]:
    if not isinstance(document, dict) or document.get("schema") != SOLUTION_SCHEMA:
        raise DecisionVerificationError("unsupported prefix-solution schema")
    dimensions = tuple(document.get("dimensions", []))
    coefficients = document.get("coefficients")
    if not isinstance(coefficients, list) or len(coefficients) != len(system["parameter_names"]):
        raise DecisionVerificationError("prefix coefficient vector malformed")
    parsed_coefficients = [
        _fraction(value, f"coefficients[{index}]")
        for index, value in enumerate(coefficients)
    ]
    checked = 0
    for label, row, rhs in zip(system["labels"], system["rows"], system["rhs"]):
        if label[0] not in dimensions:
            continue
        actual = sum(
            (value * parsed_coefficients[column] for column, value in row.items()),
            Fraction(0),
        )
        if actual != rhs:
            raise DecisionVerificationError("prefix solution fails an equation")
        checked += 1
    if checked != document.get("verification", {}).get("n_rows"):
        raise DecisionVerificationError("prefix solution row count mismatch")
    return {"verified": True, "dimensions": list(dimensions), "n_rows": checked}


def verify_result(document: Any) -> dict[str, Any]:
    if not isinstance(document, dict) or document.get("schema") != RESULT_SCHEMA:
        raise DecisionVerificationError("unsupported result schema")
    if document.get("equality_status") != "inconsistent":
        raise DecisionVerificationError("unexpected equality decision")
    if document.get("nonnegativity_status") != "infeasible_a_fortiori":
        raise DecisionVerificationError("unexpected nonnegativity decision")
    if document.get("holdout_status") != "not_run_no_training_solution":
        raise DecisionVerificationError("unexpected holdout decision")
    return {
        "verified": True,
        "equality_status": "inconsistent",
        "nonnegativity_status": "infeasible_a_fortiori",
        "holdout_status": "not_run_no_training_solution",
    }


def verify_artifact_directory(root: str | Path) -> dict[str, Any]:
    root = Path(root)
    with root.joinpath("basis.json").open(encoding="utf-8") as stream:
        basis = json.load(stream)
    with root.joinpath("training_system.json").open(encoding="utf-8") as stream:
        system_document = json.load(stream)
    with root.joinpath("inconsistency_witness.json").open(encoding="utf-8") as stream:
        witness = json.load(stream)
    with root.joinpath("preceding_prefix_solution.json").open(encoding="utf-8") as stream:
        solution = json.load(stream)
    with root.joinpath("decision.json").open(encoding="utf-8") as stream:
        result = json.load(stream)
    basis_verification = verify_basis(basis)
    parsed_system = _parse_system(system_document)
    if tuple(basis.get("parameter_names", [])) != parsed_system["parameter_names"]:
        raise DecisionVerificationError("basis and system parameter order differ")
    return {
        "basis": basis_verification,
        "system": {
            "verified": True,
            "dimensions": list(parsed_system["dimensions"]),
            "n_rows": len(parsed_system["rows"]),
            "n_edges": parsed_system["n_edges"],
            "n_parameters": len(parsed_system["parameter_names"]),
        },
        "witness": verify_witness(parsed_system, witness),
        "preceding_prefix_solution": verify_prefix_solution(
            parsed_system, solution
        ),
        "decision": verify_result(result),
        "verified": True,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("artifact_directory", type=Path)
    args = parser.parse_args()
    print(
        json.dumps(
            verify_artifact_directory(args.artifact_directory),
            indent=2,
            sort_keys=True,
        )
    )


if __name__ == "__main__":
    main()
