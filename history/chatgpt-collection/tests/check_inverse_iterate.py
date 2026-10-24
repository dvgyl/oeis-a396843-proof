#!/usr/bin/env python3
"""Independent finite checks for the inverse-iterate family and A396102.

This is a regression and source-identification check, not a replacement for
the all-index proofs in lean/More/InverseIterate.lean.  It uses only Python
integer arithmetic and the standard library.  AI-generated for Dev Goyal by
OpenAI ChatGPT; see the package AI_DISCLOSURE.md.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path


OFFICIAL_A396102_PREFIX = [
    1, 1, -2, 10, -71, 616, -6119, 67210, -799307, 10152043,
    -136403576, 1925530303, -28412020568, 436489070812,
    -6960212920001, 114914150793724, -1960409106724421,
    34499287415335777, -625380167235511394, 11663137820014193356,
    -223541345425015147487, 4399038934392019802758,
    -88806159394188157926365,
]


def x_series(degree: int) -> list[int]:
    return [0, 1] + [0] * (degree - 1)


def multiply(a: list[int], b: list[int], degree: int) -> list[int]:
    result = [0] * (degree + 1)
    for i, ai in enumerate(a[: degree + 1]):
        if ai:
            for j, bj in enumerate(b[: degree + 1 - i]):
                if bj:
                    result[i + j] += ai * bj
    return result


def compose(a: list[int], b: list[int], degree: int) -> list[int]:
    assert b[0] == 0
    result = [0] * (degree + 1)
    for ai in reversed(a[: degree + 1]):
        result = multiply(result, b, degree)
        result[0] += ai
    return result


def iterate(a: list[int], count: int, degree: int) -> list[int]:
    result = x_series(degree)
    for _ in range(count):
        result = compose(a, result, degree)
    return result


def construct_inverse_pair(parameter: int, degree: int) -> tuple[list[int], list[int]]:
    # At degree n the product R*R^[r] depends only on coefficients below n.
    # Thus R_n is its negated coefficient, with no division.
    auxiliary = [0, 1]
    for n in range(2, degree + 1):
        auxiliary.append(0)
        rhs_product = multiply(auxiliary, iterate(auxiliary, parameter, n), n)
        auxiliary[n] = -rhs_product[n]
    # The coefficient of F_n in R(F) is one.  Reversion stays integral.
    forward = [0, 1]
    for n in range(2, degree + 1):
        forward.append(0)
        forward[n] = -compose(auxiliary[: n + 1], forward, n)[n]
    return auxiliary, forward


def verify_parameter(parameter: int, degree: int) -> dict:
    auxiliary, forward = construct_inverse_pair(parameter, degree)
    x = x_series(degree)
    product = multiply(auxiliary, iterate(auxiliary, parameter, degree), degree)
    auxiliary_equation = auxiliary == [xi - pi for xi, pi in zip(x, product)]
    left_inverse = compose(auxiliary, forward, degree) == x
    right_inverse = compose(forward, auxiliary, degree) == x

    # Literal source family: F^[r] = (1+x) F^[r-1], including r=1.
    predecessor = iterate(forward, parameter - 1, degree)
    rhs = [predecessor[n] + (predecessor[n - 1] if n else 0)
           for n in range(degree + 1)]
    original_equation = iterate(forward, parameter, degree) == rhs
    coefficient_congruence = all(c % parameter == 1 % parameter for c in forward[1:])

    all_iterates = []
    current = x
    for k in range(9):
        checks = [current[n] % parameter == pow(k, n - 1, parameter)
                  for n in range(1, degree + 1)]
        all_iterates.append({"k": k, "indices_checked": degree, "passed": all(checks)})
        current = compose(forward, current, degree)

    checks = {
        "auxiliary_equation": auxiliary_equation,
        "R_composed_F_equals_x": left_inverse,
        "F_composed_R_equals_x": right_inverse,
        "literal_original_equation": original_equation,
        "positive_coefficient_congruence": coefficient_congruence,
        "iterate_congruences_k_0_through_8": all(c["passed"] for c in all_iterates),
    }
    assert all(checks.values()), (parameter, checks)
    return {
        "parameter": parameter,
        "degree": degree,
        "checks": checks,
        "iterate_checks": all_iterates,
        "R_coefficients_including_constant": auxiliary,
        "F_coefficients_including_constant": forward,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--degree", type=int, default=40)
    parser.add_argument(
        "--output", type=Path,
        default=Path(__file__).resolve().parents[1] / "validation" / "inverse_iterate_checks.json",
    )
    args = parser.parse_args()
    if args.degree < len(OFFICIAL_A396102_PREFIX):
        parser.error("degree must be at least 23 to cover the official prefix")

    family = [verify_parameter(r, args.degree) for r in range(1, 9)]
    a396102 = family[2]["F_coefficients_including_constant"]
    prefix_match = a396102[1:24] == OFFICIAL_A396102_PREFIX
    assert prefix_match, "Computed A396102 differs from the official 23-term displayed prefix"
    report = {
        "schema_version": 1,
        "status": "passed",
        "description": "Independent exact-integer finite checks; not the Lean proof",
        "ai_disclosure": "Generated by OpenAI ChatGPT for Dev Goyal",
        "arithmetic": "unbounded Python integers; triangular construction without division",
        "bounds_are_not_universal_proofs": True,
        "proof_modules": ["More.InverseIterate"],
        "source": "https://oeis.org/A396102",
        "source_checked_date": "2026-10-24",
        "degree": args.degree,
        "parameter_range": [1, 8],
        "iterate_range": [0, 8],
        "official_prefix_terms_checked": len(OFFICIAL_A396102_PREFIX),
        "official_prefix": OFFICIAL_A396102_PREFIX,
        "official_prefix_match": prefix_match,
        "all_checks_passed": True,
        "family": family,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(f"All checks passed: degree {args.degree}, r=1..8, k=0..8, 23 official prefix terms.")
    print(args.output)


if __name__ == "__main__":
    main()
