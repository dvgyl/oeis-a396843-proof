#!/usr/bin/env python3
"""Exact, finite checks for the two new compositional-series families.

The coefficients are constructed from the defining equations using triangular
integer recursions. Neither constructor uses a conjectured residue formula.
The later checks compare those independently constructed coefficients with the
proved formulas. This program is finite evidence, not an all-index proof.

Run from the package root:
    python3 scripts/verify_coefficients.py --terms 40 \
        --output reproducibility/coefficients_40.json
"""

from __future__ import annotations

import argparse
import hashlib
import json
from math import comb
from pathlib import Path
import sys
from time import perf_counter
from typing import Iterable


class VerificationError(RuntimeError):
    """A check failed; the CLI will return a nonzero status."""


class Checks:
    def __init__(self) -> None:
        self.count = 0

    def require(self, condition: bool, label: str) -> None:
        self.count += 1
        if not condition:
            raise VerificationError(label)


def multiply(a: list[int], b: list[int], degree: int) -> list[int]:
    """Cauchy product, retaining coefficients zero through degree."""
    out = [0] * (degree + 1)
    for i, ai in enumerate(a[: degree + 1]):
        if ai == 0:
            continue
        for j, bj in enumerate(b[: degree + 1 - i]):
            if bj:
                out[i + j] += ai * bj
    return out


def compose(outer: list[int], inner: list[int], degree: int) -> list[int]:
    """Return outer(inner(X)), using exact Horner evaluation."""
    if not inner or inner[0] != 0:
        raise ValueError("The inner formal series must have constant term zero")
    out = [0] * (degree + 1)
    for value in reversed(outer[: degree + 1]):
        out = multiply(out, inner, degree)
        out[0] += value
    return out


def iterates(a: list[int], maximum: int, degree: int) -> list[list[int]]:
    identity = [0] * (degree + 1)
    if degree:
        identity[1] = 1
    result = [identity]
    for _ in range(maximum):
        result.append(compose(a, result[-1], degree))
    return result


def generate_r(r: int, degree: int) -> list[int]:
    """Construct F_r = X + F_r^(circ r) F_r^(circ(r+1)).

    The coefficient in degree n of the product uses only coefficients below
    degree n in either factor. Thus a_n is the product coefficient computed
    from the already constructed a_1,...,a_(n-1).
    """
    if r < 1 or degree < 1:
        raise ValueError("r and degree must both be positive")
    a = [0, 1]
    for n in range(2, degree + 1):
        powers = iterates(a, r + 1, n - 1)
        left, right = powers[r], powers[r + 1]
        a.append(sum(left[i] * right[n - i] for i in range(1, n)))
    return a


def scaled_argument(a: list[int], q: int, degree: int) -> list[int]:
    """X - X*L_q(A), where [X^j]L_q(A) = q^(j-1)*a_j."""
    out = [0] * (degree + 1)
    if degree:
        out[1] = 1
    q_power = 1
    for j in range(1, min(len(a), degree)):
        out[j + 1] = -q_power * a[j]
        q_power *= q
    return out


def generate_q(q: int, degree: int) -> list[int]:
    """Construct G_q(X - X*L_q(G_q)) = X without dividing by q.

    With a_n temporarily zero, the degree-n coefficient of the composition
    is a residual determined by earlier coefficients. The actual a_n enters
    the outer series with coefficient exactly one and first enters the inner
    argument in degree n+1. Therefore a_n is minus that residual.
    """
    if q < 1 or degree < 1:
        raise ValueError("q and degree must both be positive")
    a = [0, 1]
    for n in range(2, degree + 1):
        argument = scaled_argument(a, q, n)
        residual = compose(a, argument, n)[n]
        a.append(-residual)
    return a


R_PREFIXES = {
    2: ("A396099", [1, 1, 5, 39, 383, 4357, 55057, 754223]),
    3: ("A396797", [1, 1, 7, 79, 1135, 18985, 353677, 7153189]),
    4: ("A396798", [1, 1, 9, 133, 2517, 55609, 1370321, 36691293]),
    5: ("A396807", [1, 1, 11, 201, 4721, 129671, 3976201, 132554541]),
}

Q_PREFIXES = {
    4: ("A393856", [1, 1, 6, 121, 8466, 2227706, 2299117036, 9437900978761]),
    5: ("A393857", [1, 1, 7, 205, 26869, 16984687, 53213653657, 831942602359489]),
    6: ("A393858", [1, 1, 8, 323, 71744, 93490314, 727730885904, 33959564479215663]),
    7: ("A393859", [1, 1, 9, 481, 167937, 404407577, 6800120127457, 800088549123479905]),
}


def coefficient_digest(a: list[int]) -> str:
    return hashlib.sha256(("\n".join(map(str, a)) + "\n").encode()).hexdigest()


def check_prefix(
    a: list[int], parameter: int, table: dict[int, tuple[str, list[int]]], checks: Checks
) -> dict[str, object] | None:
    if parameter not in table:
        return None
    sequence, prefix = table[parameter]
    length = min(len(prefix), len(a) - 1)
    for n in range(1, length + 1):
        checks.require(a[n] == prefix[n - 1], f"{sequence}: OEIS prefix mismatch at n={n}")
    return {"sequence": sequence, "terms_matched": length, "source": f"https://oeis.org/{sequence}"}


def verify_r(r: int, degree: int, maximum: int, checks: Checks) -> dict[str, object]:
    start_count = checks.count
    a = generate_r(r, degree)
    maximum = max(maximum, r + 1, 3 if r == 2 else 8 if r == 4 else 0)
    powers = iterates(a, maximum, degree)
    product = multiply(powers[r], powers[r + 1], degree)
    product[1] += 1
    for n in range(degree + 1):
        checks.require(a[n] == product[n], f"r={r}: exact defining equation failed at n={n}")

    modulus = 2 * r
    for k, power in enumerate(powers):
        for n, actual in enumerate(power):
            if n == 0:
                expected = 0
            elif n == 1:
                expected = 1
            else:
                h_n = comb(n - 2, 2) if n >= 4 else 0
                correction = r * h_n if r % 2 == 0 and k % 2 else 0
                expected = pow(k, n - 1, modulus) + correction
            checks.require((actual - expected) % modulus == 0,
                           f"r={r}, k={k}: general iterate formula failed at n={n}")
    for n in range(1, degree + 1):
        checks.require(a[n] % 2 == 1, f"r={r}: general parity failed at n={n}")

    named = []
    if r == 2:
        named = ["all_odd", "residue_cycle", "second_iterate_tail", "cancellation_tail"]
        for n in range(3, degree + 1):
            checks.require(a[n] % 4 == (1, 3, 3, 1)[(n - 3) % 4],
                           f"A396099: residue cycle failed at n={n}")
            checks.require(powers[2][n] % 4 == 0,
                           f"A396099: second iterate tail failed at n={n}")
        for n in range(1, degree + 1):
            expected = 1 if n == 1 else 0 if n == 2 else 2
            checks.require((a[n] - powers[3][n - 1]) % 4 == expected,
                           f"A396099: full cancellation identity failed at n={n}")
    if r == 4:
        named = ["corrected_coefficient_phase", "counterexample_to_source_phase"]
        checks.require(a[3] == 9 and a[3] % 8 != 5,
                       "A396798: the stated phase counterexample was not reproduced")
        for n in range(2, degree + 1):
            checks.require(a[n] % 8 == (1, 1, 5, 5)[(n - 2) % 4],
                           f"A396798: corrected phase failed at n={n}")
        for k, last in ((2, 3), (4, 2), (6, 3), (8, 1)):
            named.append(f"iterate_{k}_tail")
            for n in range(last + 1, degree + 1):
                checks.require(powers[k][n] % 8 == 0,
                               f"A396798: iterate {k} tail failed at n={n}")
        for k, block in ((3, (3, 1, 7, 5)), (5, (5, 1, 1, 5)), (7, (7, 1, 3, 5))):
            named.append(f"iterate_{k}_cycle")
            for n in range(2, degree + 1):
                checks.require(powers[k][n] % 8 == block[(n - 2) % 4],
                               f"A396798: iterate {k} cycle failed at n={n}")
    if r == 5:
        named = ["all_coefficients_one_mod_ten", "natural_iterates_in_checked_range"]
        for n in range(1, degree + 1):
            checks.require(a[n] % 10 == 1, f"A396807: coefficient congruence failed at n={n}")

    prefix = check_prefix(a, r, R_PREFIXES, checks)
    return {
        "parameter": r,
        "degree": degree,
        "natural_iterates_checked": [0, maximum],
        "coefficient_checks": checks.count - start_count,
        "named_checks": named,
        "oeis_prefix": prefix,
        "initial_coefficients": a[1:9],
        "coefficient_sha256": coefficient_digest(a),
    }


def is_power_of_two(n: int) -> bool:
    return n > 0 and (n & (n - 1)) == 0


def verify_q(q: int, degree: int, checks: Checks) -> dict[str, object]:
    start_count = checks.count
    a = generate_q(q, degree)
    argument = scaled_argument(a, q, degree)
    identity = [0, 1] + [0] * (degree - 1)
    forward = compose(a, argument, degree)
    backward = compose(argument, a, degree)
    for n in range(degree + 1):
        checks.require(forward[n] == identity[n], f"q={q}: defining equation failed at n={n}")
        checks.require(backward[n] == identity[n], f"q={q}: inverse identity failed at n={n}")
    for n in range(1, degree + 1):
        checks.require(a[n] % (q + 1) == 1 % (q + 1),
                       f"q={q}: modulus q+1 congruence failed at n={n}")
    for n in range(degree + 1):
        expected_odd = is_power_of_two(n) if q % 2 == 0 else n > 0
        checks.require(bool(a[n] % 2) == expected_odd,
                       f"q={q}: parity classification failed at n={n}")
    prefix = check_prefix(a, q, Q_PREFIXES, checks)
    named = [f"all_coefficients_one_mod_{q + 1}"]
    if q in (4, 6):
        named.append("odd_iff_power_of_two")
    return {
        "parameter": q,
        "degree": degree,
        "coefficient_checks": checks.count - start_count,
        "named_checks": named,
        "oeis_prefix": prefix,
        "initial_coefficients": a[1:9],
        "coefficient_sha256": coefficient_digest(a),
    }


def verify_all(
    degree: int = 40,
    r_parameters: Iterable[int] = range(1, 9),
    q_parameters: Iterable[int] = range(1, 9),
    iterate_max: int | None = None,
) -> dict[str, object]:
    if degree < 8:
        raise ValueError("Use at least eight terms to cover the displayed prefixes and residue blocks")
    r_parameters = list(r_parameters)
    q_parameters = list(q_parameters)
    if any(p < 1 for p in r_parameters + q_parameters):
        raise ValueError("Every family parameter must be positive")
    if iterate_max is not None and iterate_max < 0:
        raise ValueError("The maximum iterate must be nonnegative")
    checks = Checks()
    started = perf_counter()
    r_results = [verify_r(r, degree, 2 * r + 2 if iterate_max is None else iterate_max, checks)
                 for r in r_parameters]
    q_results = [verify_q(q, degree, checks) for q in q_parameters]
    return {
        "schema_version": 1,
        "result": "pass",
        "scope": "Exact finite checks only; not an all-index proof or a Lean build",
        "arithmetic": "Python arbitrary-precision integers; no floating point",
        "construction": {
            "r_family": "Triangular coefficient recursion from F=X+F^(circ r)*F^(circ(r+1))",
            "q_family": "Triangular coefficient recursion from G(X-X*L_q(G))=X",
            "uses_residue_candidates_to_construct_coefficients": False,
        },
        "degree": degree,
        "coefficient_checks": checks.count,
        "r_family": r_results,
        "q_family": q_results,
        "elapsed_seconds": round(perf_counter() - started, 6),
        "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    }


def parse_parameters(text: str) -> list[int]:
    try:
        values = list(dict.fromkeys(int(part.strip()) for part in text.split(",") if part.strip()))
    except ValueError as error:
        raise argparse.ArgumentTypeError("Use a comma-separated list of positive integers") from error
    if not values or any(value < 1 for value in values):
        raise argparse.ArgumentTypeError("Use a nonempty list of positive integers")
    return values


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--terms", type=int, default=40, help="Highest coefficient index, at least 8 (default: 40)")
    parser.add_argument("--r", type=parse_parameters, default=list(range(1, 9)),
                        help="Comma-separated r parameters (default: 1,2,3,4,5,6,7,8)")
    parser.add_argument("--q", type=parse_parameters, default=list(range(1, 9)),
                        help="Comma-separated q parameters (default: 1,2,3,4,5,6,7,8)")
    parser.add_argument("--iterate-max", type=int,
                        help="Maximum natural iterate; default 2*r+2, raised when needed for defining/named checks")
    parser.add_argument("--output", type=Path, help="Write the full JSON evidence report to this path")
    args = parser.parse_args()
    try:
        report = verify_all(args.terms, args.r, args.q, args.iterate_max)
    except (VerificationError, ValueError) as error:
        print(f"FAIL: {error}", file=sys.stderr)
        return 1
    text = json.dumps(report, indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(text, encoding="utf-8")
        print(f"PASS: {report['coefficient_checks']} coefficient checks through degree {args.terms}; "
              f"{len(args.r)} r parameters and {len(args.q)} q parameters. Report: {args.output}")
    else:
        print(text, end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
