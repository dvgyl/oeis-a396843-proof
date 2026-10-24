#!/usr/bin/env python3
"""Finite, exact checks for a family of Hanna generating functions.

For an integer m, construct A_m(x) = x + sum_{n>=2} a_n(m) x^n from

    A_m(x*A_m(x) - m*x*A_m(x)**2) = x**2.

Construction uses the coefficient of x**(n+1) to determine a_n: with
a_n temporarily zero, that coefficient is -a_n. All arithmetic uses
Python integers. There are no numerical approximations or dependencies.

The checks below corroborate finite instances of the accompanying
mathematical proof; they do not prove statements about all n.

Sources for the known prefixes and the counterexample's conjecture:
    https://oeis.org/A396843  (m = 3)
    https://oeis.org/A396844  (m = 4)

Usage:
    python verify_hanna_congruences.py
    python verify_hanna_congruences.py --terms 100
"""

import argparse
import json
from math import gcd


KNOWN_PREFIXES = {
    3: [
        1, 3, 15, 117, 975, 8631, 79839, 763209, 7477701,
        74700315, 758027205, 7792075341, 80968633731,
        849122117991, 8975430108207, 95526419313969,
        1022842349889807, 11010529561615155,
        119088263248757523, 1293532210166103045,
    ],
    4: [
        1, 4, 28, 288, 3204, 37984, 470864, 6031872,
        79213292, 1060777376, 14430659088, 198871682304,
        2770567442480, 38955095818496, 552076498222272,
        7878133131149312, 113101684573952804,
        1632423925911360864, 23673430851581280880,
        344778022864540259584,
    ],
}


def require(condition, message):
    """Keep validation active even when Python is invoked with -O."""
    if not condition:
        raise AssertionError(message)


def multiply(left, right, degree):
    """Multiply coefficient lists, retaining degrees 0 through degree."""
    result = [0] * (degree + 1)
    for i, left_coefficient in enumerate(left[: degree + 1]):
        if not left_coefficient:
            continue
        for j, right_coefficient in enumerate(right[: degree - i + 1]):
            if right_coefficient:
                result[i + j] += left_coefficient * right_coefficient
    return result


def inner_argument(series, parameter, degree):
    """Return x*A(x) - m*x*A(x)^2 through the requested degree."""
    square = multiply(series, series, degree - 1)
    result = [0] * (degree + 1)
    for index in range(1, degree + 1):
        coefficient = series[index - 1] if index - 1 < len(series) else 0
        result[index] = coefficient - parameter * square[index - 1]
    return result


def compose_by_powers(outer, inner, degree):
    """Compute a truncated composition by successively forming powers."""
    require(inner[0] == 0, "Composition requires zero constant term.")
    result = [0] * (degree + 1)
    power = [1] + [0] * degree
    for exponent, coefficient in enumerate(outer):
        if coefficient:
            for index, power_coefficient in enumerate(power):
                result[index] += coefficient * power_coefficient
        if exponent + 1 < len(outer):
            power = multiply(power, inner, degree)
    return result


def compose_by_horner(outer, inner, degree):
    """A separate composition algorithm for the final residual check."""
    require(inner[0] == 0, "Composition requires zero constant term.")
    result = [0] * (degree + 1)
    for coefficient in reversed(outer):
        result = multiply(result, inner, degree)
        result[0] += coefficient
    return result


def construct_coefficients(parameter, terms):
    """Return [a_0, ..., a_terms], with a_0 = 0 and a_1 = 1.

    At stage n, a_n occurs with coefficient 1 in degree n+1 of the
    defining composition; every other contribution uses earlier terms.
    """
    series = [0, 1]
    for index in range(2, terms + 1):
        series.append(0)
        inner = inner_argument(series, parameter, index + 1)
        composition = compose_by_powers(series, inner, index + 1)
        series[index] = -composition[index + 1]
    return series


def compositional_inverse(series):
    """Construct B(x) from A(B(x)) = x, using only integer operations.

    With b_n temporarily zero, degree n of A(B(x)) is -b_n, because
    A has linear coefficient 1. This uses neither the congruences nor
    the normalized inverse identity checked later.
    """
    inverse = [0, 1]
    for index in range(2, len(series)):
        inverse.append(0)
        composition = compose_by_horner(series[: index + 1], inverse, index)
        inverse[index] = -composition[index]
    return inverse


def predicted_square_modulus_residue(parameter, index):
    """The accompanying theorem's prediction, used only for comparison."""
    if index == 1:
        return 1
    predecessor = index - 1
    if predecessor & (predecessor - 1):
        return 0
    exponent = predecessor.bit_length() - 1
    sign = -1 if exponent % 2 else 1
    return (parameter * sign) % (parameter * parameter)


def verify(parameter, series):
    terms = len(series) - 1
    require(series[0] == 0 and series[1] == 1, "Incorrect normalization.")

    prefix = KNOWN_PREFIXES.get(parameter, [])
    prefix_terms = min(terms, len(prefix))
    require(
        series[1 : prefix_terms + 1] == prefix[:prefix_terms],
        f"Known OEIS prefix mismatch for m={parameter}.",
    )

    inverse = compositional_inverse(series)
    dyadic_indices = []
    for index in range(1, terms + 1):
        expected_parity = 1 if index == 1 else parameter % 2
        require(
            series[index] % 2 == expected_parity,
            f"Parity failure at m={parameter}, n={index}.",
        )
        require(
            series[index] % (parameter * parameter)
            == predicted_square_modulus_residue(parameter, index),
            f"Congruence failure at m={parameter}, n={index}.",
        )
        digit_weight = (index - 1).bit_count()
        divisor = parameter ** digit_weight
        require(
            series[index] % divisor == 0,
            f"Binary digit bound failure for A at m={parameter}, n={index}.",
        )
        require(
            inverse[index] % divisor == 0,
            f"Binary digit bound failure for B at m={parameter}, n={index}.",
        )
        if index > 1 and (index - 1) & (index - 2) == 0:
            # This verifies v_p(a_n) = v_p(m) simultaneously for every
            # prime p dividing m, without factoring either integer.
            require(
                series[index] % parameter == 0
                and gcd(series[index] // parameter, parameter) == 1,
                f"Exact dyadic valuation failure at m={parameter}, n={index}.",
            )
            dyadic_indices.append(index)

    # Coefficients through a_N determine the composition through degree
    # N+1. The omitted a_(N+1) first affects degree N+2.
    degree = terms + 1
    inner = inner_argument(series, parameter, degree)
    residual = compose_by_horner(series, inner, degree)
    residual[2] -= 1
    require(
        all(coefficient == 0 for coefficient in residual),
        f"Nonzero defining-equation residual for m={parameter}.",
    )

    target_inverse = [0, 1] + [0] * (terms - 1)
    require(
        compose_by_powers(series, inverse, terms) == target_inverse,
        f"A(B(x)) differs from x for m={parameter}.",
    )
    require(
        compose_by_powers(inverse, series, terms) == target_inverse,
        f"B(A(x)) differs from x for m={parameter}.",
    )

    # If A=x*F and B=x*G, the proof uses F=G(x^2)+m*x*F^2.
    # Check that identity directly, independently of the inverse's
    # construction, through all available degrees of F and G.
    normalized_a = series[1:]
    normalized_b = inverse[1:]
    for index in range(terms):
        right = normalized_b[index // 2] if index % 2 == 0 else 0
        if index:
            right += parameter * sum(
                normalized_a[left] * normalized_a[index - 1 - left]
                for left in range(index)
            )
        require(
            normalized_a[index] == right,
            f"Normalized inverse identity failure at m={parameter}, degree={index}.",
        )

    return {
        "m": parameter,
        "known_prefix_terms_checked": prefix_terms,
        "parity_terms_checked": terms,
        "mod_m_squared_terms_checked": terms,
        "binary_digit_bound_terms_checked_A": terms,
        "binary_digit_bound_terms_checked_B": terms,
        "exact_dyadic_valuation_indices_checked": len(dyadic_indices),
        "composition_residual_zero_through_degree": degree,
        "both_inverse_compositions_equal_x_through_degree": terms,
        "normalized_inverse_identity_checked_through_degree": terms - 1,
    }


def term_count(value):
    try:
        result = int(value)
    except ValueError as error:
        raise argparse.ArgumentTypeError("terms must be an integer") from error
    if result < 17:
        raise argparse.ArgumentTypeError(
            "terms must be at least 17 to include the counterexample"
        )
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--terms", type=term_count, default=100,
        help="highest coefficient index to construct and check (default: 100)",
    )
    arguments = parser.parse_args()
    checks = []
    counterexample = None
    binary_bound_example = None
    for parameter in range(2, 10):
        series = construct_coefficients(parameter, arguments.terms)
        checks.append(verify(parameter, series))
        if parameter == 3:
            example_index = 32 if arguments.terms >= 32 else 16
            remainder = series[example_index]
            actual_valuation = 0
            while remainder % 3 == 0:
                actual_valuation += 1
                remainder //= 3
            binary_bound_example = {
                "m": 3,
                "n": example_index,
                "ones_in_binary_n_minus_1": (example_index - 1).bit_count(),
                "guaranteed_v_3_lower_bound": (example_index - 1).bit_count(),
                "actual_v_3": actual_valuation,
            }
        if parameter == 4:
            value = series[17]
            require(value == 113101684573952804, "Counterexample mismatch.")
            require(value % 16 == 4, "Unexpected counterexample residue.")
            # 17 - 1 = 2^4, whose exponent is even. Thus 17 cannot have
            # the form 2*4^k + 1, which has exponent 2*k + 1 instead.
            require((17 - 1).bit_length() - 1 == 4, "Index check failed.")
            counterexample = {
                "sequence": "A396844",
                "n": 17,
                "a_n": value,
                "residue_mod_16": value % 16,
                "listed_conjecture_predicts_residue": 0,
            }
    print(json.dumps({
        "status": "all finite exact-arithmetic checks passed",
        "scope": "Finite verification only; not a proof for all indices.",
        "terms_per_parameter": arguments.terms,
        "checks": checks,
        "counterexample": counterexample,
        "binary_bound_example": binary_bound_example,
    }, indent=2))


if __name__ == "__main__":
    main()
