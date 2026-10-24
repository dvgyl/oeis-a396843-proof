#!/usr/bin/env python3
"""Rebuild all advertised results, compile typed contracts, and audit axioms.

Only complete validation is supported.  The required endpoint list is fixed
here as well as recorded in validation/final_theorems.json, so removing an
unproved claim from the manifest cannot turn an incomplete run into success.
Mechanical acceptance does not replace a mathematical review of definitions
and of their correspondence with the manuscripts.
"""

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
import time
import tomllib
import zipfile

from audit_axioms import AuditError, audit_text, required_theorems


EXPECTED_TOOLCHAIN = "leanprover/lean4:v4.19.0"
EXPECTED_MATHLIB_REV = "c44e0c8ee63ca166450922a373c7409c5d26b00b"
EXPECTED_MATHLIB_URL = "https://github.com/leanprover-community/mathlib4.git"
EXPECTED_PACKAGE = "congruence_proofs"
EXPECTED_IMPORTS = ["Consecutive", "Related", "Hanna.Acceptance", "More", "Round3", "Round4"]
BASELINE_ARCHIVE = "prior_work/oeis_congruence_proofs_Dev_Goyal_v1.zip"
BASELINE_SHA256 = "04f347b0e116a1c92cd7a1f21f38a37ae3dfb71c733dd5f55769accd0714489c"

PREVIOUS_V2_ARCHIVE = "prior_work/oeis_proofs_complete_Dev_Goyal_v2.zip"
PREVIOUS_V2_SHA256 = "b28c6de12f53e862b670d37d79d8b5f11333ce3d7acd44e61cb27eb2b99dbc10"
PREVIOUS_V3_ARCHIVE = "prior_work/oeis_proofs_complete_Dev_Goyal_v3.zip"
PREVIOUS_V3_SHA256 = "6a0cbeb94076a90e8938627a156ed4152f6cc3fd88546d0d2e29cd9331744d41"
RETAINED_ARCHIVES = {BASELINE_ARCHIVE, PREVIOUS_V2_ARCHIVE, PREVIOUS_V3_ARCHIVE}

# Explicit reviewed mathematical endpoints.  Intermediate algebra lemmas are
# dependencies of these declarations, and therefore included in their audits.
ENDPOINT_GROUPS = {
    "construction_and_natural_iterates": [
        "Consecutive.existence_uniqueness",
        "Consecutive.solution_normalized",
        "Consecutive.solution_equation",
        "Consecutive.map_solution",
        "Consecutive.map_iter",
        "Consecutive.iter_solution_mod",
        "Consecutive.map_iter_solution_mod",
        "Consecutive.iter_solution_mod_eq_X_iff",
        "Consecutive.iter_solution_mod_period",
    ],
    "integer_iterates": [
        "Consecutive.ziter_normalized",
        "Consecutive.map_ziter",
        "Consecutive.ziter_negative_is_inverse",
        "Consecutive.ziter_solution_mod",
        "Consecutive.map_ziter_solution_mod",
        "Consecutive.integerIterateCoeff_mod",
        "Consecutive.ziter_solution_mod_eq_X_iff",
    ],
    "a396099_all_four": [
        "Consecutive.a396099_all_four",
        "Consecutive.a396099_odd",
        "Consecutive.a396099_residue",
        "Consecutive.a396099_period",
        "Consecutive.a396099_second_iterate_series",
        "Consecutive.a396099_second_iterate",
        "Consecutive.a396099_difference_series",
        "Consecutive.a396099_difference",
    ],
    "a396798": [
        "Consecutive.a396798_iterate_residue",
        "Consecutive.a396798_corrected_residue",
        "Consecutive.a396798_corrected_period",
        "Consecutive.a396798_counterexample",
        "Consecutive.a396798_literal_period_false",
        "Consecutive.a396798_second_iterate",
        "Consecutive.a396798_fourth_iterate",
        "Consecutive.a396798_sixth_iterate",
        "Consecutive.a396798_eighth_iterate",
        "Consecutive.a396798_third_iterate_period",
        "Consecutive.a396798_fifth_iterate_period",
        "Consecutive.a396798_seventh_iterate_period",
    ],
    "a396807": [
        "Consecutive.a396807_residue",
        "Consecutive.a396807_iterate_residue",
        "Consecutive.a396807_integer_iterate_congruence",
    ],
    "scaled_inverse_family": [
        "Hanna.Related.ScaledInverse.existence_uniqueness",
        "Hanna.Related.ScaledInverse.scaledSolution_normalized",
        "Hanna.Related.ScaledInverse.scaledSolution_equation",
        "Hanna.Related.ScaledInverse.map_scaledSolution",
        "Hanna.Related.ScaledInverse.integer_mod_parameter_add_one",
        "Hanna.Related.ScaledInverse.integer_coeff_odd_iff",
        "Hanna.Related.ScaledInverse.a393856_mod_five",
        "Hanna.Related.ScaledInverse.a393856_parity",
        "Hanna.Related.ScaledInverse.a393857_mod_six",
        "Hanna.Related.ScaledInverse.a393858_mod_seven",
        "Hanna.Related.ScaledInverse.a393858_parity",
        "Hanna.Related.ScaledInverse.a393859_mod_eight",
    ],
    "hanna_regression": ["Hanna.Acceptance." + suffix for suffix in (
        "existence_uniqueness", "compositional_inverse",
        "coefficient_polynomial_specialization", "parity_odd", "parity_even",
        "mod_parameter_squared", "binary_divisibility_polynomial",
        "inverse_binary_divisibility_polynomial", "binary_divisibility_integer",
        "inverse_binary_divisibility_integer", "power_of_two_index",
        "prime_divisibility_lower_bound", "prime_exponent_exists_unique",
        "minimum_prime_exponent_iff", "residues_parameter_three",
        "residues_parameter_four",
    )],
    "a396093_rational_parity": ["RationalParity." + suffix for suffix in (
        "B_denominator", "A_definition", "map_A", "third_period_denominator",
        "a396093_residue", "a396093_even_iff", "a396093_even_indices",
        "a396093_odd_indices_original",
    )],
    "cubic_reversion": ["More.CubicReversion." + suffix for suffix in (
        "frobenius_substitution", "existence_uniqueness",
        "cubicSolution_normalized", "cubicSolution_equation",
        "a389474_normalized", "a389474_equation", "a389474_unique",
        "a389474_existence_uniqueness",
        "a389474_square_mod_nine", "a389474_conjecture_3", "a389474_conjecture_4",
        "a389475_normalized", "a389475_equation", "a389475_unique",
        "a389475_existence_uniqueness",
        "a389475_cube_mod_three", "a389475_square_mod_three",
        "a389475_conjecture_4a", "a389475_conjecture_4b",
    )],
    "known_stirling_periodicity_formalization": [
        "More.PowerPeriodicity.nat_pow_totient_add_modEq",
        "More.PowerPeriodicity.pow_totient_add_eq",
        "More.TailPeriodicity.leastPeriod_spec",
        "More.Stirling.transform_periodic_of_powers",
        "More.Stirling.transform_totient_period",
        "More.Stirling.transform_eventually_periodic",
        "More.Stirling.transform_exact_tail_period",
    ] + ["More.Stirling." + entry + suffix
         for suffix in ("_period", "_leastPeriod_dvd")
         for entry in ("A052895", "A064618", "A354242", "A167137", "A305550", "A306082", "A080253")],
    "a396102_inverse_iterate": ["InverseIterate." + suffix for suffix in (
        "R_existence_uniqueness", "R_equation", "F_normalized", "compose_R_F",
        "compose_F_R", "F_original_equation", "F_original_existence_uniqueness",
        "F_original_unique", "map_F", "F_mod", "coefficient_congruence",
        "a396102_definition", "a396102_unique", "a396102_congruence",
        "iterate_coefficient_congruence",
    )],
}
# Round-three requirements remain fixed independently of the editable manifest.
ENDPOINT_GROUPS.update({'a397588_differential_parity': ['Round3.DifferentialParity.existence_uniqueness',
                                 'Round3.DifferentialParity.A_normalized',
                                 'Round3.DifferentialParity.A_equation',
                                 'Round3.DifferentialParity.map_A',
                                 'Round3.DifferentialParity.A_mod_two_quadratic',
                                 'Round3.DifferentialParity.a397588_parity',
                                 'Round3.DifferentialParity.A_mod_three',
                                 'Round3.DifferentialParity.a397588_divisible_by_three'],
 'a389536_mahler_mod_four': ['Round3.MahlerParity.existence_uniqueness',
                             'Round3.MahlerParity.A_normalized',
                             'Round3.MahlerParity.A_equation',
                             'Round3.MahlerParity.map_A',
                             'Round3.MahlerParity.A_mod_four',
                             'Round3.MahlerParity.a389536_residue',
                             'Round3.MahlerParity.a389536_four_dvd_iff'],
 'elementary_source_contracts': ['Round3.ElementaryContracts.differential_existence',
                                 'Round3.ElementaryContracts.differential_definition',
                                 'Round3.ElementaryContracts.differential_source_unique',
                                 'Round3.ElementaryContracts.differential_parity',
                                 'Round3.ElementaryContracts.differential_mod_three',
                                 'Round3.ElementaryContracts.differential_divisible_by_three',
                                 'Round3.ElementaryContracts.mahler_existence',
                                 'Round3.ElementaryContracts.mahler_definition',
                                 'Round3.ElementaryContracts.mahler_source_unique',
                                 'Round3.ElementaryContracts.mahler_mod_four',
                                 'Round3.ElementaryContracts.mahler_residue',
                                 'Round3.ElementaryContracts.mahler_four_dvd_iff'],
 'round3_mod_four_transfer': ['Round3.ModFour.double_eq_iff',
                              'Round3.ModFour.series_double_eq_iff',
                              'Round3.ModFour.reduce_int_map',
                              'Round3.ModFour.two_mul_half'],
 'round3_a389537': ['Round3.LacunaryInverse.auxiliary_existence_uniqueness',
                    'Round3.LacunaryInverse.R_normalized',
                    'Round3.LacunaryInverse.R_equation',
                    'Round3.LacunaryInverse.A_normalized',
                    'Round3.LacunaryInverse.R_A',
                    'Round3.LacunaryInverse.A_R',
                    'Round3.LacunaryInverse.map_R',
                    'Round3.LacunaryInverse.map_A',
                    'Round3.LacunaryInverse.A_equation',
                    'Round3.LacunaryInverse.inverse_source',
                    'Round3.LacunaryInverse.A_unique',
                    'Round3.LacunaryInverse.source_existence_uniqueness',
                    'Round3.LacunaryInverse.A_mod_two',
                    'Round3.LacunaryInverse.H_constantCoeff',
                    'Round3.LacunaryInverse.A_decomposition',
                    'Round3.LacunaryInverse.A_mod_four_decomposition',
                    'Round3.LacunaryInverse.H_mod_two_equation',
                    'Round3.LacunaryInverse.H_mod_two',
                    'Round3.LacunaryInverse.H_mod_two_coeff',
                    'Round3.LacunaryInverse.a389537_residue'],
 'round3_a389542': ['Round3.SquareReversion.L_existence_uniqueness',
                    'Round3.SquareReversion.L_normalized',
                    'Round3.SquareReversion.L_equation',
                    'Round3.SquareReversion.R_normalized',
                    'Round3.SquareReversion.R_equation',
                    'Round3.SquareReversion.A389542_normalized',
                    'Round3.SquareReversion.compose_R_A',
                    'Round3.SquareReversion.compose_A_R',
                    'Round3.SquareReversion.source_of_inverse',
                    'Round3.SquareReversion.inverse_of_source',
                    'Round3.SquareReversion.a389542_equation',
                    'Round3.SquareReversion.inverse_equation_unique',
                    'Round3.SquareReversion.a389542_unique',
                    'Round3.SquareReversion.a389542_existence_uniqueness',
                    'Round3.SquareReversion.map_L',
                    'Round3.SquareReversion.map_R',
                    'Round3.SquareReversion.map_A389542',
                    'Round3.SquareReversion.L_quadratic_mod_two',
                    'Round3.SquareReversion.L_coeff_one_iff',
                    'Round3.SquareReversion.R_involution_mod_four',
                    'Round3.SquareReversion.A_eq_R_mod_four',
                    'Round3.SquareReversion.a389542_series_mod_four',
                    'Round3.SquareReversion.a389542_coeff_mod_four',
                    'Round3.SquareReversion.a389542_residue',
                    'Round3.SquareReversion.a389542_two_mod_four_iff',
                    'Round3.SquareReversion.a389542_four_dvd_iff'],
 'theta_substitution_source_and_congruences': ['ThetaSubstitution.theta_constant',
                                               'ThetaSubstitution.theta_coefficient',
                                               'ThetaSubstitution.a378580_constant',
                                               'ThetaSubstitution.a378581_constant',
                                               'ThetaSubstitution.a378580_quotient_identity',
                                               'ThetaSubstitution.a378580_source_equation',
                                               'ThetaSubstitution.a378581_source_equation',
                                               'ThetaSubstitution.a378580_source_uniqueness',
                                               'ThetaSubstitution.a378581_source_uniqueness',
                                               'ThetaSubstitution.a378580_source_existence_uniqueness',
                                               'ThetaSubstitution.a378581_source_existence_uniqueness',
                                               'ThetaSubstitution.a378580_series_mod_four',
                                               'ThetaSubstitution.a378581_series_mod_four',
                                               'ThetaSubstitution.a378580_congruence',
                                               'ThetaSubstitution.a378581_congruence',
                                               'ThetaSubstitution.a378580_square_iff',
                                               'ThetaSubstitution.a378581_square_iff',
                                               'ThetaSubstitution.a378580_four_dvd_iff',
                                               'ThetaSubstitution.a378581_four_dvd_iff']})
# Version-four reviewed additions are fixed independently of the JSON manifest.
ENDPOINT_GROUPS.update({'round4_nested_reversion': ['Round4.NestedReversion.family_existence_uniqueness',
                             'Round4.NestedReversion.source_existence_uniqueness',
                             'Round4.NestedReversion.tail_normalized',
                             'Round4.NestedReversion.tail_equation',
                             'Round4.NestedReversion.tail_right_inverse',
                             'Round4.NestedReversion.tail_left_inverse',
                             'Round4.NestedReversion.tail_is_inverse',
                             'Round4.NestedReversion.approximation_normalized',
                             'Round4.NestedReversion.approximation_succ',
                             'Round4.NestedReversion.approximation_agrees',
                             'Round4.NestedReversion.map_tail',
                             'Round4.NestedReversion.tail_of_zero_weight',
                             'Round4.NestedReversion.tail_quadratic_of_next_zero',
                             'Round4.NestedReversion.A_normalized',
                             'Round4.NestedReversion.A_source',
                             'Round4.NestedReversion.A_source_left',
                             'Round4.NestedReversion.A_mod_two_quadratic',
                             'Round4.NestedReversion.a195194_parity'],
 'generic_square_composition': ['Round4.SquareComposition.existence_uniqueness',
                                'Round4.SquareComposition.map_solution'],
 'a393172': ['Round4.CatalanComposition.a393172_existence_uniqueness',
             'Round4.CatalanComposition.A_normalized',
             'Round4.CatalanComposition.A_equation',
             'Round4.CatalanComposition.A_unique',
             'Round4.CatalanComposition.map_A',
             'Round4.CatalanComposition.A_mod_four',
             'Round4.CatalanComposition.a393172_residue',
             'Round4.CatalanComposition.a393172_four_dvd_iff'],
 'a393171': ['Round4.CatalanComposition.a393171_existence_uniqueness',
             'Round4.CatalanComposition.a393171_named_existence_uniqueness',
             'Round4.CatalanComposition.B_normalized',
             'Round4.CatalanComposition.B_equation',
             'Round4.CatalanComposition.B_fixed',
             'Round4.CatalanComposition.B_composed_catalan',
             'Round4.CatalanComposition.B_unique',
             'Round4.CatalanComposition.map_B',
             'Round4.CatalanComposition.A_integer_decomposition',
             'Round4.CatalanComposition.B_mod_eight',
             'Round4.CatalanComposition.a393171_residue',
             'Round4.CatalanComposition.a393171_eight_dvd_iff'],
 'a392210_elementary': ['Round4.NestedBinomial.existence_uniqueness',
                        'Round4.NestedBinomial.A_equation',
                        'Round4.NestedBinomial.rational_argument',
                        'Round4.NestedBinomial.a392210_odd_indices'],
 'explicit_source_contracts': ['Round4.CatalanContracts.first_existence',
                               'Round4.CatalanContracts.first_definition',
                               'Round4.CatalanContracts.first_residue',
                               'Round4.CatalanContracts.first_arbitrary_source',
                               'Round4.CatalanContracts.second_existence',
                               'Round4.CatalanContracts.second_named_existence',
                               'Round4.CatalanContracts.second_definition',
                               'Round4.CatalanContracts.second_residue',
                               'Round4.CatalanContracts.second_arbitrary_source',
                               'Round4.CatalanContracts.third_existence',
                               'Round4.CatalanContracts.third_definition',
                               'Round4.CatalanContracts.third_evenness',
                               'Round4.CatalanContracts.third_arbitrary_source'],
 'a380056_source_and_modular_results': ['Round4.ExpCosine.a_conv',
                                        'Round4.ExpCosine.a_convolution_unique',
                                        'Round4.ExpCosine.cosine_egf_eq',
                                        'Round4.ExpCosine.A_coeff',
                                        'Round4.ExpCosine.A_integral_coefficients',
                                        'Round4.ExpCosine.a380056_source_equation',
                                        'Round4.ExpCosine.a380056_source_quotient',
                                        'Round4.ExpCosine.a380056_source_unique',
                                        'Round4.ExpCosine.a380056_source_existence_uniqueness',
                                        'Round4.ExpCosine.a380056_mod_four',
                                        'Round4.ExpCosine.a380056_mod_five_formula',
                                        'Round4.ExpCosine.a380056_mod_five_period',
                                        'Round4.ExpCosine.a380056_mod_five_four_mul',
                                        'Round4.ExpCosine.a380056_five_dvd',
                                        'Round4.ExpCosine.a380056_mod_five_residue',
                                        'Round4.ExpCosine.a380056_five_dvd_iff'],
 'exp_cosine_source_contracts': ['Round4.ExpCosineContracts.integer_egf_definition',
                                 'Round4.ExpCosineContracts.source_egf',
                                 'Round4.ExpCosineContracts.literal_source_equation',
                                 'Round4.ExpCosineContracts.literal_source_unique',
                                 'Round4.ExpCosineContracts.integer_coefficients',
                                 'Round4.ExpCosineContracts.first_source_conjecture',
                                 'Round4.ExpCosineContracts.second_source_conjecture',
                                 'Round4.ExpCosineContracts.exact_mod_five_pattern',
                                 'Round4.ExpCosineContracts.exact_divisibility_by_five'],
 'round4_theta_rational_source_and_results': ['Round4.ThetaRational.ratio_quotient',
                                              'Round4.ThetaRational.sigma_coeff_finsum',
                                              'Round4.ThetaRational.existence_uniqueness',
                                              'Round4.ThetaRational.map_solution',
                                              'Round4.ThetaRational.solution_mod_four',
                                              'Round4.ThetaRational.a380060_source_equation',
                                              'Round4.ThetaRational.a380060_existence_uniqueness',
                                              'Round4.ThetaRational.a380060_source_uniqueness',
                                              'Round4.ThetaRational.a380060_coefficient_formula',
                                              'Round4.ThetaRational.a380060_series_mod_four',
                                              'Round4.ThetaRational.a380060_congruence',
                                              'Round4.ThetaRational.a380060_square_iff',
                                              'Round4.ThetaRational.a380060_four_dvd_iff',
                                              'Round4.ThetaRational.a380680_source_formula',
                                              'Round4.ThetaRational.a380680_coefficient_formula',
                                              'Round4.ThetaRational.a380680_series_mod_four',
                                              'Round4.ThetaRational.a380680_corrected_congruence',
                                              'Round4.ThetaRational.a380680_twice_square_iff',
                                              'Round4.ThetaRational.a380680_four_dvd_iff',
                                              'Round4.ThetaRational.a380680_coeff_one',
                                              'Round4.ThetaRational.a380680_coeff_two',
                                              'Round4.ThetaRational.a380680_literal_conjecture_false',
                                              'Round4.ThetaRational.a380680_nonsquare_clause_false'],
 'round4_theta_rational_contracts': ['Round4.ThetaRationalContracts.implicit_source_exists_unique',
                                     'Round4.ThetaRationalContracts.implicit_actual_source',
                                     'Round4.ThetaRationalContracts.explicit_actual_source',
                                     'Round4.ThetaRationalContracts.a380060_statement',
                                     'Round4.ThetaRationalContracts.a380680_corrected_statement',
                                     'Round4.ThetaRationalContracts.a380680_counterexamples',
                                     'Round4.ThetaRationalContracts.a380680_literal_statement_is_false',
                                     'Round4.ThetaRationalContracts.a380680_complement_is_false']})
FINAL_NAMES = [name for group in ENDPOINT_GROUPS.values() for name in group]
DIAGNOSTIC = re.compile(r"\b(?:warning|error):", re.IGNORECASE)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def validate_manifest(manifest):
    """Reject weakened or substituted requirements before invoking Lean."""
    names = required_theorems(manifest)
    if manifest.get("mode") != "complete":
        raise AuditError("Only the complete reviewed requirement set is accepted.")
    if names != FINAL_NAMES:
        raise AuditError(f"The manifest must retain all {len(FINAL_NAMES)} fixed endpoints in order.")
    if manifest.get("imports") != EXPECTED_IMPORTS:
        raise AuditError("The fixed imports for the complete proof package must be retained.")
    if manifest.get("contract_check_file") != "ContractChecks.lean":
        raise AuditError("The fixed ContractChecks.lean file is required.")
    if manifest.get("expected_toolchain") != EXPECTED_TOOLCHAIN:
        raise AuditError("The requirement set must retain the reviewed Lean version.")
    if manifest.get("expected_mathlib_revision") != EXPECTED_MATHLIB_REV:
        raise AuditError("The requirement set must retain the reviewed Mathlib revision.")
    if manifest.get("package_name") != EXPECTED_PACKAGE:
        raise AuditError("The package name must remain congruence_proofs.")
    return names


def validate_pins(project):
    pinned = (project / "lean-toolchain").read_text().strip()
    if pinned != EXPECTED_TOOLCHAIN:
        raise AuditError("lean-toolchain differs from the reviewed release.")
    config = tomllib.loads((project / "lakefile.toml").read_text())
    if config.get("name") != EXPECTED_PACKAGE:
        raise AuditError("lakefile.toml has an unexpected package name.")
    if config.get("defaultTargets") != ["Hanna", "Consecutive", "Related", "More", "Round3", "Round4"]:
        raise AuditError("Every reviewed proof library must remain a default build target.")
    requirements = [p for p in config.get("require", []) if p.get("name") == "mathlib"]
    if len(requirements) != 1 or requirements[0].get("rev") != EXPECTED_MATHLIB_REV or \
            requirements[0].get("git") != EXPECTED_MATHLIB_URL:
        raise AuditError("lakefile.toml does not pin the reviewed Mathlib source.")
    lock = json.loads((project / "lake-manifest.json").read_text())
    if lock.get("name") != EXPECTED_PACKAGE:
        raise AuditError("The Lake lockfile package name does not match the project.")
    packages = [p for p in lock.get("packages", []) if p.get("name") == "mathlib"]
    if len(packages) != 1 or any(packages[0].get(key) != value for key, value in {
        "rev": EXPECTED_MATHLIB_REV, "inputRev": EXPECTED_MATHLIB_REV,
        "url": EXPECTED_MATHLIB_URL, "type": "git",
    }.items()):
        raise AuditError("lake-manifest.json does not lock the reviewed Mathlib commit.")
    return pinned


def source_snapshot(repo, output):
    """Hash all first-party files, including root documents and final PDFs.

    Dependency/build caches and generated validation evidence are excluded.
    A first-party symlink is rejected rather than silently hashing another tree.
    """
    excluded = {".lake", ".git", "__pycache__", "reproducibility"}
    included = {}
    for path in repo.rglob("*"):
        relative = path.relative_to(repo)
        if any(part in excluded for part in relative.parts):
            continue
        if path.name == "SHA256SUMS" or (path.suffix == ".zip" and str(relative) not in RETAINED_ARCHIVES):
            continue  # Generated release output, not first-party source.
        if path.is_symlink():
            raise AuditError(f"First-party source must not be a symlink: {relative}")
        if path.resolve().is_relative_to(output):
            continue
        if path.is_file():
            included[str(relative)] = digest(path)
    return dict(sorted(included.items()))


def validate_baseline(repo, archive_name=BASELINE_ARCHIVE, expected_sha256=BASELINE_SHA256):
    """Retain the entire previous release and every original Lean proof unchanged."""
    archive = repo / archive_name
    if digest(archive) != expected_sha256:
        raise AuditError("The embedded previous release does not match its delivered SHA-256.")
    checked = []
    with zipfile.ZipFile(archive) as old:
        if old.testzip() is not None:
            raise AuditError("The embedded previous archive has a CRC failure.")
        prefix = "oeis-congruence-proofs/"
        manifest = json.loads(old.read(prefix + "validation/final_theorems.json"))
        previous_names = required_theorems(manifest)
        if FINAL_NAMES[:len(previous_names)] != previous_names:
            raise AuditError("The expanded release must retain every previous endpoint in order.")
        for name in old.namelist():
            if not name.startswith(prefix + "lean/") or not name.endswith(".lean"):
                continue
            rel = name[len(prefix):]
            if rel == "lean/ContractChecks.lean":
                # The previous typed contracts must be preserved as a literal suffix
                # after the added imports; new contracts live in separate library modules.
                current = (repo / rel).read_text()
                previous = old.read(name).decode()
                if previous not in current:
                    raise AuditError("Previous typed contracts were changed or removed.")
            elif (repo / rel).read_bytes() != old.read(name):
                raise AuditError(f"Previous formal proof source was changed: {rel}")
            checked.append(rel)
    return {
        "archive": archive_name, "sha256": expected_sha256,
        "previous_endpoint_count": len(previous_names),
        "retained_lean_sources": checked,
        "original_zip_preserved_verbatim": True,
    }


def first_party_compile_order(project):
    """Return every local module in dependency order, apart from the final contract.

    This project uses ordinary one-line Lean import declarations. External
    dependency modules retain their pinned cached objects; every first-party
    module is explicitly re-elaborated even if the environment restored a build artifact.
    """
    modules = {}
    for path in project.rglob("*.lean"):
        relative = path.relative_to(project)
        if ".lake" in relative.parts or relative.as_posix() == "ContractChecks.lean":
            continue
        if path.is_symlink():
            raise AuditError(f"First-party module must not be a symlink: {relative}")
        modules[".".join(relative.with_suffix("").parts)] = path
    result, active, done = [], set(), set()

    def visit(name):
        if name in done:
            return
        if name in active:
            raise AuditError(f"Cyclic first-party module imports: {name}")
        active.add(name)
        for line in modules[name].read_text().splitlines():
            match = re.match(r"^\s*import\s+(.+?)(?:\s*--.*)?$", line)
            if match:
                for dependency in match.group(1).split():
                    if dependency in modules:
                        visit(dependency)
        active.remove(name)
        done.add(name)
        result.append((name, modules[name]))

    for name in sorted(modules):
        visit(name)
    if not result:
        raise AuditError("No first-party Lean modules found for forced re-elaboration.")
    return result


def remove_project_build_cache(project):
    """Delete only this project's build artifacts, never dependency caches.

    Lake's package-qualified clean command can retain library objects.  Removing
    this exact directory also removes their trace files and forces every local
    proof module to be elaborated again.  Refuse symlinked cache paths rather
    than risking a directory outside this project.
    """
    project = project.resolve()
    lake_dir = project / ".lake"
    build = lake_dir / "build"
    if not (project / "lakefile.toml").is_file():
        raise AuditError("Cannot clean a directory without the project lakefile.toml.")
    if lake_dir.is_symlink() or build.is_symlink():
        raise AuditError("Refusing to delete a symlinked project build-cache path.")
    if build.resolve() != project / ".lake" / "build":
        raise AuditError("The project build-cache path resolves outside its expected location.")
    existed = build.exists()
    if existed and not build.is_dir():
        raise AuditError("The project build-cache path is not a directory.")
    removed_oleans = sum(1 for path in build.rglob("*.olean") if path.is_file()) if existed else 0
    if existed:
        shutil.rmtree(build)
    if build.exists() or build.is_symlink():
        raise AuditError("Project build artifacts remain after the required fresh-build cleanup.")
    return {
        "path": "lean/.lake/build",
        "directory_existed": existed,
        "removed_olean_count": removed_oleans,
        "directory_absent_before_build": True,
        "dependency_cache_path_preserved": "lean/.lake/packages",
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--mode", choices=["complete"], default="complete")
    parser.add_argument("--repo", type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument("--lake", default="lake", help="Lake executable or absolute path")
    parser.add_argument("--output", type=Path, help="Directory for fresh validation evidence")
    args = parser.parse_args()
    repo = args.repo.resolve()
    project = repo / "lean"
    output = (args.output or repo / "reproducibility" / "lean_complete").resolve()
    if output == repo or output == project or output in repo.parents:
        raise SystemExit("The evidence directory must not contain the source tree.")
    output.mkdir(parents=True, exist_ok=True)
    report = {
        "mode": "complete", "status": "failed", "commands": [],
        "scope": "Clean build and forced re-elaboration of every first-party source, typed contracts, full types, transitive axiom checks, and independent finite corroboration.",
        "semantic_review": "Required: inspect definitions and typed contracts against the manuscripts.",
    }

    def run(command, name, env, cwd=project):
        start = time.monotonic()
        completed = subprocess.run(command, cwd=cwd, env=env, text=True,
                                   stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        log = output / name
        log.parent.mkdir(parents=True, exist_ok=True)
        log.write_text(completed.stdout)
        report["commands"].append({
            "command": command, "working_directory": str(cwd.relative_to(repo)),
            "exit_code": completed.returncode,
            "elapsed_seconds": round(time.monotonic() - start, 3),
            "log": name, "log_sha256": digest(log),
        })
        if completed.returncode:
            raise AuditError(f"Command failed; see {log}.")
        if DIAGNOSTIC.search(completed.stdout):
            raise AuditError(f"Warning/error output is not accepted; see {log}.")
        return completed.stdout

    try:
        manifest_path = repo / "validation" / "final_theorems.json"
        manifest = json.loads(manifest_path.read_text())
        names = validate_manifest(manifest)
        report["required_theorems"] = names
        report["endpoint_count"] = len(names)
        report["requirements_sha256"] = digest(manifest_path)
        contract = project / "ContractChecks.lean"
        if not contract.is_file() or not contract.read_text().strip():
            raise AuditError("lean/ContractChecks.lean is missing or empty.")
        report["pinned_toolchain"] = validate_pins(project)
        report["previous_release_preservation"] = validate_baseline(repo)
        report["previous_v2_release_preservation"] = validate_baseline(
            repo, PREVIOUS_V2_ARCHIVE, PREVIOUS_V2_SHA256)
        report["previous_v3_release_preservation"] = validate_baseline(
            repo, PREVIOUS_V3_ARCHIVE, PREVIOUS_V3_SHA256)
        report["pinned_mathlib_revision"] = EXPECTED_MATHLIB_REV
        lake = shutil.which(args.lake)
        if lake is None:
            raise AuditError("Lake is unavailable; install the pinned toolchain or pass --lake.")
        lake = str(Path(lake).absolute())  # retain an Elan shim's invocation name
        env = os.environ.copy()
        env["PATH"] = str(Path(lake).parent) + os.pathsep + env.get("PATH", "")
        env["PYTHONDONTWRITEBYTECODE"] = "1"
        report["sources_before"] = source_snapshot(repo, output)
        version = run([lake, "env", "lean", "--version"], "toolchain.log", env)
        if not re.search(r"\bversion 4\.19\.0(?:\s|,|\))", version):
            raise AuditError("The executing Lean version does not match the pinned release.")
        mathlib = project / ".lake" / "packages" / "mathlib"
        revision = run(["git", "-C", str(mathlib), "rev-parse", "HEAD"], "mathlib_revision.log", env)
        if revision.strip() != EXPECTED_MATHLIB_REV:
            raise AuditError("The installed Mathlib checkout is not at the pinned commit.")
        dirty = run(["git", "-C", str(mathlib), "status", "--porcelain", "--untracked-files=no"],
                    "mathlib_status.log", env)
        if dirty.strip():
            raise AuditError("Tracked Mathlib files have local changes.")
        run([sys.executable, "-m", "unittest", "discover", "-s", "tests", "-v"],
            "checker_tests.log", env, cwd=repo)
        numerical = [
            ("scripts/verify_coefficients.py", ["--terms", "40"], "coefficients_40.json"),
            ("scripts/verify_rational_parity.py", [], "rational_parity_numeric.json"),
            ("scripts/verify_cubic_reversion.py", ["--degree", "40"], "cubic_reversion_numeric.json"),
            ("tests/check_inverse_iterate.py", ["--degree", "40"], "inverse_iterate_checks.json"),
            ("scripts/verify_stirling_periodicity.py", ["--max-modulus", "128"], "stirling_numeric.json"),
            ("scripts/verify_differential_mahler.py", [], "differential_mahler_numeric.json"),
            ("scripts/verify_lacunary_inverse.py", ["--degree", "80"], "lacunary_inverse_numeric.json"),
            ("scripts/verify_square_reversion.py", ["--degree", "80"], "square_reversion_numeric.json"),
            ("scripts/verify_theta_substitution.py", [], "theta_substitution_numeric.json"),
            ("scripts/verify_nested_reversion.py", [], "nested_reversion_numeric.json"),
            ("scripts/verify_catalan_composition.py", [], "catalan_composition_numeric.json"),
            ("scripts/verify_exp_cosine.py", [], "exp_cosine_numeric.json"),
            ("scripts/verify_theta_rational.py", [], "theta_rational_numeric.json"),
        ]
        report["numeric_evidence"] = {}
        for script, options, filename in numerical:
            destination = output / filename
            run([sys.executable, script, *options, "--output", str(destination)],
                Path(filename).stem + ".log", env, cwd=repo)
            report["numeric_evidence"][filename] = digest(destination)
        # Clean ONLY this package; preserve the pinned dependency build caches.
        run([lake, "clean", EXPECTED_PACKAGE], "clean.log", env)
        report["project_build_cache_cleanup"] = remove_project_build_cache(project)
        cleanup_log = output / "project_cache_cleanup.json"
        cleanup_log.write_text(json.dumps(report["project_build_cache_cleanup"], indent=2) + "\n")
        report["project_build_cache_cleanup_sha256"] = digest(cleanup_log)
        run([lake, "build"], "build.log", env)
        # Capture Lake's external dependency path once, then compile directly
        # with a fresh isolated project-object directory FIRST. Exclude the old
        # project build path entirely, so restored objects cannot satisfy local
        # imports. Lean's command-line frontend elaborates each supplied source.
        env_probe = run([lake, "env", sys.executable, "-c",
                         "import json,os,shutil; print(json.dumps({'lean':shutil.which('lean'),"
                         "'LEAN_PATH':os.environ.get('LEAN_PATH','')}))"],
                        "compiler_environment.log", env)
        compiler_info = json.loads(env_probe)
        lean = compiler_info.get("lean")
        if not lean or not Path(lean).is_file():
            raise AuditError("Could not resolve the exact Lean compiler for isolated re-elaboration.")
        fresh_objects = Path(tempfile.mkdtemp(prefix="oeis-lean-recheck-"))
        old_objects = (project / ".lake/build/lib/lean").resolve()
        external_paths = []
        for entry in compiler_info["LEAN_PATH"].split(os.pathsep):
            if not entry:
                continue
            path = Path(entry)
            resolved = (path if path.is_absolute() else project / path).resolve()
            if resolved != old_objects:
                external_paths.append(str(resolved))
        fresh_env = env.copy()
        fresh_env["LEAN_PATH"] = os.pathsep.join([str(fresh_objects), *external_paths])
        report["isolated_compiler"] = {
            "executable": lean, "fresh_project_object_directory": str(fresh_objects),
            "fresh_directory_initially_empty": not any(fresh_objects.iterdir()),
            "old_project_object_directory_excluded": str(old_objects),
            "effective_lean_path": fresh_env["LEAN_PATH"],
        }
        report["forced_source_reelaboration"] = []
        for module, source in first_party_compile_order(project):
            relative = source.relative_to(project)
            object_file = fresh_objects / relative.with_suffix(".olean")
            if object_file.exists() or object_file.is_symlink():
                raise AuditError(f"Isolated proof object already exists before compiling {module}.")
            object_file.parent.mkdir(parents=True, exist_ok=True)
            started_ns = time.time_ns()
            run([lean, "-R", str(project), "-o", str(object_file), relative.as_posix()],
                "forced_source/" + module + ".log", fresh_env)
            if not object_file.is_file() or object_file.is_symlink():
                raise AuditError(f"Explicit Lean invocation did not create {module}'s object.")
            if object_file.stat().st_mtime_ns < started_ns:
                raise AuditError(f"Explicit Lean invocation reused an old object for {module}.")
            report["forced_source_reelaboration"].append({
                "module": module, "source": relative.as_posix(),
                "source_sha256": digest(source), "object_sha256": digest(object_file),
                "new_object_created": True,
            })
        report["forced_source_module_count"] = len(report["forced_source_reelaboration"])
        run([lean, "-R", str(project), "-o", str(output / "ContractChecks.olean"),
             "ContractChecks.lean"], "contracts.log", fresh_env)
        report["contract_compiled"] = True
        report["contract_object_sha256"] = digest(output / "ContractChecks.olean")
        prefix = "\n".join("import " + module for module in EXPECTED_IMPORTS) + "\n\n"
        types_file = output / "GeneratedTypes.lean"
        types_file.write_text(prefix + "set_option pp.all true\n\n" +
                              "\n".join("#check " + name for name in names) + "\n")
        run([lean, str(types_file)], "types.log", fresh_env)
        audit_file = output / "GeneratedAxiomAudit.lean"
        audit_file.write_text(prefix + "\n".join("#print axioms " + name for name in names) + "\n")
        text = run([lean, str(audit_file)], "axioms.log", fresh_env)
        report["axiom_dependencies"] = audit_text(text, names)
        report["generated_types_sha256"] = digest(types_file)
        report["generated_axiom_audit_sha256"] = digest(audit_file)
        report["sources_after"] = source_snapshot(repo, output)
        if report["sources_before"] != report["sources_after"]:
            raise AuditError("First-party sources changed during validation; rerun on a stable tree.")
        validate_pins(project)
        report["status"] = "mechanical_checks_passed"
    except (OSError, ValueError, subprocess.SubprocessError) as error:
        report["failure"] = str(error)
    report["completed_utc"] = datetime.now(timezone.utc).isoformat(timespec="seconds")
    (output / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({key: report[key] for key in ("mode", "status", "scope")}, indent=2))
    print(f"Evidence directory: {output}")
    if "failure" in report:
        print(report["failure"], file=sys.stderr)
    return 0 if report["status"] == "mechanical_checks_passed" else 1


if __name__ == "__main__":
    raise SystemExit(main())
