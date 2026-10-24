"""Small exact checks of the verifier's arithmetic and independent recursions."""

import unittest

from scripts.verify_coefficients import compose, generate_q, generate_r, multiply, verify_all


class CoefficientVerifierTests(unittest.TestCase):
    def test_cauchy_product_and_truncation(self):
        self.assertEqual(multiply([1, 2, 3], [4, 5, 6], 3), [4, 13, 28, 27])

    def test_composition_orientation(self):
        # (X+2X^2) composed with (X+3X^2) is X+5X^2+12X^3+18X^4.
        self.assertEqual(compose([0, 1, 2], [0, 1, 3], 4), [0, 1, 5, 12, 18])
        self.assertEqual(compose([0, 1, 3], [0, 1, 2], 4), [0, 1, 5, 12, 12])

    def test_inner_constant_rejected(self):
        with self.assertRaises(ValueError):
            compose([0, 1, 2], [1, 1], 4)

    def test_r_recursion_matches_source_values(self):
        self.assertEqual(generate_r(2, 8)[1:], [1, 1, 5, 39, 383, 4357, 55057, 754223])
        self.assertEqual(generate_r(4, 4)[1:], [1, 1, 9, 133])

    def test_q_recursion_matches_source_values(self):
        self.assertEqual(generate_q(4, 8)[1:],
                         [1, 1, 6, 121, 8466, 2227706, 2299117036, 9437900978761])
        self.assertEqual(generate_q(7, 4)[1:], [1, 1, 9, 481])

    def test_complete_small_suite(self):
        report = verify_all(8, [1, 2, 4, 5], [4, 5, 6, 7])
        self.assertEqual(report["result"], "pass")
        self.assertGreater(report["coefficient_checks"], 500)
        self.assertFalse(report["construction"]["uses_residue_candidates_to_construct_coefficients"])

    def test_invalid_parameter_ranges(self):
        with self.assertRaises(ValueError):
            generate_r(0, 8)
        with self.assertRaises(ValueError):
            generate_q(-1, 8)
        with self.assertRaises(ValueError):
            verify_all(7, [2], [4])


if __name__ == "__main__":
    unittest.main()
