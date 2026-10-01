import unittest
from fractions import Fraction

import routea_producer_readback_2319 as readback


class ProducerReadbackTests(unittest.TestCase):
    def test_target_and_companion_are_exact_roots(self):
        for rho in ((Fraction(3, 4), Fraction(7)),
                    (Fraction(1, 2), Fraction(7)),
                    (Fraction(3, 4), Fraction(0))):
            with self.subTest(rho=rho):
                roots = readback.orbit_nodes(rho)
                for root in roots:
                    self.assertEqual(readback.polynomial_value(roots, root), readback.ZERO)
                    self.assertEqual(readback.squared_polynomial_value(roots, root), readback.ZERO)

    def test_shifted_roots_do_not_kill_old_target(self):
        roots = readback.orbit_nodes((Fraction(3, 4), Fraction(7)))
        shifted = tuple((root[0] + Fraction(1, 1024), root[1]) for root in roots)
        self.assertNotEqual(readback.polynomial_value(shifted, roots[0]), readback.ZERO)

    def test_fixed_cutoff_and_changing_owner_are_different(self):
        previous = Fraction(4)
        for cutoff in range(1, 17):
            current = 4 * Fraction(3, 4) ** cutoff
            self.assertEqual(current / previous, Fraction(3, 4))
            self.assertEqual(current * Fraction(4, 3) ** cutoff, 4)
            previous = current

    def test_artifact_prescription_is_not_float_solve_certification(self):
        report = readback.build_report()
        self.assertEqual(report["prescribed_pair_square_value"], ["-1", "0"])
        self.assertTrue(report["prescribed_values_are_not_a_certified_float_solve"])
        self.assertTrue(all(report["source_checks"].values()))
        for row in report["growth_controls"]:
            self.assertEqual(row["p_only_marked_gain"], "0")
            self.assertIsNone(row["tail_over_marked_gain"])


if __name__ == "__main__":
    unittest.main()
