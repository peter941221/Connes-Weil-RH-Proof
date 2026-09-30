"""2294 controls: algebraic error propagation and corrected-owner cell guards."""
from fractions import Fraction
from decimal import Decimal
import json
from pathlib import Path
import unittest

import mpmath as mp

import routea_uniform_radius_functional_floor_2294 as instrument


class UniformRadiusFloorControls(unittest.TestCase):
    def setUp(self):
        mp.mp.dps = mp.iv.dps = 80

    def test_exact_product_majorant_expansion(self):
        for base in (Fraction(0), Fraction(1, 3), Fraction(3)):
            for corr in (Fraction(0), Fraction(2, 5), Fraction(4)):
                for base_radius, corr_radius in ((Fraction(0), Fraction(0)),
                                                  (Fraction(1, 2), Fraction(2, 3))):
                    price = instrument.squared_product_error_majorant(base, corr, base_radius, corr_radius)
                    expected = (base + base_radius)**2*(corr + corr_radius)**2-base**2*corr**2
                    self.assertEqual(price, expected)
                    self.assertGreaterEqual(price, base_radius**2*corr_radius**2)

    def test_complex_perturbations_are_bounded(self):
        base = mp.mpc(3, 4)
        corr = mp.mpc(-4, 3)
        base_radius = mp.mpf("0.25")
        corr_radius = mp.mpf("0.4")
        bound = instrument.squared_product_error_majorant(abs(base), abs(corr), base_radius, corr_radius)
        for angle in (0, mp.pi/3, mp.pi, -mp.pi/2):
            delta_base = base_radius*mp.exp(1j*angle)
            delta_corr = corr_radius*mp.exp(-2j*angle)
            movement = abs(abs(base + delta_base)**2*abs(corr + delta_corr)**2
                           -abs(base)**2*abs(corr)**2)
            self.assertLessEqual(movement, bound)

    def test_independent_aligned_errors_attain_majorant(self):
        base = mp.mpc(3, 4)
        corr = mp.mpc(-4, 3)
        delta_base = mp.mpf("0.25")*base/abs(base)
        delta_corr = mp.mpf("0.4")*corr/abs(corr)
        movement = abs(base + delta_base)**2*abs(corr + delta_corr)**2-abs(base)**2*abs(corr)**2
        bound = instrument.squared_product_error_majorant(abs(base), abs(corr), mp.mpf("0.25"), mp.mpf("0.4"))
        self.assertLess(abs(movement-bound), mp.mpf("1e-70"))

    def test_negative_radius_is_rejected(self):
        with self.assertRaises(ValueError):
            instrument.squared_product_error_majorant(1, 1, -1, 1)

    def test_exported_endpoints_are_outward_rounded(self):
        box = mp.iv.mpf(1)/3
        encoded = instrument.interval_text(box)
        for key, raw, lower in (("lower", box._mpi_[0], True), ("upper", box._mpi_[1], False)):
            sign, mantissa, exponent, _ = raw
            exact = Fraction((-1 if sign else 1)*mantissa)*Fraction(2)**exponent
            written = Fraction(Decimal(encoded[key]))
            if lower:
                self.assertLessEqual(written, exact)
            else:
                self.assertGreaterEqual(written, exact)

    def test_exact_prime_power_labels(self):
        self.assertEqual(instrument.enumerate_prime_powers(10),
                         [(2, 2), (3, 3), (4, 2), (5, 5), (7, 7), (8, 2), (9, 3)])
        self.assertEqual(instrument.enumerate_prime_powers(1), [])

    def test_complete_book_matches_independent_owner_enumerator(self):
        artifact = json.loads(instrument.OUT.read_text(encoding="utf-8"))
        cutoff = artifact["weight_cell"]["cutoff"]
        primary = instrument.enumerate_prime_powers(cutoff)
        independent = instrument.owner.owner_source.rig.prime_powers_up_to(cutoff)
        self.assertEqual([number for number, _ in primary], [number for number, _ in independent])
        self.assertEqual(len(primary), 41136)

    def test_sigma_origin_cell_positivity_reference(self):
        eta = mp.mpf("0.00001")
        self.assertLess((mp.pi*eta)**2, mp.mpf(3)/16)
        for xi in (-eta, 0, eta):
            sigma = mp.log(mp.pi) - mp.re(mp.digamma(mp.mpc(mp.mpf(1)/4, -mp.pi*xi)))
            self.assertGreater(sigma, 0)

    def test_four_factor_modulus_lower_bound_both_signs(self):
        gamma = mp.mpf(instrument.owner.owner_source.GAMMA)
        delta = mp.mpf(instrument.owner.owner_source.DELTA)
        eta = mp.mpf("0.00001")
        floor = (gamma - 2*mp.pi*eta)**8
        for xi in (-eta, 0, eta):
            product = mp.mpc(1)
            for real in (-delta, delta):
                for imaginary in (-gamma, gamma):
                    product *= mp.mpc(real, imaginary + 2*mp.pi*xi)
            self.assertGreaterEqual(abs(product)**2, floor)

    def test_artifact_scope_and_all_partition_prices(self):
        artifact = json.loads(instrument.OUT.read_text(encoding="utf-8"))
        self.assertFalse(artifact["certificate"])
        self.assertFalse(artifact["hgap_closed"])
        self.assertEqual([row["subcells_per_panel"] for row in artifact["rows"]], [8, 16, 32])
        for row in artifact["rows"]:
            self.assertGreater(mp.mpf(row["budget_ratio_floor"]["lower"]), 1)
            self.assertTrue(row["method_over_budget"])
            ratio = mp.mpf(row["budget_ratio_floor"]["lower"])
            ceiling = mp.mpf(row["common_radius_scale_necessary_ceiling"]["upper"])
            self.assertLess(abs(ceiling*ratio**mp.mpf("0.25")-1), mp.mpf("1e-40"))


if __name__ == "__main__":
    unittest.main()
