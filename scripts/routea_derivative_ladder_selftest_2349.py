"""2349: exact-algebra, independent derivative and provenance controls."""
import copy
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import unittest

from flint import arb, ctx
import mpmath as mp

import routea_derivative_ladder_2349 as ladder

ROOT = Path(__file__).resolve().parents[1]


class DerivativeLadderTests(unittest.TestCase):
    def setUp(self):
        ctx.prec = 192
        self.parent = json.loads((ROOT / "results/2342_direct_ideal_strip.json").read_text())
        self.result = json.loads((ROOT / "results/2349_derivative_ladder.json").read_text())

    def test_exact_numerators_and_constants(self):
        expected = [{0: 1}, {1: -60}, {0: -60, 2: 3480, 4: 180},
                    {1: 10080, 3: -193680, 5: -31680, 7: -720},
                    {0: 10080, 2: -1085040, 4: 10189440,
                     6: 3575520, 8: 266400, 10: 3600}]
        self.assertEqual(ladder.get_numerators(), expected)
        self.assertEqual(ladder.get_constants(), [1, 60, 3720, 236160, 15130080])

    def test_two_variable_recurrence_clears_to_same_polynomials(self):
        for order, numerator in enumerate(ladder.get_two_variable_numerators()):
            self.assertEqual(ladder.clear_denominator(numerator, order),
                             ladder.get_numerators()[order])

    def test_derivatives_against_independent_mpmath(self):
        with mp.workdps(100):
            for coordinate in ("-0.9", "-0.5", "-0.1", "0", "0.1", "0.5", "0.9"):
                position = mp.mpf(coordinate)
                deficit = 1 - position**2
                for order, numerator in enumerate(ladder.get_numerators()):
                    candidate = mp.exp(-30 / deficit) * deficit**(-2 * order) * sum(
                        coefficient * position**power for power, coefficient in numerator.items())
                    reference = mp.diff(lambda point: mp.exp(-30 / (1 - point**2)),
                                        position, order)
                    scale = max(abs(candidate), mp.exp(-30))
                    self.assertLess(abs(candidate - reference), mp.mpf("1e-85") * scale)

    def test_envelope_controls_both_sides_and_all_orders(self):
        with mp.workdps(80):
            for index in range(-199, 200):
                position = mp.mpf(index) / 200
                deficit = 1 - position**2
                for order, numerator in enumerate(ladder.get_numerators()):
                    value = mp.exp(-30 / deficit) * deficit**(-2 * order) * sum(
                        coefficient * position**power for power, coefficient in numerator.items())
                    self.assertLessEqual(abs(value), ladder.get_constants()[order] * mp.exp(-30))

    def test_legacy_constants_are_not_invalidated_by_coarser_triangle(self):
        constants = ladder.get_constants()
        self.assertEqual(self.result["legacy_constants"], [1, 60, 3900, 245160, 23402880])
        self.assertTrue(all(new <= old for new, old in zip(constants, self.result["legacy_constants"])))
        coarse_third = sum(abs(value) for value in ladder.get_two_variable_numerators()[3].values())
        self.assertEqual(coarse_third, 272160)
        self.assertLess(constants[3], self.result["legacy_constants"][3])

    def test_ladder_rejects_incomplete_or_invalid_owner(self):
        with self.assertRaises(ValueError):
            ladder.get_ladder([(arb(1), arb(2))], [], [arb(1)])
        for radius in (arb(0), arb(-1), arb(0, 1)):
            with self.assertRaises(ValueError):
                ladder.get_ladder([(arb(1), arb(2))], [arb(1)], [radius])

    def test_parent_contract_rejects_endpoint_grid_and_scope_mutations(self):
        mutations = (("nodes", 120000), ("precision_bits", 256),
                     ("coordinates", "float uniform grid"), ("rh_claim", True),
                     ("coefficient_owner", "stored rather than ideal coefficients"))
        for key, value in mutations:
            altered = copy.deepcopy(self.parent)
            altered[key] = value
            with self.assertRaises(ValueError):
                ladder.validate_parent(altered)
        altered = copy.deepcopy(self.parent)
        altered["endpoints"].reverse()
        with self.assertRaises(ValueError):
            ladder.validate_parent(altered)

    def test_parent_contract_rejects_provenance_mutations(self):
        for key in ("input_sha256", "helper_sha256"):
            altered = copy.deepcopy(self.parent)
            name = next(iter(altered[key]))
            altered[key][name] = "0" * 64
            with self.assertRaises(ValueError):
                ladder.validate_parent(altered)

    def test_same_run_replay_is_identical(self):
        self.assertEqual(ladder.run(), self.result)
        self.assertTrue(self.result["same_run_old_panels_and_totals_exact"])

    def test_node_sums_unchanged_and_each_panel_improves_or_equals(self):
        for old_endpoint, endpoint in zip(self.parent["endpoints"], self.result["endpoints"]):
            for name in ("base", "correction"):
                for key in ("m0", "d2"):
                    old = old_endpoint["channels"][name]
                    new = endpoint["channels"][name]
                    self.assertEqual(new[key + "_point_upper"], old[key + "_point_upper"])
                    self.assertLess(Fraction(new[key + "_panel_upper"]["upper_exact"]),
                                    Fraction(old[key + "_panel_upper"]["upper_exact"]))
                    self.assertLess(Fraction(new[key]["upper_exact"]),
                                    Fraction(old[key]["upper_exact"]))

    def test_product_reconstructs_below_old_bound_and_pin(self):
        maxima = {name: {key: max(Fraction(endpoint["channels"][name][key]["upper_exact"])
                                 for endpoint in self.result["endpoints"])
                         for key in ("m0", "d2")} for name in ("base", "correction")}
        reconstructed = min(maxima["base"]["d2"] * maxima["correction"]["m0"],
                            maxima["correction"]["d2"] * maxima["base"]["m0"])
        self.assertEqual(reconstructed, Fraction(self.result["continuum_min_product_upper_exact"]))
        self.assertLess(reconstructed, Fraction(self.result["old_continuum_min_product_upper_exact"]))
        self.assertLess(reconstructed, Fraction(self.result["frozen_pin_exact"]))

    def test_source_hashes_and_scope_flags(self):
        self.assertEqual(self.result["source_sha256"], hashlib.sha256(Path(ladder.__file__).read_bytes()).hexdigest())
        self.assertEqual(self.result["parent_sha256"], hashlib.sha256(
            (ROOT / "results/2342_direct_ideal_strip.json").read_bytes()).hexdigest())
        for flag in ("node_sums_recomputed", "derivative_majorants_formalized_in_lean",
                     "lean_certificate_imported", "healthy_detector_instantiated",
                     "complete_signed_kernel_priced", "owner_transfer_to_live_consumer",
                     "producer_go", "rh_claim"):
            self.assertFalse(self.result[flag])


if __name__ == "__main__":
    unittest.main(verbosity=2)
