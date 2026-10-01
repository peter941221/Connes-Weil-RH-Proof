"""2342: controls for the independent exact-grid strip enclosure."""
import hashlib
import json
from fractions import Fraction
from pathlib import Path
import unittest

from flint import acb, arb, ctx
import mpmath as mp

import routea_direct_ideal_strip_2342 as direct

ROOT = Path(__file__).resolve().parents[1]


class DirectIdealStripTests(unittest.TestCase):
    def setUp(self):
        ctx.prec = 192
        self.result = json.loads((ROOT / "results/2342_direct_ideal_strip.json").read_text())

    def test_committed_result_is_independent_of_2303_point_rows(self):
        self.assertFalse(self.result["legacy_2303_point_sums_used"])
        self.assertEqual(self.result["coordinates"], "exact rational uniform grid")
        self.assertEqual(self.result["nodes"], 120001)
        self.assertTrue(self.result["fits_existing_pin"])

    def test_pin_margin_and_continuum_endpoint_scope(self):
        upper = Fraction(self.result["continuum_min_product_upper_exact"])
        pin = Fraction(self.result["frozen_pin_exact"])
        self.assertLess(upper, pin)
        self.assertEqual({row["sigma_exact"] for row in self.result["endpoints"]}, {"-1/2", "1/2"})
        maxima = {channel: {key: max(Fraction(row["channels"][channel][key]["upper_exact"])
                                    for row in self.result["endpoints"])
                           for key in ("m0", "d2")} for channel in ("base", "correction")}
        reconstructed = min(maxima["base"]["d2"] * maxima["correction"]["m0"],
                            maxima["correction"]["d2"] * maxima["base"]["m0"])
        self.assertEqual(upper, reconstructed)

    def test_input_and_helper_hashes_match(self):
        for name, digest in self.result["input_sha256"].items():
            self.assertEqual(digest, hashlib.sha256((ROOT / name).read_bytes()).hexdigest())
        for name, digest in self.result["helper_sha256"].items():
            self.assertEqual(digest, hashlib.sha256((ROOT / "scripts" / name).read_bytes()).hexdigest())
        self.assertEqual(self.result["source_sha256"],
                         hashlib.sha256((ROOT / "scripts/routea_direct_ideal_strip_2342.py").read_bytes()).hexdigest())

    def test_repair_owner_has_all_thirty_rows(self):
        repair = json.loads((ROOT / "results/2338_exact_interpolation_repair.json").read_text())
        self.assertEqual(len(repair["coefficient_rows"]), 30)
        self.assertEqual([row["index"] for row in repair["coefficient_rows"]], list(range(30)))
        self.assertLess(Fraction(repair["neumann_defect_infinity_upper"]["upper_exact"]), Fraction(1, 2))

    def test_endpoint_channels_are_finite_and_nonnegative(self):
        for endpoint in self.result["endpoints"]:
            for channels in endpoint["channels"].values():
                for key in ("m0", "d2", "m0_point_upper", "d2_point_upper",
                            "m0_panel_upper", "d2_panel_upper"):
                    self.assertGreaterEqual(Fraction(channels[key]["upper_exact"]), 0)

    def test_scope_flags_are_not_overclaimed(self):
        for key in ("zero_count_used", "legacy_2303_point_sums_used",
                    "lean_certificate_imported", "healthy_detector_instantiated",
                    "complete_signed_kernel_priced", "owner_transfer_to_live_consumer",
                    "producer_go", "rh_claim"):
            self.assertFalse(self.result[key])

    def test_invalid_node_parameters_are_rejected(self):
        with self.assertRaises(ValueError):
            direct.run(2, 192)
        with self.assertRaises(ValueError):
            direct.run(101, 64)

    def test_rectangle_decoder_rejects_inverted_bounds(self):
        with self.assertRaises(ValueError):
            direct.decode_real_rectangle({"lower_exact": "2", "upper_exact": "1"})

    def test_five_control_nodes_are_recorded(self):
        self.assertEqual(len(self.result["node_controls"]), 5)
        self.assertEqual(self.result["node_controls"][0]["index"], 0)
        self.assertEqual(self.result["node_controls"][-1]["index"], 120000)

    def test_decoded_rectangle_contains_exact_endpoints(self):
        for precision in (53, 192):
            ctx.prec = precision
            value = direct.decode_real_rectangle({"lower_exact": "1/7", "upper_exact": "2/7"})
            self.assertLessEqual(Fraction(str(value.lower().fmpq())), Fraction(1, 7))
            self.assertGreaterEqual(Fraction(str(value.upper().fmpq())), Fraction(2, 7))

    def test_support_boundary_and_outside_are_exactly_zero(self):
        families = [(arb(1), arb(7))]
        for coordinate in (Fraction(-2), Fraction(-1), Fraction(1), Fraction(2)):
            values = direct.evaluate_node(coordinate, families, [Fraction(1)], [arb(1)],
                                          [[acb(1)], [acb(2)]])
            self.assertTrue(all(value.is_zero() for value in values))

    def test_phase_and_radius_terms_in_center_second_derivative(self):
        values = direct.evaluate_node(Fraction(0), [(arb(1), arb(5))], [Fraction(2)], [arb(2)],
                                      [[acb(1)], [acb(2)]])
        bump = arb(-30).exp()
        self.assertTrue(values[0].real.overlaps(bump))
        self.assertTrue(values[1].real.overlaps(-40 * bump))
        self.assertTrue(values[3].real.overlaps(-80 * bump))

    def test_complex_sums_cancel_before_modulus(self):
        families = [(arb(1), arb(7)), (arb(1), arb(7))]
        values = direct.evaluate_node(Fraction(1, 3), families, [Fraction(1)] * 2, [arb(1)] * 2,
                                      [[acb(1, 2), acb(-1, -2)], [acb(3), acb(-3)]])
        for value in values:
            self.assertTrue(value.contains(0))
            self.assertLess(abs(value).upper(), arb("1e-40"))

    def test_mpmath_independent_single_family_value_and_derivative(self):
        coordinate = Fraction(1, 3)
        values = direct.evaluate_node(coordinate, [(arb(1), arb(7))], [Fraction(2)], [arb(2)],
                                      [[acb(1, 2)], [acb(3, -1)]])
        with mp.workdps(100):
            point = mp.mpf(1) / 3
            function = lambda argument: mp.exp(-30 / (1 - (argument / 2)**2) + 7j * argument)
            reference = [factor * derivative for factor in (mp.mpc(1, 2), mp.mpc(3, -1))
                         for derivative in (function(point), mp.diff(function, point, 2))]
            for value, truth in zip(values, reference):
                independent = acb(arb(mp.nstr(truth.real, 100), "1e-95"),
                                  arb(mp.nstr(truth.imag, 100), "1e-95"))
                self.assertTrue(value.overlaps(independent))

    def test_full_source_controls_against_independent_midpoint_evaluator(self):
        repair = json.loads((ROOT / "results/2338_exact_interpolation_repair.json").read_text())
        capture = json.loads((ROOT / "results/2275_gap_owner_audit.json").read_text())["owner_capture"]
        def exact_mp(value):
            value = Fraction(value)
            return mp.mpf(value.numerator) / value.denominator
        with mp.workdps(100):
            families = [(exact_mp(Fraction(float.fromhex(width))**2),
                         exact_mp(Fraction(float.fromhex(theta)))) for width, theta in capture["families_hex"]]
            coefficients = []
            for name in ("ideal_base_coefficient", "ideal_correction_coefficient"):
                channel = []
                for row in repair["coefficient_rows"]:
                    parts = []
                    for component in ("real", "imag"):
                        rectangle = row[name][component]
                        midpoint = (Fraction(rectangle["lower_exact"]) + Fraction(rectangle["upper_exact"])) / 2
                        parts.append(exact_mp(midpoint))
                    channel.append(mp.mpc(*parts))
                coefficients.append(channel)
            for control in self.result["node_controls"]:
                point = exact_mp(control["coordinate_exact"])
                reference = [mp.mpc(0) for _ in range(4)]
                for index, (radius, theta) in enumerate(families):
                    if abs(point) >= radius:
                        continue
                    ratio = point / radius
                    denominator = 1 - ratio**2
                    first = -60 * ratio / (radius * denominator**2)
                    second = -60 * (denominator**-2 + 4 * ratio**2 * denominator**-3) / radius**2
                    family = mp.exp(-30 / denominator + 1j * theta * point)
                    factor = second + first**2 - theta**2 + 2j * theta * first
                    for channel in range(2):
                        term = coefficients[channel][index] * family
                        reference[2 * channel] += term
                        reference[2 * channel + 1] += term * factor
                for stored, truth in zip(control["values"], reference):
                    enclosing = direct.decode_complex_rectangle(stored)
                    independent = acb(arb(mp.nstr(truth.real, 100), "1e-85"),
                                      arb(mp.nstr(truth.imag, 100), "1e-85"))
                    self.assertTrue(enclosing.overlaps(independent))


if __name__ == "__main__":
    unittest.main()
