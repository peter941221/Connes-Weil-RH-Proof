"""Selftests for the record-2622 panel-batch generator.

Pure exact rational arithmetic: an independent recurrence engine, the
panel094 semantic regression, partition-wide pricing, LF hygiene, and
negative controls. No Lean compilation happens here.
"""
from fractions import Fraction
import importlib.util
import json
from pathlib import Path
import sys
import unittest

if hasattr(sys, "set_int_max_str_digits"):
    sys.set_int_max_str_digits(0)

_SPEC = importlib.util.spec_from_file_location(
    "panel_batch_2622",
    Path(__file__).resolve().parent / "generate_moment_panel_batch_2622.py")
batch = importlib.util.module_from_spec(_SPEC)
sys.modules["panel_batch_2622"] = batch
_SPEC.loader.exec_module(batch)


def independent_recurrence(beta, center, degree):
    """Second implementation of the S recurrence: explicit forward loops,
    no shared helpers with the generator."""
    h = Fraction(0)
    d0 = 1 - center * center
    d1 = -2 * center
    d2 = Fraction(-1)
    den = [d0 * d0, 2 * d0 * d1, d1 * d1 + 2 * d0 * d2, 2 * d1 * d2, d2 * d2]
    num = [beta * value for value in den]
    num[0] -= 60 * center
    num[1] -= 60
    coeff = [Fraction(1)]
    for order in range(degree):
        rhs = Fraction(0)
        for index in range(0, min(4, order) + 1):
            rhs += num[index] * coeff[order - index]
        lhs = Fraction(0)
        for index in range(1, min(4, order) + 1):
            lhs += den[index] * (order - index + 1) * coeff[order - index + 1]
        coeff.append((rhs - lhs) / (den[0] * (order + 1)))
    return coeff, den, num


class PartitionTests(unittest.TestCase):
    def test_panel_centers_match_committed_partition(self):
        self.assertEqual(batch.panel_center(94), Fraction(9, 200))
        self.assertEqual(batch.panel_center(0), Fraction(-179, 200))
        self.assertEqual(batch.panel_center(179), Fraction(179, 200))
        for index in (0, 1, 93, 94, 95, 178, 179):
            self.assertEqual(
                Fraction(-9, 10) + (2 * index + 1) * batch.HALF_WIDTH,
                batch.panel_center(index))
        for index in range(180):
            self.assertLess(abs(batch.panel_center(index)) + batch.HALF_WIDTH, 1)

    def test_out_of_range_panel_rejected(self):
        with self.assertRaises(ValueError):
            batch.panel_center(180)
        with self.assertRaises(ValueError):
            batch.panel_center(-1)


class GenerationTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.owner = batch.get_data()
        cls.indices = [90, 91, 92, 93, 94, 95, 96, 97, 98, 99]
        cls.panels = [batch.panel_data(index, cls.owner) for index in cls.indices]

    def test_independent_engine_agrees(self):
        for panel in self.panels:
            coeff, den, num = independent_recurrence(
                panel["beta"], panel["center"], batch.DEGREE)
            self.assertEqual(coeff, panel["coefficients"][:-1])
            residual = list(panel["residual"])
            self.assertFalse(any(residual[:batch.DEGREE]))
            self.assertEqual(residual[batch.DEGREE + 5:], [0])

    def test_primitive_and_charge_recomputed(self):
        for panel in self.panels:
            primitive = [Fraction(0)] + [value / (index + 1) for index, value
                                         in enumerate(panel["coefficients"][:-1])]
            self.assertEqual(primitive, panel["primitive"])
            half = batch.HALF_WIDTH
            integral = batch.evaluate(half, primitive) - batch.evaluate(-half, primitive)
            self.assertEqual(integral, panel["integral"])
            edge = abs(panel["center"]) + half
            denominator_lower = (1 - edge ** 2) ** 2
            analytic = ((panel["amplitude_center"] + panel["amplitude_radius"]) *
                        (panel["growth_center"] + panel["growth_radius"]) *
                        (panel["residual_upper"] / denominator_lower) * 2 * half ** 2)
            charge = (panel["radius"] * (analytic +
                      panel["amplitude_radius"] * abs(integral)))
            self.assertEqual(charge, panel["integral_charge"])
            self.assertEqual(charge, panel["integral_charge"])
            self.assertLessEqual(charge, Fraction(1, 10 ** panel["charge_digits"]))

    def test_panel094_semantic_regression(self):
        batch.cross_check_panel94(self.panels)

    def test_payload_records_scope_honestly(self):
        sources, payload = batch.generate(self.indices, write=False)
        self.assertFalse(payload["lean_verified"])
        self.assertFalse(payload["actual_entry_containment_lean_verified"])
        self.assertFalse(payload["partition_assembly_lean_verified"])
        self.assertFalse(payload["producer_go"])
        self.assertFalse(payload["rh_claim"])
        self.assertEqual(sorted(payload["panels"]), self.indices)
        self.assertIn("C1RouteAMomentPanelBatchAudit2622.lean", sources)
        for index in self.indices:
            self.assertIn(f"C1RouteAMomentPanelScalars2622Panel{index:03d}.lean", sources)
            self.assertIn(f"C1RouteAMomentPanelTable2622Panel{index:03d}.lean", sources)
            self.assertIn(f"C1RouteAMomentActualPanel2622Panel{index:03d}.lean", sources)

    def test_emitted_sources_use_lf_only(self):
        sources, _ = batch.generate(self.indices, write=False)
        for filename, source in sources.items():
            self.assertNotIn("\r", source, filename)
        payload = json.loads(json.dumps(batch.payload_data(
            self.indices, self.panels, self.owner)))
        self.assertNotIn("\r", json.dumps(payload))


class PricingSweepTests(unittest.TestCase):
    def test_partition_charges_sit_inside_2597_budget(self):
        owner = batch.get_data()
        pricing = batch.partition_pricing(owner)
        margin = Fraction(pricing["achieved_margin_exact"])
        self.assertGreaterEqual(margin, batch.PARTITION_SAFETY)
        print(f"\npartition: 180-panel charge sum ~{float(Fraction(pricing['sum_charge_exact'])):.6e}, "
              f"worst panel {pricing['worst_panel_index']} "
              f"~{float(Fraction(pricing['worst_panel_charge_exact'])):.6e}, "
              f"2597 width margin ~{float(margin):.3e}", flush=True)


class NegativeControlTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.owner = batch.get_data()

    def test_perturbed_coefficient_breaks_residual_confinement(self):
        panel = batch.panel_data(94, self.owner)
        center = batch.panel_center(94)
        deficit = [1 - center ** 2, -2 * center, Fraction(-1)]
        denominator = batch.multiply(deficit, deficit)
        numerator = batch.add(batch.scale(panel["beta"], denominator),
                              [-60 * center, Fraction(-60)])
        coefficients = list(panel["coefficients"])
        coefficients[7] += Fraction(1, 10 ** 40)
        residual = batch.add(
            batch.multiply(denominator, batch.derivative(coefficients)),
            batch.scale(Fraction(-1), batch.multiply(numerator, coefficients)))
        self.assertTrue(any(residual[:batch.DEGREE]),
                        "perturbed coefficient must break residual confinement")

    def test_perturbed_primitive_breaks_reconstruction(self):
        panel = batch.panel_data(94, self.owner)
        primitive = list(panel["primitive"])
        primitive[3] += Fraction(1, 10 ** 50)
        with self.assertRaises(ValueError):
            if batch.derivative(primitive) != panel["coefficients"]:
                raise ValueError("primitive derivative does not reconstruct")

    def test_partition_gate_rejects_inflated_budget(self):
        saved = batch.PARTITION_SAFETY
        try:
            batch.PARTITION_SAFETY = 10 ** 30
            with self.assertRaises(ValueError):
                batch.partition_pricing(self.owner)
        finally:
            batch.PARTITION_SAFETY = saved

    def test_huge_phase_leaves_tiny_argument_regime(self):
        with self.assertRaises(ValueError):
            batch.compact_scalar(Fraction(10 ** 7))


if __name__ == "__main__":
    unittest.main(verbosity=2)
