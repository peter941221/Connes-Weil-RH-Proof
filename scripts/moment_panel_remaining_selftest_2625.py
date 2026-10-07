"""Selftests for the record-2625 remaining-panel driver.

Pure exact rational arithmetic: scope disjointness from the committed
record-2622 batch, an independent recurrence engine on sampled panels, the
out-of-scope panel094 canary, partition-wide pricing, LF hygiene, and
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

_SCRIPTS = Path(__file__).resolve().parent
_SPEC = importlib.util.spec_from_file_location(
    "panel_remaining_2625", _SCRIPTS / "generate_moment_panel_remaining_2625.py")
driver = importlib.util.module_from_spec(_SPEC)
sys.modules["panel_remaining_2625"] = driver
_SPEC.loader.exec_module(driver)
batch = driver.load_batch_generator()

SAMPLE = [0, 17, 45, 89, 100, 137, 165, 179]


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


class ScopeTests(unittest.TestCase):
    def test_scope_disjoint_from_committed_batch(self):
        committed = set(range(90, 100))
        self.assertEqual(set(driver.REMAINING) & committed, set())
        self.assertEqual(sorted(set(driver.REMAINING) | committed),
                         list(range(180)))
        self.assertEqual(len(driver.REMAINING), 170)

    def test_panel_centers_match_committed_partition(self):
        self.assertEqual(batch.panel_center(0), Fraction(-179, 200))
        self.assertEqual(batch.panel_center(179), Fraction(179, 200))
        for index in driver.REMAINING:
            self.assertEqual(
                Fraction(-9, 10) + (2 * index + 1) * batch.HALF_WIDTH,
                batch.panel_center(index))
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
        cls.indices = driver.REMAINING
        cls.panels = [batch.panel_data(index, cls.owner)
                      for index in cls.indices]
        cls.sources, cls.payload = driver.generate(cls.indices, write=False)

    def test_independent_engine_agrees(self):
        by_index = {panel["index"]: panel for panel in self.panels}
        for index in SAMPLE:
            panel = by_index[index]
            coeff, den, num = independent_recurrence(
                panel["beta"], panel["center"], batch.DEGREE)
            self.assertEqual(coeff, panel["coefficients"][:-1],
                             f"panel {index:03d}")
            residual = list(panel["residual"])
            self.assertFalse(any(residual[:batch.DEGREE]))
            self.assertEqual(residual[batch.DEGREE + 5:], [0])

    def test_primitive_and_charge_recomputed(self):
        by_index = {panel["index"]: panel for panel in self.panels}
        for index in SAMPLE:
            panel = by_index[index]
            primitive = [Fraction(0)] + [value / (order + 1) for order, value
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
            self.assertLessEqual(charge, Fraction(1, 10 ** panel["charge_digits"]))

    def test_panel094_canary_semantic_regression(self):
        batch.cross_check_panel94([batch.panel_data(94, self.owner)])

    def test_payload_records_scope_honestly(self):
        self.assertEqual(self.payload["record"], 2625)
        self.assertEqual(self.payload["batch_record"], 2622)
        self.assertEqual(sorted(self.payload["panels"]), driver.REMAINING)
        self.assertFalse(self.payload["lean_verified"])
        self.assertFalse(self.payload["actual_entry_containment_lean_verified"])
        self.assertFalse(self.payload["partition_assembly_lean_verified"])
        self.assertFalse(self.payload["producer_go"])
        self.assertFalse(self.payload["rh_claim"])
        self.assertIn(driver.AUDIT_MODULE + ".lean", self.sources)
        self.assertNotIn("C1RouteAMomentPanelBatchAudit2622.lean", self.sources)
        for index in [0, 89, 100, 179]:
            self.assertIn(f"C1RouteAMomentPanelScalars2622Panel{index:03d}.lean",
                          self.sources)
            self.assertIn(f"C1RouteAMomentPanelTable2622Panel{index:03d}.lean",
                          self.sources)
            self.assertIn(f"C1RouteAMomentActualPanel2622Panel{index:03d}.lean",
                          self.sources)
        for index in range(90, 100):
            self.assertNotIn(f"C1RouteAMomentActualPanel2622Panel{index:03d}.lean",
                             self.sources)

    def test_emitted_sources_use_lf_only(self):
        for filename, source in self.sources.items():
            self.assertNotIn("\r", source, filename)
        self.assertNotIn("\r", json.dumps(self.payload))


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
        panel = batch.panel_data(137, self.owner)
        center = batch.panel_center(137)
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
