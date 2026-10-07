"""Selftests for the record-2623 row-batch generator.

The primary gate is a byte regression of the whole row-zero emission
against the committed record-2617 files: the row parameterization must not
disturb the already-certified row. Independent exact recomputation of a
later row's entry bounds and negative controls complete the gate.
"""

import importlib.util
import json
from fractions import Fraction
from pathlib import Path
import sys
import unittest

if hasattr(sys, "set_int_max_str_digits"):
    sys.set_int_max_str_digits(0)

_SCRIPTS = Path(__file__).resolve().parent
_SPEC = importlib.util.spec_from_file_location(
    "coord_bounds_2617", _SCRIPTS / "generate_static_coordinate_bounds_2617.py")
bounds = importlib.util.module_from_spec(_SPEC)
sys.modules["coord_bounds_2617"] = bounds
_SPEC.loader.exec_module(bounds)

from generate_static_coordinate_bounds_2617 import (  # noqa: E402
    CONVERTED_ROWS,
    DEV,
    WITNESS,
    generated_row_sources,
    generated_sources,
    row_facade_source,
)
from generate_static_sum_blocks_2600 import module_source  # noqa: E402

BATCH_ROWS = [1, 2, 3, 4, 5]


def committed_content(filename):
    """Committed file bytes with line endings normalized.

    The record-2617 validation pinned the on-disk bytes of its day, and the
    Row00Col00 legacy file is CRLF on disk (its recorded source hash is the
    CRLF variant). Regressions compare content, so both sides are
    normalized to LF before comparison.
    """
    return (DEV / filename).read_bytes().replace(b"\r\n", b"\n")


def independent_entry_bound(payload, row, column):
    """Straight-loop recomputation of one defect entry's L1 coordinate bound."""
    coordinates = ("reLo", "reHi", "imLo", "imHi")
    sums = {coordinate: Fraction(0) for coordinate in coordinates}
    for inner in range(30):
        left = payload["candidate_inverse"][row][inner]
        right = payload["matrix"][inner][column]
        lr = (Fraction(left["real"]["lower_exact"]), Fraction(left["real"]["upper_exact"]))
        li = (Fraction(left["imag"]["lower_exact"]), Fraction(left["imag"]["upper_exact"]))
        rr = (Fraction(right["real"]["lower_exact"]), Fraction(right["real"]["upper_exact"]))
        ri = (Fraction(right["imag"]["lower_exact"]), Fraction(right["imag"]["upper_exact"]))
        products = [a * b for a in lr for b in rr]
        real_lo, real_hi = min(products), max(products)
        products = [a * b for a in li for b in ri]
        neg_lo, neg_hi = -max(products), -min(products)
        real = (real_lo + neg_lo, real_hi + neg_hi)
        products = [a * b for a in lr for b in ri]
        first_lo, first_hi = min(products), max(products)
        products = [a * b for a in li for b in rr]
        second_lo, second_hi = min(products), max(products)
        imag = (first_lo + second_lo, first_hi + second_hi)
        sums["reLo"] += real[0]
        sums["reHi"] += real[1]
        sums["imLo"] += imag[0]
        sums["imHi"] += imag[1]
    defect = {
        "reLo": Fraction(int(column == row)) - sums["reHi"],
        "reHi": Fraction(int(column == row)) - sums["reLo"],
        "imLo": -sums["imHi"],
        "imHi": -sums["imLo"],
    }
    return (max(abs(defect["reLo"]), abs(defect["reHi"])),
            max(abs(defect["imLo"]), abs(defect["imHi"])))


class RowZeroRegressionTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.payload = json.loads(WITNESS.read_text(encoding="utf-8"))

    def test_row_zero_emission_matches_committed_files(self):
        for filename, expected in generated_row_sources(self.payload, 0).items():
            self.assertEqual(
                committed_content(filename), expected.encode("utf-8"),
                f"row-zero byte regression failed: {filename}")

    def test_row_zero_validator_shims_unchanged(self):
        for column in range(30):
            for filename, expected in generated_sources(self.payload, column).items():
                self.assertEqual(committed_content(filename),
                                 expected.encode("utf-8"), filename)
        self.assertEqual(
            committed_content("C1RouteACorrectionStaticDefectBounds2600Row00.lean"),
            row_facade_source(0).encode("utf-8"))
        self.assertEqual(
            committed_content("C1RouteACorrectionStaticDefectSumBlocks2600Row00Col00.lean"),
            module_source(0, self.payload).encode("utf-8"))


class BatchRowTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.payload = json.loads(WITNESS.read_text(encoding="utf-8"))

    def test_batch_rows_are_converted_and_nonzero(self):
        self.assertTrue(set(BATCH_ROWS) <= CONVERTED_ROWS)
        self.assertNotIn(0, BATCH_ROWS)

    def test_independent_bounds_agree_with_generator(self):
        for row, column in ((1, 0), (1, 1), (3, 17), (5, 29)):
            real_bound, imag_bound = independent_entry_bound(self.payload, row, column)
            sums, defect, gen_real, gen_imag = bounds.compute_coordinates(
                self.payload, column, row)
            self.assertEqual(real_bound, gen_real, f"cell {row:02d}-{column:02d}")
            self.assertEqual(imag_bound, gen_imag, f"cell {row:02d}-{column:02d}")

    def test_emitted_batch_sources_use_lf_only(self):
        for row in BATCH_ROWS:
            for filename, source in generated_row_sources(self.payload, row).items():
                self.assertNotIn("\r", source, filename)
        facade = f"C1RouteACorrectionStaticDefectBounds2600Row{BATCH_ROWS[-1]:02d}.lean"
        self.assertIn(f"row_{BATCH_ROWS[-1]:02d}",
                      generated_row_sources(self.payload, BATCH_ROWS[-1])[facade])

    def test_facade_keeps_consumer_names(self):
        source = row_facade_source(3)
        self.assertIn("theorem candidateInverseDefectEntryBound2600_row_03 (j : Fin 30)",
                      source)
        self.assertIn("fin_cases j", source)
        for column in range(30):
            self.assertIn(
                f"import ConnesWeilRH.Dev.C1RouteACorrectionStaticDefectCoordinate2617Cell03{column:02d}",
                source)

    def test_row_dependency_chain_imports_generic_block_once(self):
        col00 = module_source(0, self.payload, 2)
        self.assertIn("import ConnesWeilRH.Dev.C1RouteACorrectionStaticDefectSumBlocks2600Row00Col00",
                      col00)
        self.assertIn("import ConnesWeilRH.Dev.C1RouteACorrectionStaticDefectProductCache2600Row02",
                      col00)
        self.assertNotIn("theorem fin30_sum_eq_six_blocks", col00)
        col07 = module_source(7, self.payload, 2)
        self.assertIn("import ConnesWeilRH.Dev.C1RouteACorrectionStaticDefectSumBlocks2600Row02Col00",
                      col07)
        self.assertNotIn("theorem fin30_sum_eq_six_blocks", col07)


class NegativeControlTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.payload = json.loads(WITNESS.read_text(encoding="utf-8"))

    def test_perturbed_inverse_changes_the_bound(self):
        perturbed = json.loads(json.dumps(self.payload))
        original = perturbed["candidate_inverse"][2][5]["real"]["lower_exact"]
        perturbed["candidate_inverse"][2][5]["real"]["lower_exact"] = (
            str(Fraction(original) + Fraction(1, 10 ** 60)))
        real_original, _ = independent_entry_bound(self.payload, 2, 5)
        real_perturbed, _ = independent_entry_bound(perturbed, 2, 5)
        self.assertNotEqual(real_original, real_perturbed)

    def test_out_of_range_rows_rejected(self):
        with self.assertRaises(ValueError):
            bounds.compute_coordinates(self.payload, 30, 0)
        with self.assertRaises(ValueError):
            bounds.compute_coordinates(self.payload, 0, 30)


if __name__ == "__main__":
    unittest.main(verbosity=2)
