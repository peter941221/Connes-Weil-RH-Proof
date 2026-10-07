"""Selftests for the record-2626 row-batch extension (rows 6-29).

The primary gate stays the byte regression of the whole row-zero emission
against the committed record-2617 files, plus the committed rows 1-5
regression: the row extension must not disturb certified rows. Independent
exact recomputation of sampled new rows' entry bounds and negative controls
complete the gate.
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
    WITNESS,
    generated_row_sources,
    row_facade_source,
)
from generate_static_sum_blocks_2600 import module_source  # noqa: E402
from static_coordinate_rows_selftest_2623 import (  # noqa: E402
    committed_content,
    independent_entry_bound,
)

BATCH_ROWS = list(range(6, 30))
COMMITTED_ROWS = [1, 2, 3, 4, 5]


class RowZeroRegressionTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.payload = json.loads(WITNESS.read_text(encoding="utf-8"))

    def test_row_zero_emission_matches_committed_files(self):
        for filename, expected in generated_row_sources(self.payload, 0).items():
            self.assertEqual(
                committed_content(filename), expected.encode("utf-8"),
                f"row-zero byte regression failed: {filename}")

    def test_committed_rows_1_to_5_emission_matches_committed_files(self):
        for row in COMMITTED_ROWS:
            for filename, expected in generated_row_sources(self.payload, row).items():
                self.assertEqual(
                    committed_content(filename), expected.encode("utf-8"),
                    f"row {row:02d} byte regression failed: {filename}")


class BatchRowTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.payload = json.loads(WITNESS.read_text(encoding="utf-8"))

    def test_scope_converted_disjoint_and_total(self):
        self.assertTrue(set(BATCH_ROWS) <= CONVERTED_ROWS)
        self.assertNotIn(0, BATCH_ROWS)
        self.assertEqual(set(BATCH_ROWS) & set(COMMITTED_ROWS), set())
        self.assertEqual(sorted(set(BATCH_ROWS) | set(COMMITTED_ROWS) | {0}),
                         list(range(30)))

    def test_independent_bounds_agree_with_generator(self):
        for row, column in ((6, 0), (12, 17), (23, 5), (29, 29)):
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
        source = row_facade_source(29)
        self.assertIn("theorem candidateInverseDefectEntryBound2600_row_29 (j : Fin 30)",
                      source)
        self.assertIn("fin_cases j", source)
        for column in range(30):
            self.assertIn(
                f"import ConnesWeilRH.Dev.C1RouteACorrectionStaticDefectCoordinate2617Cell29{column:02d}",
                source)

    def test_row_dependency_chain_imports_generic_block_once(self):
        col00 = module_source(0, self.payload, 29)
        self.assertIn("import ConnesWeilRH.Dev.C1RouteACorrectionStaticDefectSumBlocks2600Row00Col00",
                      col00)
        self.assertIn("import ConnesWeilRH.Dev.C1RouteACorrectionStaticDefectProductCache2600Row29",
                      col00)
        self.assertNotIn("theorem fin30_sum_eq_six_blocks", col00)


class NegativeControlTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.payload = json.loads(WITNESS.read_text(encoding="utf-8"))

    def test_perturbed_inverse_changes_the_bound(self):
        perturbed = json.loads(json.dumps(self.payload))
        original = perturbed["candidate_inverse"][20][7]["real"]["lower_exact"]
        perturbed["candidate_inverse"][20][7]["real"]["lower_exact"] = (
            str(Fraction(original) + Fraction(1, 10 ** 60)))
        real_original, _ = independent_entry_bound(self.payload, 20, 7)
        real_perturbed, _ = independent_entry_bound(perturbed, 20, 7)
        self.assertNotEqual(real_original, real_perturbed)

    def test_out_of_range_rows_rejected(self):
        with self.assertRaises(ValueError):
            bounds.compute_coordinates(self.payload, 30, 0)
        with self.assertRaises(ValueError):
            bounds.compute_coordinates(self.payload, 0, 30)


if __name__ == "__main__":
    unittest.main(verbosity=2)
