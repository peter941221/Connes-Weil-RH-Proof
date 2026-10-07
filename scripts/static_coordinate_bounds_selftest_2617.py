"""Check the coordinate generator against the independent Fraction engine."""

import copy
from contextlib import redirect_stdout
import io
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch
from fractions import Fraction

import routea_moment_matrix_exact_check_2351 as checker
from generate_static_coordinate_bounds_2617 import (
    COORDINATES,
    DEV,
    WITNESS,
    compute_coordinates,
    generated_sources,
    generated_row_sources,
    row_facade_source,
)
from generate_static_sum_blocks_2600 import module_source
from generate_static_defect_bounds_2600 import row_module
import generate_static_defect_bounds_2600 as primary_generator
from validate_static_coordinate_bounds_2617 import parse_successful_log


def interval_value(real_lo: int, real_hi: int, imag_lo: int, imag_hi: int) -> dict:
    return {
        "real": {"lower_exact": str(real_lo), "upper_exact": str(real_hi)},
        "imag": {"lower_exact": str(imag_lo), "upper_exact": str(imag_hi)},
    }


def independently_compute(payload: dict, column: int = 0):
    matrix = payload["matrix"]
    inverse = payload["candidate_inverse"]
    product = checker.sum_complex(
        checker.complex_mul(checker.complex_interval(inverse[0][inner]),
                            checker.complex_interval(matrix[inner][column]))
        for inner in range(30)
    )
    defect = checker.complex_add(checker.point(int(column == 0)), checker.complex_neg(product))
    return product, defect, checker.l1_upper(defect)


class StaticCoordinateBoundsTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.payload = json.loads(WITNESS.read_text(encoding="utf-8"))

    def assert_matches_independent_engine(self, payload, column=0):
        sums, defect, real_bound, imag_bound = compute_coordinates(payload, column)
        product, expected_defect, expected_upper = independently_compute(payload, column)
        self.assertEqual(tuple(sums[key] for key in COORDINATES),
                         (product[0][0], product[0][1], product[1][0], product[1][1]))
        self.assertEqual(tuple(defect[key] for key in COORDINATES),
                         (expected_defect[0][0], expected_defect[0][1],
                          expected_defect[1][0], expected_defect[1][1]))
        self.assertEqual(real_bound + imag_bound, expected_upper)
        self.assertGreaterEqual(real_bound, 0)
        self.assertGreaterEqual(imag_bound, 0)

    def test_committed_cell_matches_independent_engine(self):
        for column in range(30):
            with self.subTest(column=column):
                self.assert_matches_independent_engine(self.payload, column)

    def test_zero_product_has_identity_defect(self):
        payload = copy.deepcopy(self.payload)
        payload["candidate_inverse"][0] = [interval_value(0, 0, 0, 0) for _ in range(30)]
        _, defect, real_bound, imag_bound = compute_coordinates(payload)
        self.assertEqual(defect, {"reLo": Fraction(1), "reHi": Fraction(1),
                                  "imLo": Fraction(0), "imHi": Fraction(0)})
        self.assertEqual((real_bound, imag_bound), (Fraction(1), Fraction(0)))
        self.assert_matches_independent_engine(payload)

    def test_signed_intervals_crossing_zero(self):
        payload = copy.deepcopy(self.payload)
        payload["candidate_inverse"][0] = [interval_value(0, 0, 0, 0) for _ in range(30)]
        payload["candidate_inverse"][0][0] = interval_value(-2, 3, -5, 7)
        payload["candidate_inverse"][0][1] = interval_value(-9, -4, 1, 6)
        payload["matrix"][0][0] = interval_value(-11, 13, -17, 19)
        payload["matrix"][1][0] = interval_value(2, 5, -7, -3)
        self.assert_matches_independent_engine(payload)

    def test_generated_sources_match_checked_in_files(self):
        for column in range(30):
            for filename, source in generated_sources(self.payload, column).items():
                with self.subTest(filename=filename):
                    self.assertEqual((DEV / filename).read_text(encoding="utf-8"), source)
        self.assertEqual((DEV / "C1RouteACorrectionStaticDefectBounds2600Row00.lean").read_text(
            encoding="utf-8"), row_facade_source())

    def test_block_modules_declare_the_generic_sum_once(self):
        for column in range(30):
            source = module_source(column, self.payload)
            self.assertEqual("theorem fin30_sum_eq_six_blocks" in source, column == 0)
            filename = f"C1RouteACorrectionStaticDefectSumBlocks2600Row00Col{column:02d}.lean"
            self.assertEqual((DEV / filename).read_text(encoding="utf-8"), source)

    def test_off_diagonal_zero_product_has_zero_defect(self):
        payload = copy.deepcopy(self.payload)
        payload["candidate_inverse"][0] = [interval_value(0, 0, 0, 0) for _ in range(30)]
        _, defect, real_bound, imag_bound = compute_coordinates(payload, 29)
        self.assertTrue(all(value == 0 for value in defect.values()))
        self.assertEqual((real_bound, imag_bound), (Fraction(0), Fraction(0)))
        self.assert_matches_independent_engine(payload, 29)

    def test_column_outside_production_scope_is_rejected(self):
        for column in (-1, 30):
            with self.subTest(column=column):
                with self.assertRaisesRegex(ValueError, "column must be"):
                    generated_sources(self.payload, column)

    def test_primary_generator_preserves_the_row_facade(self):
        self.assertEqual(row_module(0, [], [], [], self.payload["matrix"],
                                    self.payload["candidate_inverse"]), row_facade_source())

    def test_primary_generator_main_emits_the_complete_row_bundle(self):
        with tempfile.TemporaryDirectory() as directory:
            target = Path(directory)
            with patch.multiple(primary_generator, ROOT=target, DEV=target,
                                OUTPUT=target / "C1RouteACorrectionStaticDefectBounds2600.lean",
                                COMMON_OUTPUT=target / "C1RouteACorrectionStaticDefectBounds2600Common.lean"):
                with redirect_stdout(io.StringIO()):
                    primary_generator.main()
            for filename, expected in generated_row_sources(self.payload).items():
                with self.subTest(filename=filename):
                    self.assertEqual((target / filename).read_text(encoding="utf-8"), expected)
                    self.assertEqual((DEV / filename).read_text(encoding="utf-8"), expected)

    def test_consumer_uses_coordinate_bounds_without_rectangle_equality(self):
        sources = generated_sources(self.payload)
        consumer = sources["C1RouteACorrectionStaticDefectCoordinate2617Cell0000.lean"]
        self.assertIn("rectL1Upper2598_le_of_coordinate_bounds2617", consumer)
        self.assertNotIn("ComplexRect2427.ext", consumer)
        self.assertNotIn("eq_static", consumer)
        for coordinate in COORDINATES:
            self.assertIn(f"matrixDefectInterval2598_{coordinate}", consumer)
        self.assertEqual(len(sources), 6)

    def test_generator_rejects_wrong_scope(self):
        payload = copy.deepcopy(self.payload)
        payload["dimension"] = 29
        with self.assertRaisesRegex(ValueError, "dimension-30"):
            generated_sources(payload)

    def test_generator_rejects_inverted_matrix_interval(self):
        payload = copy.deepcopy(self.payload)
        payload["matrix"][0][0] = interval_value(2, 1, 0, 0)
        with self.assertRaisesRegex(ValueError, "inverted"):
            generated_sources(payload)

    def test_generator_rejects_nonpoint_candidate_inverse(self):
        payload = copy.deepcopy(self.payload)
        payload["candidate_inverse"][0][0] = interval_value(0, 1, 0, 0)
        with self.assertRaisesRegex(ValueError, "point rectangles"):
            generated_sources(payload)

    def test_validator_rejects_interrupted_log_even_with_time_exit_zero(self):
        text = "Command terminated by signal 2\nExit status: 0\nRESOURCE_RESULT exit=130\n"
        with self.assertRaisesRegex(ValueError, "successful runner exit"):
            parse_successful_log(text)

    def test_validator_rejects_wrong_axioms(self):
        text = ("RESOURCE_RESULT exit=0\n"
                "'example' depends on axioms: [propext, Classical.choice, Quot.sound, sorryAx]\n")
        with self.assertRaisesRegex(ValueError, "forbidden placeholder"):
            parse_successful_log(text, "example")

    def test_validator_rejects_stale_source_fingerprint(self):
        text = "RESOURCE_RESULT exit=0\nSOURCE_SHA256=old\n"
        with self.assertRaisesRegex(ValueError, "stale or missing SOURCE_SHA256"):
            parse_successful_log(text, source_sha256="current")

    def test_validator_accepts_wrapped_exact_axiom_list(self):
        text = ("RESOURCE_RESULT exit=0\n"
                "'example' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]\n"
                "Maximum resident set size (kbytes): 42\n"
                "Elapsed (wall clock) time (h:mm:ss or m:ss): 1:02.50\n")
        self.assertEqual(parse_successful_log(text, "example"),
                         {"wall_seconds": 62.5, "peak_rss_kib": 42})


if __name__ == "__main__":
    unittest.main()
