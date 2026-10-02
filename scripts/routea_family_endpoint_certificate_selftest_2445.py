"""2445 structural and mutation controls."""

import json
import math
from fractions import Fraction
import unittest
from pathlib import Path

import routea_family_endpoint_certificate_2445 as producer

ROOT = Path(__file__).resolve().parents[1]
ARTIFACT = ROOT / "results/2445_routea_family_endpoint_certificate.json"


class FamilyEndpointCertificateTests(unittest.TestCase):
    def setUp(self):
        self.artifact = json.loads(ARTIFACT.read_text(encoding="utf-8"))

    def test_owner_shape_and_scope(self):
        self.assertEqual(self.artifact["record"], 2445)
        self.assertEqual(self.artifact["status"], "MPFR-DIRECTED-FAMILY-RECTANGLE-POINT-BOX")
        self.assertFalse(self.artifact["certificate"])
        self.assertEqual(self.artifact["owner"]["families"], 30)
        self.assertEqual(self.artifact["validation"]["position_count"], 9)
        self.assertEqual(self.artifact["validation"]["terms_per_row"], 30)

    def test_rows_are_finite_and_factorized(self):
        self.assertEqual(len(self.artifact["rows"]), 18)
        for row in self.artifact["rows"]:
            self.assertEqual(len(row["terms"]), 30)
            for term in row["terms"]:
                rectangle = term["rectangle"]
                for component in ("real", "imag"):
                    self.assertLessEqual(rectangle[component]["lo"], rectangle[component]["hi"])
                    self.assertTrue(math.isfinite(rectangle[component]["lo"]))
                    self.assertTrue(math.isfinite(rectangle[component]["hi"]))
                if not rectangle["outside_support"]:
                    for factor in ("q", "bump", "phase_re", "phase_im"):
                        self.assertIn(factor, rectangle)

    def test_mutation_moves_endpoint_inward(self):
        rectangle = self.artifact["rows"][8]["terms"][0]["rectangle"]["real"]
        mutated = math.nextafter(rectangle["hi"], -math.inf)
        self.assertLess(mutated, rectangle["hi"])

    def test_support_branches_match_exact_stored_owner(self):
        capture = json.loads(producer.CAPTURE.read_text(encoding="utf-8"))["owner_capture"]
        for row in self.artifact["rows"]:
            position = Fraction.from_float(row["position"])
            for term in row["terms"]:
                width = Fraction.from_float(float.fromhex(capture["families_hex"][term["index"]][0]))
                expected = abs(position) >= width ** 2
                self.assertEqual(term["rectangle"]["outside_support"], expected)

    def test_rounded_square_cannot_force_zero(self):
        width = math.nextafter(1.0, math.inf)
        position = width * width
        self.assertFalse(producer.outside_stored_support(width, position))
        with self.assertRaisesRegex(ValueError, "strictly positive q interval"):
            producer.family_rectangle(producer.load_preflight(), width, 0.0, 1.0 + 0j, position)


if __name__ == "__main__":
    unittest.main()
