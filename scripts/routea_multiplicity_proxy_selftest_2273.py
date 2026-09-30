#!/usr/bin/env python3
"""Regression tests for the diagnostic, not analytic certificates."""
import hashlib
import json
import unittest
from fractions import Fraction

import mpmath as mp

import routea_weighted_zero_multiplicity_proxy_audit_2273 as audit


class MultiplicityProxyTests(unittest.TestCase):
    def test_rounding_direction_is_stable_across_precisions(self):
        for precision in (60, 100, 140):
            with self.subTest(precision=precision):
                result = audit.compute_audit(precision)
                self.assertEqual(result["status"], "OLD-PROXY-UNDER-ROUNDS")
                self.assertLess(Fraction(result["values"]["old_proxy_minus_exact"]), 0)
                self.assertGreater(Fraction(result["values"]["corrected_proxy_minus_exact"]), 0)

    def test_global_precision_is_preserved(self):
        precision = mp.mp.dps
        audit.compute_audit()
        self.assertEqual(mp.mp.dps, precision)

    def test_low_precision_is_rejected(self):
        with self.assertRaises(ValueError):
            audit.compute_audit(20)

    def test_committed_artifact_and_sources_reproduce(self):
        stored = json.loads(audit.OUTPUT.read_text(encoding="utf-8"))
        self.assertEqual(stored, audit.compute_audit())
        for source, digest in stored["source_sha256"].items():
            contents = (audit.ROOT / source).read_text(encoding="utf-8").encode("utf-8")
            self.assertEqual(digest, hashlib.sha256(contents).hexdigest())

    def test_corrected_tail_covers_exact_rational_product(self):
        product = 4 * Fraction("128.70692502981") * Fraction("9506275.102584327")
        self.assertLess(product, Fraction("4894093747.7643"))


if __name__ == "__main__":
    unittest.main()
