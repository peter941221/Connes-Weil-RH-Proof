#!/usr/bin/env python3
"""Regression tests for the diagnostic, not analytic certificates."""
import contextlib
import hashlib
import io
import json
import tempfile
import unittest
from fractions import Fraction
from pathlib import Path
from unittest.mock import patch

import mpmath as mp

import routea_weighted_zero_multiplicity_proxy_audit_2273 as audit


class MultiplicityProxyTests(unittest.TestCase):
    def test_project_proxy_coverage_is_stable_across_precisions(self):
        for precision in (60, 100, 140):
            with self.subTest(precision=precision):
                result = audit.compute_audit(precision)
                self.assertEqual(result["status"], "BOTH-PROXIES-COVER-PROJECT-NORMALIZATION")
                self.assertGreater(Fraction(result["values"]["old_proxy_minus_value"]), 0)
                self.assertGreater(Fraction(result["values"]["corrected_proxy_minus_value"]), 0)

    def test_standard_and_project_normalizations_are_distinct(self):
        values = audit.compute_audit()["values"]
        self.assertGreater(Fraction(values["completed_xi_two"]), 1)
        self.assertLess(Fraction(values["spectral_multiplicity"]), Fraction("128.65"))
        self.assertGreater(Fraction(values["historical_standard_multiplicity"]),
                           Fraction(values["old_proxy"]))
        archived = json.loads((audit.ROOT /
            "results/2273_multiplicity_proxy_audit_superseded.json").read_text(encoding="utf-8"))
        self.assertEqual(values["historical_standard_multiplicity"],
                         archived["values"]["spectral_multiplicity"])

    def test_failed_diagnostic_overwrites_stale_success_and_exits_nonzero(self):
        with tempfile.TemporaryDirectory() as temporary:
            output = Path(temporary) / "audit.json"
            output.write_text('{"status":"BOTH-PROXIES-COVER-PROJECT-NORMALIZATION"}')
            failure = {"status": "AUDIT-REQUIRES-REVIEW", "values": {}}
            with patch.object(audit, "OUTPUT", output), \
                    patch.object(audit, "compute_audit", return_value=failure), \
                    contextlib.redirect_stdout(io.StringIO()):
                with self.assertRaises(SystemExit) as raised:
                    audit.main()
            self.assertEqual(raised.exception.code, 1)
            self.assertEqual(json.loads(output.read_text())["status"], "AUDIT-REQUIRES-REVIEW")

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
