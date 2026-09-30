"""Record-2271 regressions for fail-closed status and replay provenance.

Uses unittest and temporary operand files. No numerical search is performed.
Run with --integration in Linux to exercise the actual 2267 reduction too.
"""
import contextlib
import hashlib
import io
import json
import math
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

import routea_weighted_zero_sigma_envelope_certified_2267 as strip

INTEGRATION = "--integration" in sys.argv
if INTEGRATION:
    sys.argv.remove("--integration")


class StatusTests(unittest.TestCase):
    def test_covered(self):
        self.assertEqual(strip.classify_status(6.0, 9.0, True, True),
                         "CERTIFIED-STRIP-COVERED")

    def test_equal_bound(self):
        self.assertEqual(strip.classify_status(9.0, 9.0, True, True),
                         "CERTIFIED-STRIP-COVERED")

    def test_reprice(self):
        self.assertEqual(strip.classify_status(10.0, 9.0, True, True),
                         "STRIP-REPRICE-NEEDED")

    def test_anchor_failure_dominates_coverage(self):
        self.assertEqual(strip.classify_status(6.0, 9.0, False, True),
                         "STRIP-CONTROL-FAIL")

    def test_input_failure_dominates_coverage(self):
        self.assertEqual(strip.classify_status(6.0, 9.0, True, False),
                         "STRIP-CONTROL-FAIL")

    def test_nonfinite_and_nonpositive(self):
        for invalid in (math.nan, math.inf, -math.inf, 0.0, -1.0):
            with self.subTest(invalid=invalid):
                self.assertEqual(strip.classify_status(invalid, 9.0, True, True),
                                 "STRIP-CONTROL-FAIL")
                self.assertEqual(strip.classify_status(6.0, invalid, True, True),
                                 "STRIP-CONTROL-FAIL")


class ManifestTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.operand = self.root / "operand.json"
        self.operand.write_bytes(b"{\"value\":1}\n")
        self.manifest_path = self.root / "manifest.json"
        self.manifest = {
            "schema_version": 1,
            "parameters": strip.replay_parameters(),
            "files": {"operand.json": {
                "sha256": hashlib.sha256(self.operand.read_bytes()).hexdigest(),
                "bytes": self.operand.stat().st_size}},
        }
        self.inventory_patch = patch.object(strip, "required_inputs",
                                             return_value=["operand.json"])
        self.inventory_patch.start()
        self.addCleanup(self.inventory_patch.stop)

    def validate(self):
        self.manifest_path.write_text(json.dumps(self.manifest), encoding="utf-8")
        return strip.validate_manifest(self.root, self.manifest_path)

    def test_valid(self):
        result = self.validate()
        self.assertTrue(result["ok"])
        self.assertEqual(result["files_checked"], 1)
        self.assertEqual(len(result["manifest_sha256"]), 64)

    def test_modified_operand(self):
        self.operand.write_bytes(b"changed")
        self.assertFalse(self.validate()["ok"])

    def test_missing_operand(self):
        self.operand.unlink()
        self.assertFalse(self.validate()["ok"])

    def test_incomplete_inventory(self):
        self.manifest["files"] = {}
        self.assertFalse(self.validate()["ok"])

    def test_parameter_drift(self):
        self.manifest["parameters"]["half_step"] = 0.01
        self.assertFalse(self.validate()["ok"])

    def test_path_escape(self):
        self.manifest["files"]["../outside.json"] = {}
        result = self.validate()
        self.assertFalse(result["ok"])
        self.assertTrue(any("outside replay root" in error
                            for error in result["errors"]))

    def test_invalid_schema(self):
        self.manifest["schema_version"] = 2
        self.assertFalse(self.validate()["ok"])

    def test_malformed_json(self):
        self.manifest_path.write_text("not json", encoding="utf-8")
        self.assertFalse(strip.validate_manifest(self.root, self.manifest_path)["ok"])

    def test_manifest_is_not_object(self):
        self.manifest_path.write_text("[]", encoding="utf-8")
        self.assertFalse(strip.validate_manifest(self.root, self.manifest_path)["ok"])

    def test_bad_entry(self):
        self.manifest["files"]["operand.json"] = None
        self.assertFalse(self.validate()["ok"])


class CliTests(unittest.TestCase):
    def test_invalid_input_does_not_start_reduction(self):
        with patch.object(strip, "validate_manifest", return_value={"ok": False}), \
                patch.object(strip, "run_reduction") as reduction, \
                patch.object(strip, "write_control_failure") as failure, \
                contextlib.redirect_stdout(io.StringIO()):
            self.assertEqual(strip.main([]), 1)
            reduction.assert_not_called()
            failure.assert_called_once()

    def test_failed_status_exits_nonzero(self):
        with patch.object(strip, "validate_manifest", return_value={"ok": True}), \
                patch.object(strip, "run_reduction", return_value={
                    "status": "STRIP-CONTROL-FAIL"}), \
                contextlib.redirect_stdout(io.StringIO()):
            self.assertEqual(strip.main([]), 1)

    def test_missing_operand_exits_nonzero(self):
        with patch.object(strip, "validate_manifest", return_value={"ok": True}), \
                patch.object(strip, "run_reduction", side_effect=FileNotFoundError()), \
                patch.object(strip, "write_control_failure") as failure, \
                contextlib.redirect_stdout(io.StringIO()):
            self.assertEqual(strip.main([]), 1)
            failure.assert_called_once()

    def test_input_failure_overwrites_stale_success(self):
        with tempfile.TemporaryDirectory() as temporary, \
                patch.object(strip, "validate_manifest", return_value={"ok": False}), \
                contextlib.redirect_stdout(io.StringIO()):
            output = Path(temporary) / "result.json"
            output.write_text('{"status":"CERTIFIED-STRIP-COVERED"}')
            self.assertEqual(strip.main(["--output", str(output)]), 1)
            self.assertEqual(json.loads(output.read_text())["status"],
                             "STRIP-CONTROL-FAIL")

    def test_verify_only_does_not_overwrite_result(self):
        with patch.object(strip, "validate_manifest", return_value={"ok": False}), \
                patch.object(strip, "write_control_failure") as failure, \
                contextlib.redirect_stdout(io.StringIO()):
            self.assertEqual(strip.main(["--verify-only"]), 1)
            failure.assert_not_called()


@unittest.skipUnless(INTEGRATION, "use --integration for the Linux numeric replay")
class IntegrationTests(unittest.TestCase):
    def test_real_anchor_failure_is_not_success(self):
        validation = strip.validate_manifest(strip.ROOT, strip.MANIFEST)
        self.assertTrue(validation["ok"], validation["errors"])
        with tempfile.TemporaryDirectory() as temporary, \
                patch.object(strip, "FROZEN_C", strip.FROZEN_C * 2), \
                patch.object(strip, "validate_manifest", return_value=validation), \
                contextlib.redirect_stdout(io.StringIO()):
            output = Path(temporary) / "anchor_failure.json"
            self.assertEqual(strip.main(["--output", str(output)]), 1)
            result = json.loads(output.read_text())
            self.assertTrue(result["centered"]["covered"])
            self.assertFalse(result["anchors_ok"])
            self.assertEqual(result["status"], "STRIP-CONTROL-FAIL")


if __name__ == "__main__":
    unittest.main()
