"""2445 independent replay controls."""

import json
from fractions import Fraction
import unittest
from pathlib import Path

import mpmath as mp

import routea_family_endpoint_independent_replay_2445 as replay

ROOT = Path(__file__).resolve().parents[1]
RESULT = ROOT / "results/2445_routea_family_endpoint_independent_replay.json"


class IndependentReplayTests(unittest.TestCase):
    def test_all_terms_are_contained(self):
        result = json.loads(RESULT.read_text(encoding="utf-8"))
        self.assertEqual(result["status"], "INDEPENDENT-MPMATH-CONTAINMENT-REPLAY")
        self.assertEqual(result["checked_terms"], 540)
        self.assertEqual(result["failure_count"], 0)
        self.assertTrue(result["source_hashes_verified"])

    def test_position_is_exact_binary64(self):
        with mp.workdps(80):
            value = 0.1
            exact = Fraction.from_float(value)
            lifted = replay.lift_stored_position(value)
            self.assertEqual(lifted, mp.mpf(exact.numerator) / exact.denominator)
            self.assertNotEqual(lifted, mp.mpf(str(value)))

    def test_changed_source_hash_is_rejected(self):
        artifact = json.loads(replay.ARTIFACT.read_text(encoding="utf-8"))
        artifact["source_sha256"]["scripts/routea_family_endpoint_certificate_2445.py"] = "0" * 64
        with self.assertRaisesRegex(ValueError, "source hash differs"):
            replay.validate_artifact_sources(artifact)

    def test_missing_backend_hash_is_rejected(self):
        artifact = json.loads(replay.ARTIFACT.read_text(encoding="utf-8"))
        del artifact["source_sha256"]["scripts/routea_mpfr_owner_atom_preflight_2286.py"]
        with self.assertRaisesRegex(ValueError, "missing a required source hash"):
            replay.validate_artifact_sources(artifact)

    def test_owner_capture_hash_is_rejected(self):
        artifact = json.loads(replay.ARTIFACT.read_text(encoding="utf-8"))
        artifact["owner"]["capture_sha256"] = "0" * 64
        with self.assertRaisesRegex(ValueError, "owner capture hash differs"):
            replay.validate_artifact_sources(artifact)


if __name__ == "__main__":
    unittest.main()
