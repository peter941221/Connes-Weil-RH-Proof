"""Mutation controls for 2337 exact-rational postprocessing."""
import copy
import json
import unittest

from routea_marked_sign_rational_check_2337 import ROOT, get_interval, verify_certificate


class RationalCertificateTests(unittest.TestCase):
    def setUp(self):
        self.artifact = json.loads((ROOT / "results/2337_marked_sign_certificate.json").read_text())

    def test_committed_certificate_passes(self):
        result = verify_certificate(self.artifact)
        self.assertEqual(result["source_target_exclusions"], list(range(8)))
        self.assertEqual(result["status"], "RATIONAL_POSTPROCESS_PASS")

    def test_node_order_mutation_is_rejected(self):
        mutated = copy.deepcopy(self.artifact)
        mutated["mandatory_nodes"].reverse()
        with self.assertRaises(ValueError):
            verify_certificate(mutated)

    def test_forged_capture_hash_is_rejected(self):
        mutated = copy.deepcopy(self.artifact)
        mutated["capture_sha256"] = "0" * 64
        with self.assertRaises(ValueError):
            verify_certificate(mutated)

    def test_zero_base_mutation_breaks_marked_sign(self):
        mutated = copy.deepcopy(self.artifact)
        mutated["mandatory_nodes"][0]["base"]["real"]["lower_exact"] = "0"
        mutated["mandatory_nodes"][0]["base"]["real"]["upper_exact"] = "0"
        with self.assertRaises(ValueError):
            verify_certificate(mutated)

    def test_unsupported_producer_claim_is_rejected(self):
        mutated = copy.deepcopy(self.artifact)
        mutated["producer_go"] = True
        with self.assertRaises(ValueError):
            verify_certificate(mutated)

    def test_reversed_interval_is_rejected(self):
        with self.assertRaises(ValueError):
            get_interval({"lower_exact": "2", "upper_exact": "1"})


if __name__ == "__main__":
    unittest.main()
