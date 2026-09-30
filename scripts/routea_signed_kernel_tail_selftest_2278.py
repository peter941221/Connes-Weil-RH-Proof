"""2278 regression controls."""
import json
import unittest
import routea_signed_kernel_tail_screen_2278 as screen

class TailScreenTests(unittest.TestCase):
    def test_corrected_support_changes_prime_count(self):
        _, families, _, _ = screen.load_owner()
        support = 2 * max(width * width for width, _ in families)
        self.assertGreater(len(screen.rig.prime_powers_up_to(__import__("math").exp(support))), 40000)

    def test_signed_screen_has_frozen_hashes(self):
        artifact = json.loads((screen.ROOT / "results/2278_signed_kernel_tail_screen.json").read_text())
        self.assertEqual(artifact["screen"]["base_md5"], "d461872e14212dcba8efe1874de6f652")
        self.assertEqual(artifact["screen"]["corr_md5"], "c37e16a9dfeb4383c7bab1d23aa59566")

    def test_fft_refinement_fails_closed(self):
        artifact = json.loads((screen.ROOT / "results/2278_signed_kernel_tail_screen.json").read_text())
        self.assertEqual(artifact["refinement"]["trust_status"], "FFT-TAIL-UNTRUSTED")
        self.assertGreater(artifact["refinement"]["signed_relative_change"], 1.0)

    def test_finite_screen_is_not_hgap(self):
        artifact = json.loads((screen.ROOT / "results/2278_signed_kernel_tail_screen.json").read_text())
        self.assertFalse(artifact["certificate"])
        self.assertFalse(artifact["hgap_closed"])

    def test_prime_count_is_recorded(self):
        artifact = json.loads((screen.ROOT / "results/2278_signed_kernel_tail_screen.json").read_text())
        self.assertEqual(artifact["screen"]["prime_power_count"], 41136)

if __name__ == "__main__":
    unittest.main()
