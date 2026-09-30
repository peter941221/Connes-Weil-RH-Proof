"""2279 direct quadrature trust controls."""
import json
import unittest
import routea_direct_oscillatory_tail_screen_2279 as screen

class DirectQuadratureTests(unittest.TestCase):
    def test_support_uses_current_owner(self):
        _, families, _, _ = screen.load_owner()
        self.assertEqual(len(screen.rig.prime_powers_up_to(__import__("math").exp(2 * max(width * width for width, _ in families)))), 41136)

    def test_main_rule_is_untrusted(self):
        artifact = json.loads((screen.ROOT / "results/2279_direct_oscillatory_tail_screen.json").read_text())
        self.assertEqual(artifact["trust_status"], "DIRECT-GL-TAIL-UNTRUSTED")
        self.assertGreater(artifact["order_refinement"][1]["signed_relative_change"], 10.0)

    def test_high_order_rule_is_untrusted(self):
        artifact = json.loads((screen.ROOT / "results/2279_direct_oscillatory_tail_high_order.json").read_text())
        self.assertEqual(artifact["trust_status"], "DIRECT-GL-TAIL-UNTRUSTED")
        self.assertGreater(artifact["order_refinement"][0]["signed_relative_change"], 4.0)

    def test_nonclaim_flags_remain(self):
        artifact = json.loads((screen.ROOT / "results/2279_direct_oscillatory_tail_screen.json").read_text())
        self.assertFalse(artifact["certificate"])
        self.assertFalse(artifact["hgap_closed"])
        self.assertIn("finite xi range is not the infinite tail", artifact["nonclaims"])

if __name__ == "__main__":
    unittest.main()
