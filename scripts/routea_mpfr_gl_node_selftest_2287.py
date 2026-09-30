"""2287 focused controls."""
import json
import unittest
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
class MpfrGlNodeTests(unittest.TestCase):
    def test_backend_and_guard(self):
        artifact=json.loads((ROOT/'results/2287_mpfr_gl_node_preflight.json').read_text())
        self.assertEqual(artifact['status'],'MPFR-DIRECTED-GL-NODE-PREFLIGHT')
        self.assertEqual(artifact['owner']['prime_power_count'],41136)
        self.assertEqual(artifact['backend']['rounding'],'RNDD/RNDU')
    def test_remainder_is_binding(self):
        artifact=json.loads((ROOT/'results/2287_mpfr_gl_node_preflight.json').read_text())
        self.assertLess(artifact['max_base_radius'],1e-10)
        self.assertLess(artifact['max_corr_radius'],1e-7)
        self.assertGreater(artifact['max_base_mid_relative_change'],4.0)
        self.assertGreater(artifact['max_corr_mid_relative_change'],10.0)
if __name__=='__main__': unittest.main()
