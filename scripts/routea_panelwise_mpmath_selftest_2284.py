"""2284 focused controls."""
import json
import unittest
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
class PanelwiseMpmathTests(unittest.TestCase):
    def test_precision_instability_is_recorded(self):
        artifact=json.loads((ROOT/'results/2284_panelwise_mpmath_audit.json').read_text())
        self.assertEqual(artifact['trust_status'],'PANELWISE-MP-UNTRUSTED')
        self.assertGreater(artifact['base_precision_movement'],1e10)
        self.assertGreater(artifact['corr_precision_movement'],1e10)
    def test_panel_scale_exposes_false_cancellation(self):
        artifact=json.loads((ROOT/'results/2284_panelwise_mpmath_audit.json').read_text())
        self.assertGreater(artifact['base'][0]['panel_abs_max'],1e-2)
        self.assertGreater(artifact['corr'][0]['panel_abs_max'],1e-2)
if __name__=='__main__': unittest.main()
