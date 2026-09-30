"""2288 focused controls."""
import json
import unittest
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
class GlRemainderPriceTests(unittest.TestCase):
    def test_price_is_far_above_budget(self):
        artifact=json.loads((ROOT/'results/2288_gl_remainder_price.json').read_text())
        self.assertEqual(artifact['status'],'GL-REMAINDER-SAMPLED-PRICE')
        self.assertGreater(artifact['max_base_price'],1e30)
        self.assertGreater(artifact['max_corr_price'],1e30)
    def test_nonclaims(self):
        artifact=json.loads((ROOT/'results/2288_gl_remainder_price.json').read_text())
        self.assertFalse(artifact['certificate'])
        self.assertIn('sampled derivative maxima are not uniform bounds',artifact['nonclaims'])
if __name__=='__main__': unittest.main()
