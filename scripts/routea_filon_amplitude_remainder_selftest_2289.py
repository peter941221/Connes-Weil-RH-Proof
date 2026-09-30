"""2289 focused controls."""
import json
import unittest
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
class FilonAmplitudeRemainderTests(unittest.TestCase):
    def test_candidate_profile_is_below_raw_gap_budget(self):
        artifact=json.loads((ROOT/'results/2289_filon_amplitude_remainder_price.json').read_text())
        self.assertEqual(artifact['status'],'FILON-AMPLITUDE-REMAINDER-PRICE')
        self.assertLess(artifact['best_base_price']+artifact['best_corr_price'],1e7)
    def test_no_certificate_claim(self):
        artifact=json.loads((ROOT/'results/2289_filon_amplitude_remainder_price.json').read_text())
        self.assertFalse(artifact['certificate'])
        self.assertIn('sampled amplitude derivatives are not uniform bounds',artifact['nonclaims'])
if __name__=='__main__': unittest.main()
