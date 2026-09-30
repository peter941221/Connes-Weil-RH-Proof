"""2290 focused controls."""
import json
import unittest
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
class FifthDerivativeSamplingTests(unittest.TestCase):
    def test_sampling_refinement_stays_candidate_scale(self):
        artifact=json.loads((ROOT/'results/2290_filon_fifth_derivative_sampling.json').read_text())
        base=[row['base']['amplitude_remainder_price'] for row in artifact['rows']]
        corr=[row['corr']['amplitude_remainder_price'] for row in artifact['rows']]
        self.assertLess(base[-1]+corr[-1],1e7)
        self.assertLess(base[-1]/base[0],2.0)
        self.assertLess(corr[-1]/corr[0],1.1)
    def test_nonclaims(self):
        artifact=json.loads((ROOT/'results/2290_filon_fifth_derivative_sampling.json').read_text())
        self.assertFalse(artifact['certificate'])
        self.assertIn('sampled maxima are not uniform derivative enclosures',artifact['nonclaims'])
if __name__=='__main__': unittest.main()
