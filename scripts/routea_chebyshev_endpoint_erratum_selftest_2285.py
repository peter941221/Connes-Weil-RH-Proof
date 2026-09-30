"""2285 erratum controls."""
import json
import unittest
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
class ChebyshevErratumTests(unittest.TestCase):
    def test_endpoint_control(self):
        artifact=json.loads((ROOT/'results/2285_chebyshev_endpoint_erratum.json').read_text())
        self.assertEqual(artifact['unit_control']['old_coefficients'],[0,0,2])
        self.assertEqual(artifact['unit_control']['correct_coefficients'],[0,0,1])
    def test_corrected_claims(self):
        artifact=json.loads((ROOT/'results/2285_chebyshev_endpoint_erratum.json').read_text())
        self.assertLess(artifact['corrected_2281']['max_corr_relative_error'],1e-5)
        self.assertGreater(artifact['corrected_2282']['18_to_24_corr'],100)
if __name__=='__main__': unittest.main()
