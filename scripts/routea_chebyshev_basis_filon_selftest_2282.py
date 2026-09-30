"""2282 focused controls."""
import json
import unittest
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
class ChebyshevFilonTests(unittest.TestCase):
    def test_profile_is_untrusted(self):
        artifact=json.loads((ROOT/'results/2282_chebyshev_basis_filon_screen.json').read_text())
        self.assertEqual(artifact['trust_status'],'CHEBYSHEV-MP-UNTRUSTED')
        self.assertGreater(artifact['profile_refinement'][1]['max_corr_relative_change'],100.0)
    def test_nonclaims(self):
        artifact=json.loads((ROOT/'results/2282_chebyshev_basis_filon_screen.json').read_text())
        self.assertFalse(artifact['certificate'])
        self.assertIn('high precision is not a directed interval enclosure',artifact['nonclaims'])
if __name__=='__main__': unittest.main()
