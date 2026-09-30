"""2283 focused controls."""
import json
import unittest
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
class FilonResidualPriceTests(unittest.TestCase):
    def test_residual_price_is_large(self):
        artifact=json.loads((ROOT/'results/2283_filon_residual_derivative_price.json').read_text())
        row=artifact['rows'][-1]
        self.assertGreater(row['base']['interpolation_integral_bound'],1e8)
        self.assertGreater(row['corr']['interpolation_integral_bound'],1e7)
    def test_nonclaims(self):
        artifact=json.loads((ROOT/'results/2283_filon_residual_derivative_price.json').read_text())
        self.assertFalse(artifact['certificate'])
        self.assertIn('sampled derivative maxima are not uniform derivative enclosures',artifact['nonclaims'])
if __name__=='__main__': unittest.main()
