"""2291 focused controls."""
import json
import unittest
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
class GroupedFamilywiseTests(unittest.TestCase):
    def test_familywise_loss_is_binding(self):
        artifact=json.loads((ROOT/'results/2291_filon_grouped_vs_familywise_price.json').read_text())
        self.assertGreater(artifact['familywise_to_grouped']['corr'],3000)
        self.assertGreater(artifact['familywise_to_grouped']['base'],3)
    def test_nonclaims(self):
        artifact=json.loads((ROOT/'results/2291_filon_grouped_vs_familywise_price.json').read_text())
        self.assertFalse(artifact['certificate'])
        self.assertIn('familywise price is a feasibility comparison, not a certificate',artifact['nonclaims'])
if __name__=='__main__': unittest.main()
