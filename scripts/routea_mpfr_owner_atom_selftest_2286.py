"""2286 focused controls; runtime backend is exercised in WSL."""
import json
import unittest
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
class MpfrAtomPreflightTests(unittest.TestCase):
    def test_backend_and_scope(self):
        artifact=json.loads((ROOT/'results/2286_mpfr_owner_atom_preflight.json').read_text())
        self.assertEqual(artifact['status'],'MPFR-DIRECTED-OWNER-ATOM-PREFLIGHT')
        self.assertEqual(artifact['backend']['rounding'],'RNDD/RNDU')
        self.assertEqual(artifact['owner']['prime_power_count'],41136)
    def test_finite_atom_radii(self):
        artifact=json.loads((ROOT/'results/2286_mpfr_owner_atom_preflight.json').read_text())
        self.assertLess(artifact['max_base_radius'],1e-10)
        self.assertLess(artifact['max_corr_radius'],1e-7)
        self.assertTrue(all(row['base_finite'] and row['corr_finite'] for row in artifact['rows']))
if __name__=='__main__': unittest.main()
