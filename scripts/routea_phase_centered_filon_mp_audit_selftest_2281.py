"""2281 focused controls."""
import json
import unittest
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]

class FilonMPAuditTests(unittest.TestCase):
    def test_corrected_audit_is_float_consistent(self):
        artifact=json.loads((ROOT/'results/2281_phase_centered_filon_mp_audit.json').read_text())
        self.assertEqual(artifact['status'],'FILON-FLOAT-ARITHMETIC-AUDIT')
        self.assertLess(artifact['max_base_relative_error'],1e-5)
        self.assertLess(artifact['max_corr_relative_error'],1e-5)
    def test_nonclaims(self):
        artifact=json.loads((ROOT/'results/2281_phase_centered_filon_mp_audit.json').read_text())
        self.assertFalse(artifact['certificate'])
        self.assertIn('mpmath high precision is not directed interval proof',artifact['nonclaims'])

if __name__=='__main__': unittest.main()


