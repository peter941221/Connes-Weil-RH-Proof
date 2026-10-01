"""Mutation controls for the exact 2344 binding checker."""
import copy
import json
import unittest

import routea_external_owner_binding_2344 as binding


class BindingTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.source = (binding.ROOT / binding.OWNER).read_text(encoding="utf-8")
        cls.families = json.loads((binding.ROOT / binding.CAPTURE).read_text())["owner_capture"]["families_hex"]
        cls.constants = (binding.ROOT / binding.ENDPOINTS).read_text(encoding="utf-8")
        cls.result = json.loads((binding.ROOT / binding.RESULT).read_text())

    def test_exact_widths_and_squares(self):
        rows = binding.check_widths(self.source, self.families)
        self.assertEqual(len(rows), 30)
        for row in rows:
            self.assertEqual(binding.Fraction(row["radius_exact"]), binding.Fraction(row["width_exact"])**2)

    def test_every_width_mutation_rejected(self):
        for index in range(30):
            with self.subTest(index=index):
                changed = copy.deepcopy(self.families)
                changed[index][0] = "0x1.0p+0"
                with self.assertRaises(ValueError):
                    binding.check_widths(self.source, changed)

    def test_reordered_capture_rejected(self):
        changed = copy.deepcopy(self.families)
        changed[0], changed[1] = changed[1], changed[0]
        with self.assertRaises(ValueError):
            binding.check_widths(self.source, changed)

    def test_incomplete_capture_rejected(self):
        with self.assertRaises(ValueError):
            binding.check_widths(self.source, self.families[:-1])

    def test_unparsed_expression_rejected(self):
        changed = self.source.replace("3602879701896397 / 2251799813685248", "1 + 1", 1)
        with self.assertRaises(ValueError):
            binding.parse_widths(changed)

    def test_endpoint_constants_are_outward(self):
        checks = binding.check_constants(self.constants, self.result)
        self.assertEqual(len(checks), 4)
        self.assertTrue(all(binding.Fraction(row["slack_exact"]) > 0 for row in checks))

    def test_each_inward_constant_rejected(self):
        for literal in ("2.7790943782", "9044.9434472", "231.2642026141", "666472.585392"):
            with self.subTest(literal=literal):
                with self.assertRaises(ValueError):
                    binding.check_constants(self.constants.replace(literal, "0", 1), self.result)

    def test_missing_endpoint_rejected(self):
        changed = copy.deepcopy(self.result)
        changed["endpoints"].pop()
        with self.assertRaises(ValueError):
            binding.check_constants(self.constants, changed)


if __name__ == "__main__":
    unittest.main()

