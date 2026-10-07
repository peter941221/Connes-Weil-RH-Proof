"""Negative controls for the 2618 proof-log and exact-width validation."""
import unittest

from validate_analytic_moment_normalization_2618 import describe_width, THEOREMS
from validate_static_coordinate_bounds_2617 import parse_successful_log


class NormalizationValidationTests(unittest.TestCase):
    def test_underflow_width_remains_nonzero(self):
        reading = describe_width({"lower_exact": "0", "upper_exact": f"1/{10 ** 420}"})
        self.assertEqual(reading["width_decimal"], "1E-420")

    def test_subtraction_is_exact(self):
        reading = describe_width({"lower_exact": "1/3", "upper_exact": "1/2"})
        self.assertEqual(reading["width_exact"], "1/6")

    def test_degenerate_width_is_rejected(self):
        with self.assertRaises(ValueError):
            describe_width({"lower_exact": "1/2", "upper_exact": "1/2"})

    def test_reversed_width_is_rejected(self):
        with self.assertRaises(ValueError):
            describe_width({"lower_exact": "1", "upper_exact": "0"})

    def test_multiline_axioms_are_accepted(self):
        text = self.log("propext,\n Classical.choice,\n Quot.sound")
        parse_successful_log(text, f"ConnesWeilRH.Dev.{THEOREMS[-2]}")

    def test_extra_axiom_is_rejected(self):
        text = self.log("propext, Classical.choice, Quot.sound, additionalAxiom")
        with self.assertRaises(ValueError):
            parse_successful_log(text, f"ConnesWeilRH.Dev.{THEOREMS[-2]}")

    def test_interrupted_success_code_is_rejected(self):
        text = self.log("propext, Classical.choice, Quot.sound")
        with self.assertRaises(ValueError):
            parse_successful_log(text + "Command terminated by signal 2\n")

    @staticmethod
    def log(axioms):
        return (f"'ConnesWeilRH.Dev.{THEOREMS[-2]}' depends on axioms: [{axioms}]\n"
                "Elapsed (wall clock) time (h:mm:ss or m:ss): 0:01.20\n"
                "Maximum resident set size (kbytes): 1000\n"
                "Exit status: 0\nRESOURCE_RESULT exit=0\n")


if __name__ == "__main__":
    unittest.main()
