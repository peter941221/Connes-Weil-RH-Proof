"""2276: directed analytic prices for the correctly scaled stored owner.

The script settles two bounded decisions: whether the legacy physical
owner is the 2249 owner, and whether absolute-family majorants can supply
its frozen strip/tail budgets. It is not a detector gap certificate.
"""
import argparse
import ast
import ctypes
from dataclasses import dataclass
from fractions import Fraction
import hashlib
import json
import math
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
INPUTS = (
    "results/2275_gap_owner_audit.json",
    "results/2267_replay_operands.json",
    "scripts/fourpoint_owner_completion_1980.py",
    "scripts/routea_weighted_zero_l1_enclosure_2249.py",
    "scripts/routea_weighted_zero_direct_product_mass_screen_2197.py",
    "scripts/routea_weighted_zero_direct_product_outward_2234.py",
    "scripts/routea_owner_scale_price_2276.py",
    "ConnesWeilRH/Dev/C1RouteAOwnerScaleAudit.lean",
    "ConnesWeilRH/Dev/C1RouteAOwnerScaleAuditAudit.lean",
    "scripts/routea_gap_owner_audit_2275.py",
)


class MpfrStruct(ctypes.Structure):
    _fields_ = [("prec", ctypes.c_long), ("sign", ctypes.c_int),
                ("exp", ctypes.c_long), ("digits", ctypes.POINTER(ctypes.c_ulong))]


class DirectedEngine:
    def __init__(self):
        self.lib = ctypes.CDLL("libmpfr.so.6")
        pointer = ctypes.POINTER(MpfrStruct)
        self.lib.mpfr_init2.argtypes = [pointer, ctypes.c_long]
        self.lib.mpfr_clear.argtypes = [pointer]
        self.lib.mpfr_set_d.argtypes = [pointer, ctypes.c_double, ctypes.c_int]
        self.lib.mpfr_get_d.argtypes = [pointer, ctypes.c_int]
        self.lib.mpfr_get_d.restype = ctypes.c_double
        for name in ("mpfr_add", "mpfr_sub", "mpfr_mul", "mpfr_div"):
            getattr(self.lib, name).argtypes = [pointer, pointer, pointer, ctypes.c_int]
        for name in ("mpfr_exp", "mpfr_sqrt"):
            getattr(self.lib, name).argtypes = [pointer, pointer, ctypes.c_int]
        self.slots = [MpfrStruct() for _ in range(3)]
        for slot in self.slots:
            self.lib.mpfr_init2(ctypes.byref(slot), 256)

    def evaluate(self, name, operands, rounding):
        for slot, operand in zip(self.slots, operands):
            self.lib.mpfr_set_d(ctypes.byref(slot), operand, 0)
        output = ctypes.byref(self.slots[2])
        arguments = [output] + [ctypes.byref(self.slots[index])
                                for index in range(len(operands))] + [rounding]
        getattr(self.lib, name)(*arguments)
        value = float(self.lib.mpfr_get_d(output, rounding))
        if not math.isfinite(value):
            raise ValueError("nonfinite enclosure; no price verdict")
        return value

    def close(self):
        for slot in self.slots:
            self.lib.mpfr_clear(ctypes.byref(slot))


ENGINE = None


@dataclass(frozen=True)
class Interval:
    lo: float
    hi: float

    def __post_init__(self):
        if not math.isfinite(self.lo) or not math.isfinite(self.hi) or self.lo > self.hi:
            raise ValueError("invalid interval")

    @staticmethod
    def exact(value):
        rational = Fraction(value)
        approximate = float(rational)
        if not math.isfinite(approximate):
            raise ValueError("rational is outside binary64 enclosure range")
        lifted = Fraction(approximate)
        return Interval(math.nextafter(approximate, -math.inf) if lifted > rational else approximate,
                        math.nextafter(approximate, math.inf) if lifted < rational else approximate)

    def binary(self, other, operation):
        other = other if isinstance(other, Interval) else Interval.exact(other)
        if operation == "mpfr_div" and other.lo <= 0 <= other.hi:
            raise ValueError("division interval contains zero")
        pairs = [(left, right) for left in (self.lo, self.hi)
                 for right in (other.lo, other.hi)]
        return Interval(min(ENGINE.evaluate(operation, pair, 3) for pair in pairs),
                        max(ENGINE.evaluate(operation, pair, 2) for pair in pairs))

    def __add__(self, other):
        return self.binary(other, "mpfr_add")

    def __sub__(self, other):
        return self.binary(other, "mpfr_sub")

    def __mul__(self, other):
        return self.binary(other, "mpfr_mul")

    def __truediv__(self, other):
        return self.binary(other, "mpfr_div")

    def power(self, order):
        if order < 0:
            raise ValueError("power must be nonnegative")
        value = Interval.exact(1)
        for _ in range(order):
            value = value * self
        return value

    def unary(self, operation):
        if operation == "mpfr_sqrt" and self.lo < 0:
            raise ValueError("negative sqrt interval")
        return Interval(ENGINE.evaluate(operation, (self.lo,), 3),
                        ENGINE.evaluate(operation, (self.hi,), 2))

    def pair(self):
        return [self.lo, self.hi]


def stored_rational(value):
    return Fraction.from_float(float.fromhex(value))


def coefficient_norm(parts):
    real, imaginary = (Interval.exact(stored_rational(part)) for part in parts)
    return (real * real + imaginary * imaginary).unary("mpfr_sqrt")


def source_controls():
    old = (ROOT / INPUTS[2]).read_text()
    screen = (ROOT / INPUTS[4]).read_text()
    outward = (ROOT / INPUTS[5]).read_text()
    discrete = (ROOT / INPUTS[3]).read_text()
    return {
        "frequency_dilates_again": "a * r59.phi_laplace(a, k, a * (s + 1j * th), XW=XW[j])" in old,
        "screen_uses_unsquared_width": "u = x / a" in screen,
        "outward_uses_unsquared_width": "wb.set(wb.push(), a))" in outward
            and "u = wb.div(wb.push(), wb.set(wb.push(), xv)" in outward,
        "visible_cutoff_uses_legacy_support": "support = 2 * max(pair[0] for pair in fam)" in discrete,
        "annihilator_uses_centered_orbit": "return [rho - 0.5, (1 - np.conj(rho)) - 0.5," in old
            and "np.conj(rho) - 0.5, (1 - rho) - 0.5]" in old,
    }


def norm_majorant(families, coefficients, derivative_order, weighted_transform=False):
    total = Interval.exact(0)
    for (width_hex, theta_hex), coefficient in zip(families, coefficients):
        width = stored_rational(width_hex)
        radius = Interval.exact(width * width)
        theta = Interval.exact(abs(stored_rational(theta_hex)))
        if weighted_transform:
            theta = theta + Fraction(1, 2)
        base = (Interval.exact(-30) + radius / 2).unary("mpfr_exp") * radius * 2
        first = Interval.exact(60) / radius
        second = Interval.exact(3900) / radius.power(2)
        third = Interval.exact(272160) / radius.power(3)
        if derivative_order == 0:
            polynomial = Interval.exact(1)
        elif derivative_order == 2:
            polynomial = second + theta * first * 2 + theta.power(2)
        elif derivative_order == 3:
            polynomial = (third + theta * second * 3
                          + theta.power(2) * first * 3 + theta.power(3))
        else:
            raise ValueError("unsupported derivative order")
        total = total + coefficient_norm(coefficient) * base * polynomial
    return total


def build_price():
    global ENGINE
    controls = source_controls()
    if not all(controls.values()):
        raise ValueError("owner source control changed")
    audit = json.loads((ROOT / INPUTS[0]).read_text())
    capture = audit["owner_capture"]
    import routea_gap_owner_audit_2275 as gap_owner
    baseline = json.loads((ROOT / "results/2249_l1_enclosure.json").read_text())["diagnostics"]
    gap_owner.verify_capture(capture, baseline)
    if audit["input_sha256"] != gap_owner.build_audit(capture)["input_sha256"]:
        raise ValueError("2249 input provenance changed")
    replay = json.loads((ROOT / INPUTS[1]).read_text())
    if capture["families_hex"] != replay["families_hex"]:
        raise ValueError("family alignment control failed")
    families = capture["families_hex"]
    widths = [stored_rational(pair[0]) for pair in families]
    assignments = {node.targets[0].id: ast.literal_eval(node.value)
                   for node in ast.parse((ROOT / INPUTS[3]).read_text()).body
                   if isinstance(node, ast.Assign) and isinstance(node.targets[0], ast.Name)
                   and node.targets[0].id in ("K", "GAMMA", "DELTA")}
    if assignments["K"] != 30:
        raise ValueError("bump order changed")
    orbit_cap = (abs(Fraction.from_float(assignments["GAMMA"]))
                 + abs(Fraction.from_float(0.5 + assignments["DELTA"]) - Fraction(1, 2)))
    if orbit_cap >= 40:
        raise ValueError("annihilator factor cap failed")
    if len(widths) != 30 or [index for index, width in enumerate(widths) if width * width > 6] != [4]:
        raise ValueError("unique surviving-family control failed")
    if any(width >= 6 for width in widths):
        raise ValueError("legacy zero-support control failed")
    ENGINE = DirectedEngine()
    try:
        norms = {}
        for side in ("base", "corr"):
            coefficients = capture[side + "_hex"]
            for order in (0, 2):
                norms[side + "_D" + str(order)] = norm_majorant(families, coefficients, order)
            norms[side + "_weighted_D3"] = norm_majorant(families, coefficients, 3, True)
        products = [norms["base_D2"] * norms["corr_D0"],
                    norms["corr_D2"] * norms["base_D0"]]
        strip_expression = Interval(min(value.lo for value in products),
                                    min(value.hi for value in products))
        radius = Interval.exact(widths[4] ** 2)
        bump_at_six = (Interval.exact(-30) /
                       (Interval.exact(1) - (Interval.exact(6) / radius).power(2))).unary("mpfr_exp")
        support_witness = {side: (coefficient_norm(capture[side + "_hex"][4]) * bump_at_six).pair()
                           for side in ("base", "corr")}
        if any(pair[0] <= 0 for pair in support_witness.values()):
            raise ValueError("nonzero corrected-owner witness not enclosed away from zero")
        cutoff = (Interval.exact(2 * widths[4])).unary("mpfr_exp")
        if cutoff.hi >= 168:
            raise ValueError("visible-prime cutoff certificate failed")
        prime_bound = 167 * 168
        tail_factor = (Interval.exact(9).power(8) / Interval.exact(6).power(12)
                       * 2 * (Interval.exact(8 + prime_bound) / (3 * 40 ** 3)
                              + Interval.exact(1152) / 40))
        tail_expression = (tail_factor * norms["base_weighted_D3"].power(2)
                           * norms["corr_weighted_D3"].power(2))
        frozen_strip = Interval.exact(Fraction("9506275.102584327"))
        frozen_gap = 10000000
        ratios = {"strip": (strip_expression / frozen_strip).pair(),
                  "ideal_tail": (tail_expression / frozen_gap).pair()}
        status = "ABSOLUTE-FAMILY-METHOD-REJECTED" if (
            strip_expression.lo > frozen_strip.hi and tail_expression.lo > frozen_gap
        ) else "REQUIRES-REVIEW"
        return {
            "record": 2276,
            "owner_status": "LEGACY-STRIP-OWNER-MISMATCH",
            "price_status": status,
            "hgap_closed": False,
            "source_controls": controls,
            "unique_surviving_family_at_six": 4,
            "legacy_base_and_corr_at_six_exact": "0",
            "corrected_magnitude_at_six_enclosures": support_witness,
            "legacy_max_radius_exact": str(widths[4]),
            "corrected_max_radius_exact": str(widths[4] ** 2),
            "coefficient_component_mismatches": {
                side: sum(value != other for pair, other_pair in zip(capture[side + "_hex"],
                          replay[side + "_hex"]) for value, other in zip(pair, other_pair))
                for side in ("base", "corr")},
            "norm_upper_expression_enclosures": {name: value.pair() for name, value in norms.items()},
            "strip_upper_expression_enclosure": strip_expression.pair(),
            "ideal_tail_upper_expression_enclosure": tail_expression.pair(),
            "method_price_ratios": ratios,
            "visible_cutoff_enclosure": cutoff.pair(),
            "annihilator_node_l1_cap_exact": str(orbit_cap),
            "prime_channel_abs_upper": prime_bound,
            "tail_scope": "ideal same-stored-coefficient transform with the frozen visible-prime kernel; not an actual selected-detector readback",
            "enclosure_scope": "intervals enclose analytic majorant expressions, not lower bounds on the true norms or tail",
            "input_sha256": {path: hashlib.sha256((ROOT / path).read_bytes()).hexdigest() for path in INPUTS},
            "nonclaims": ["the actual ideal gap is not bounded here",
                          "the true norms/tail need not exceed the frozen budgets",
                          "the generic Lean producer theorem remains valid",
                          "no producer GO or RH claim"],
        }
    finally:
        ENGINE.close()
        ENGINE = None


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=ROOT / "results/2276_owner_scale_price.json")
    args = parser.parse_args()
    result = build_price()
    args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(result["owner_status"])
    print(result["price_status"])
    print(json.dumps(result["method_price_ratios"]))


if __name__ == "__main__":
    main()
