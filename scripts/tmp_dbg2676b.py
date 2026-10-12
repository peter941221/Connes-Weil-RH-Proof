"""Localize the base_M0 escape: float views of my aggregate vs the exported
2675 rectangle vs an mpmath evaluation of the true channel function."""
import importlib.util
import json
import struct
from fractions import Fraction
from pathlib import Path

ROOT = Path("/mnt/c/Projects/Connes-Weil-RH-Proof")


def load_module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    m = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(m)
    return m


scr = load_module("scr2676", ROOT / "scripts/routea_cell4096_containment_2676.py")
probe = load_module("probe2670",
                    ROOT / "scripts/routea_repaired_owner_continuous_box_price_2670.py")
strip = load_module("strip2303",
                    ROOT / "scripts/routea_corrected_strip_envelope_2303.py")

repair = json.loads(probe.REPAIR.read_text())
base, correction = probe.coefficient_arrays(repair["coefficient_rows"])
families, _, _, _ = strip.load_owner()

art = json.loads(
    (ROOT / "results/2675_repaired_owner_cell_price_certificate.json").read_text())
cell = art["cell"]


def bits_to_fraction(bits_hex):
    bits = int(bits_hex, 16)
    return Fraction.from_float(struct.unpack(">d", struct.pack(">Q", bits))[0])


xlo = bits_to_fraction(cell["cell_endpoints"]["x_lo"]["bits"])
xhi = bits_to_fraction(cell["cell_endpoints"]["x_hi"]["bits"])
print("cell:", float(xlo), float(xhi))

exported = {}
for row in cell["channels"]:
    ep = row["rectangle_endpoints"]
    exported[row["name"]] = tuple(
        Fraction(ep[k]["exact"]) for k in ("re_lo", "re_hi", "im_lo", "im_hi"))

width_lean = scr.parse_fin30_rationals(
    ROOT / "ConnesWeilRH/Dev/C1RouteAOwnerScaleAudit.lean", "storedWidth")
theta_lean = scr.parse_fin30_rationals(
    ROOT / "ConnesWeilRH/Dev/C1RouteACorrectionCaptureParameters2584.lean",
    "capturedModulations2584")

_, _, phi_lo_base, phi_hi_pin = scr.exp_pins()
per_family = scr.build_chain(families, base, correction, xhi,
                             theta_lean, width_lean, (phi_lo_base, phi_hi_pin))
k0_base, k2_base = scr.channel_rects(per_family, base)
k0_corr, k2_corr = scr.channel_rects(per_family, correction)

from mpmath import mp, mpf, exp as mexp, mpc
mp.dps = 40


def true_channel(x, coeff, order):
    s = mpc(0)
    for j in range(30):
        r = mpf(width_lean[j]) ** 2
        t = mpf(theta_lean[j])
        u2 = (mpf(x) / r) ** 2
        q = 1 - u2
        phi = mexp(mpf(-30) / q)
        v = mpc(coeff[j].real, coeff[j].imag) * phi * mexp(1j * t * mpf(x))
        if order == 0:
            s += v
        else:
            L1 = -60 * (mpf(x) / r) / (r * q ** 2)
            L2 = (-60 / r ** 2) * (1 / q ** 2 + 4 * (mpf(x) / r) ** 2 / q ** 3)
            s += v * (L2 + L1 * L1 - t * t + 2j * t * L1)
    return s


for name, rects in (("base_M0", k0_base), ("base_D2", k2_base),
                    ("correction_M0", k0_corr), ("correction_D2", k2_corr)):
    coeff = base if name.startswith("base") else correction
    order = 0 if name.endswith("M0") else 2
    agg = scr.aggregate(rects)
    ex = exported[name]
    print(f"== {name}")
    print("  mine   ", [f"{float(v):.9g}" for v in agg])
    print("  theirs ", [f"{float(v):.9g}" for v in ex])
    for x in (xlo, (xlo + xhi) / 2, xhi):
        v = true_channel(x, coeff, order)
        in_mine = (agg[0] <= v.real <= agg[1] and agg[2] <= v.imag <= agg[3])
        in_theirs = (ex[0] <= v.real <= ex[1] and ex[2] <= v.imag <= ex[3])
        print(f"  truth@{float(x):.6g}  re={float(v.real):.9g}  "
              f"im={float(v.imag):.9g}  in_mine={in_mine}  in_theirs={in_theirs}")

print("-- per-family base_M0 rects (re_lo, re_hi, im_lo, im_hi) --")
for j, r in enumerate(k0_base):
    print(f"  j={j:2d} [{float(r[0]):+.6g},{float(r[1]):+.6g}] "
          f"[{float(r[2]):+.6g},{float(r[3]):+.6g}]")
