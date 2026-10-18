"""Outward complex-rectangle enclosure for the right Cauchy circle."""
import json
import hashlib
from pathlib import Path
from mpmath import iv, mp

iv.dps = 30
mp.dps = 80


def z_of(t):
    a = 2 * t / (1 - t * t)
    e = iv.exp(2 * a)
    return (e - 1) / (e + 1) / t


def h_of(t, z):
    y = t * t
    return (24*y**5*z**3 + 36*y**5*z**2 + 18*y**5*z + 3*y**5
            + 96*y**4*z**3 + 144*y**4*z**2 + 68*y**4*z + 9*y**4
            + 144*y**3*z**3 + 72*y**3*z**2 - 148*y**3*z - 114*y**3
            + 96*y**2*z**3 - 144*y**2*z**2 - 240*y**2*z + 18*y**2
            + 24*y*z**3 - 108*y*z**2 + 50*y*z + 63*y - 4*z + 21)


def abs_upper(value):
    re = value.real
    im = value.imag
    # Keep interval endpoints in arbitrary precision.  Converting to binary64
    # before forming the modulus can round an outward endpoint inward.
    def endpoint(x):
        # ivmpf stores each endpoint as an exact (sign, mantissa, exponent,
        # bit-count) tuple; converting that tuple avoids the interval repr and
        # avoids a binary64 round-trip.
        return mp.mpf(x._mpi_[0])
    re_max = max(abs(endpoint(re.a)), abs(endpoint(re.b)))
    im_max = max(abs(endpoint(im.a)), abs(endpoint(im.b)))
    return mp.sqrt(re_max**2 + im_max**2)


def endpoint_text(x):
    """Serialize an iv endpoint without a binary64 conversion."""
    return mp.nstr(mp.mpf(x._mpi_[0]), 70)


def main():
    rows = []
    cell_rows = []
    radius = iv.mpf("0.05")
    for cells in (64, 256):
        maximum = mp.mpf("0")
        for k in range(cells):
            theta_lo = 2 * 3.141592653589793 * k / cells
            theta_hi = 2 * 3.141592653589793 * (k + 1) / cells
            theta = iv.mpf([theta_lo, theta_hi])
            t = radius * (iv.cos(theta) + 1j * iv.sin(theta))
            value = h_of(t, z_of(t))
            upper = abs_upper(value)
            maximum = max(maximum, upper)
            cell_rows.append({"angle_cells": cells, "cell": k,
                              "theta_lo": repr(theta_lo),
                              "theta_hi": repr(theta_hi),
                              "re_lo": endpoint_text(value.real.a),
                              "re_hi": endpoint_text(value.real.b),
                              "im_lo": endpoint_text(value.imag.a),
                              "im_hi": endpoint_text(value.imag.b),
                              "rigorous_rectangle_upper": mp.nstr(upper, 70)})
        rows.append({"radius": "0.05", "angle_cells": cells,
                     "rigorous_rectangle_upper": mp.nstr(maximum, 70),
                     "order_22_scale": mp.nstr(maximum * (mp.mpf("0.01") / mp.mpf("0.05"))**22, 70)})
    generator_sha256 = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    payload = {"record": 2889, "generator_sha256": generator_sha256, "rows": rows,
               "cell_rows": cell_rows,
               "claims": {"outward_complex_rectangle_enclosure": True,
                          "full_cauchy_remainder_certificate": False},
               "next_target": "integrate the complex-circle bound with a proved Cauchy remainder theorem"}
    out = Path("results/2889_route_b_d4_cauchy_interval.json")
    out.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(payload, indent=2))


if __name__ == "__main__":
    main()
