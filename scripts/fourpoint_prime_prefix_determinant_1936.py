#!/usr/bin/env python3
"""Record 1936: finite visible-prime prefix screen for the four-point determinant.

This is a cutoff-selection probe only.  It asks whether a short initial
visible prime-power prefix already gives the negative prime-channel determinant
on the committed model cases; the remaining kernel is retained for a future
explicit tail certificate.
"""

import importlib.util
import json
import math
import os
import sys

import numpy as np


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    mod = importlib.util.module_from_spec(spec)
    sys.modules[name] = mod
    spec.loader.exec_module(mod)
    return mod


HERE = os.path.dirname(os.path.abspath(__file__))
rig = load("fourpoint_diagonal_sign_1918", os.path.join(HERE, "fourpoint_diagonal_sign_1918.py"))
ker = load("fourpoint_gate_kernel_form_1919", os.path.join(HERE, "fourpoint_gate_kernel_form_1919.py"))


def main():
    with open("results/1918_fourpoint_diagonal_sign_certified.json") as fh:
        cert = json.load(fh)
    tags = [c["tag"] for c in cert["cases"] if c["c"] in (1.3, 2.0, 3.0)]
    rows = []
    for tag in tags:
        case = next(c for c in cert["cases"] if c["tag"] == tag)
        c = case["c"]
        delta, gamma = case["rho"][0] - 0.5, case["rho"][1]
        xi, Fh = ker.ghat_grid(rig.bump(c))
        W = (Fh * np.conj(Fh)).real
        dxi = 1.0 / (rig.NF * rig.DU)
        om = 2.0 * np.pi * xi
        P = (delta * delta + gamma * gamma - om * om) ** 2 + 4 * delta * delta * om * om
        terms = rig.prime_powers_up_to(math.exp(2.0 * c))
        K = np.zeros_like(xi)
        sigma = rig.sigma_vec(om)
        first_negative = None
        first_full_negative = None
        dets = []
        full_dets = []
        for j, (n, lam) in enumerate(terms, 1):
            K = K + 2.0 * lam / math.sqrt(n) * np.cos(2.0 * np.pi * xi * math.log(n))
            A = float(np.sum(K * W) * dxi)
            B = float(np.sum(K * P * W) * dxi)
            D = float(np.sum(K * P * P * W) * dxi)
            det = D * A - B * B
            dets.append(det)
            Kfull = sigma + K
            Af = float(np.sum(Kfull * W) * dxi)
            Bf = float(np.sum(Kfull * P * W) * dxi)
            Df = float(np.sum(Kfull * P * P * W) * dxi)
            det_full_prefix = Df * Af - Bf * Bf
            full_dets.append(det_full_prefix)
            if first_negative is None and det < 0:
                first_negative = j
            if first_full_negative is None and det_full_prefix < 0:
                first_full_negative = j
        full = dets[-1] if dets else 0.0
        full_total = full_dets[-1] if full_dets else 0.0
        rows.append({"tag": tag, "terms": len(terms), "first_negative_prefix": first_negative,
                     "first_full_negative_prefix": first_full_negative,
                     "det_prefix": dets, "det_full": full,
                     "full_det_prefix": full_dets, "full_det": full_total})
        print(f"{tag}: prime_first={first_negative} full_first={first_full_negative} "
              f"prime_full={full:.6e} full_full={full_total:.6e}", flush=True)
    os.makedirs("results", exist_ok=True)
    with open("results/1936_fourpoint_prime_prefix_determinant.json", "w") as fh:
        json.dump(rows, fh, indent=1)
    print("wrote results/1936_fourpoint_prime_prefix_determinant.json", flush=True)


if __name__ == "__main__":
    main()
