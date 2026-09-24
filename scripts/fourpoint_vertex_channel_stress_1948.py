#!/usr/bin/env python3
"""Stress vertex channel signs beyond the narrow committed bump family."""

import json
import math
import os
import sys

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import fourpoint_diagonal_sign_1918 as rig  # noqa: E402
from fourpoint_gate_kernel_form_1919 import ghat_grid, kernel_grid  # noqa: E402


OUT = "results/1948_fourpoint_vertex_channel_stress.json"


def main():
    rows = []
    for c in (1.3, 1.6, 2.0, 2.4, 3.0):
        for gamma in (14.134725141734693, 21.022039638771555):
            delta = 0.05
            xi, fh = ghat_grid(rig.bump(c))
            W = (fh * np.conj(fh)).real
            dxi = 1.0 / (rig.NF * rig.DU)
            om = 2.0 * np.pi * xi
            P = (delta * delta + gamma * gamma - om * om) ** 2 \
                + 4.0 * delta * delta * om * om
            sigma = rig.sigma_vec(om)
            K = kernel_grid(xi, 2.0 * c)
            Kp = K - sigma
            C = float(np.sum(K * W) * dxi)
            B = float(np.sum(K * P * W) * dxi)
            D = float(np.sum(K * P * P * W) * dxi)
            lam = B / C
            q = D - 2.0 * lam * B + lam * lam * C
            qa = float(np.sum(sigma * (P - lam) ** 2 * W) * dxi)
            qp = float(np.sum(Kp * (P - lam) ** 2 * W) * dxi)
            rows.append({
                "c": c, "gamma": gamma, "delta": delta,
                "lambda_vertex": lam, "Q_full": q,
                "Q_arch": qa, "Q_prime": qp,
                "identity_residual": q - (qa + qp),
            })
    summary = {
        "case_count": len(rows),
        "full_negative_count": sum(r["Q_full"] < 0 for r in rows),
        "arch_negative_count": sum(r["Q_arch"] < 0 for r in rows),
        "prime_negative_count": sum(r["Q_prime"] < 0 for r in rows),
        "max_arch": max(r["Q_arch"] for r in rows),
        "max_prime": max(r["Q_prime"] for r in rows),
        "max_identity_residual": max(abs(r["identity_residual"]) for r in rows),
    }
    result = {
        "provenance": "1918 FFT rig, 1919 kernel form, vertex lambda=B/C, delta=0.05",
        "summary": summary, "rows": rows,
    }
    os.makedirs(os.path.dirname(OUT), exist_ok=True)
    with open(OUT, "w", encoding="utf-8") as fh:
        json.dump(result, fh, indent=2)
    print(json.dumps(summary, indent=2))
    for row in rows:
        print(row)
    print("wrote", OUT)


if __name__ == "__main__":
    main()
