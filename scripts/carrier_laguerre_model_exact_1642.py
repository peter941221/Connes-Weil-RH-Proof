#!/usr/bin/env python3
"""1642: continuous exact model matrix for m=1.

With c=2 log(lambda), multiplication by exp(2*pi*i*c*xi) translates the
inverse Fourier transform.  The selected Hardy-side defect in the probe is
therefore the Gram matrix on (-infinity,c):

  M_ij(c) = integral_{-infinity}^c h_i(y) h_j(y) dy
           = integral_{-c}^infinity exp(-t) L_i(t)L_j(t) dt.

This gives a continuous calibration independent of the FFT half-line
projection.  It is a model control for the actual Gamma multiplier, not a
claim about that multiplier.
"""

import math
import sys

import numpy as np
from scipy.integrate import quad_vec
from scipy.linalg import eigh
from scipy.special import eval_laguerre


def exact_model_matrix(dim, lam):
    a = -2.0 * math.log(lam)

    def integrand(t):
        vals = np.array([eval_laguerre(n, t) for n in range(dim)])
        return math.exp(-t) * np.outer(vals, vals)

    M, err = quad_vec(integrand, a, np.inf, epsabs=1e-13, epsrel=1e-13)
    return 0.5 * (M + M.T), float(np.max(np.abs(err)))


def main():
    print("1642 continuous exact m=1 model")
    print("+--------+------+--------------+--------------+")
    print("| lambda | dim  | sigma_min    | quad error   |")
    print("+--------+------+--------------+--------------+")
    for lam in (0.2, 0.1, 0.05, 0.02):
        for dim in (8, 10, 12, 14):
            M, err = exact_model_matrix(dim, lam)
            vals = np.linalg.eigvalsh(M)
            print("| %6.3f | %4d | %12.4e | %12.4e |" %
                  (lam, dim, math.sqrt(max(float(vals[0]), 0.0)), err))
        print("+--------+------+--------------+--------------+")


if __name__ == "__main__":
    main()
