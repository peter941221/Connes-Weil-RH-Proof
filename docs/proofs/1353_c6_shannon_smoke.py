# 1353 C6 smoke (MODEL grade; NO branch, NO verdict band, law 42 not engaged:
# this is a correction-audit illustration for record 1353, not a preregistered
# measurement). Nothing here certifies anything about the gate or RH.
#
# Claim under test (from record 1353 s2): the sampling information a SET of
# zero-height nodes carries about G = laplaceAt g (band-limited to [-sigma,sigma])
# is governed by the Beurling/paley-wiener uncertainty relation
#
#     N_eff(interval of width L) ~= sigma * L / pi,
#
# which is the number of eigenvalues > 1/2 of the time-limiting o band-limiting
# (Slepian/prolate) operator on that interval. We measure the top eigenvalue
# lambda_1 and the >1/2 count for (a) a tiny cluster interval J, (b) the off-
# line spread set I\J, (c) the full window I, for BOTH committed sigma values:
# the full prime-free class sigma = log 2 (window W = pi/sigma) and the realized
# bump-net class sigma = 0.33657359027997263.
#
# Expected (prediction locked HERE, before running):
#   N_eff(J) << 1 with lambda_1 ~ sigma*|J|/pi  => cluster carries ~zero info;
#   N_eff(I) = 1 exactly (W := pi/sigma)        => window is at criticality;
#   ratio info(spread in I\J) / info(cluster in J) = (|I|-|J|)/|J| >> 1.
import math

import numpy as np

SIGMAS = {
    "full-class": math.log(2.0),
    "realized":   0.33657359027997263,
}
W_CLUSTER = 0.05          # adversary's on-line cluster interval J
N = 4000                  # grid points per interval (midpoint rule)


def prolate_spectrum(sigma: float, length: float, n: int = N):
    """Eigenvalues of the band-limit sigma + time-limit [0,length] operator.

    Kernel k(x-y) = sin(sigma*(x-y)) / (pi*(x-y)) (the reproducing kernel of
    the Paley-Wiener space PW_sigma), discretized on the interval with
    midpoint weights h: M_ij = h * k(x_i - x_j). Symmetric by construction.
    """
    h = length / n
    x = (np.arange(n) + 0.5) * h
    d = x[:, None] - x[None, :]
    with np.errstate(invalid="ignore", divide="ignore"):
        k = np.where(np.abs(d) < 1e-300, sigma / math.pi,
                     np.sin(sigma * d) / (math.pi * d))
    return np.linalg.eigvalsh(h * k)[::-1]  # descending


for name, sigma in SIGMAS.items():
    W = math.pi / sigma
    print(f"== sigma={sigma:.6f}  window W=pi/sigma={W:.4f}  "
          f"pred N_eff(W)=sigma*W/pi={sigma*W/math.pi:.4f}  "
          f"pred N_eff(J)={sigma*W_CLUSTER/math.pi:.6f}")
    for label, length in (("J (cluster)", W_CLUSTER),
                          ("I\\J (spread)", W - W_CLUSTER),
                          ("I (window)", W)):
        ev = prolate_spectrum(sigma, length)
        lam1, cnt = float(ev[0]), int((ev > 0.5).sum())
        pred = sigma * length / math.pi
        print(f"   {label:14s} L={length:8.4f}  lambda_1={lam1:.5f}  "
              f"count(ev>0.5)={cnt}   pred N_eff={pred:.4f}   "
              f"lam1/pred={lam1/max(pred,1e-15):.3f}")
