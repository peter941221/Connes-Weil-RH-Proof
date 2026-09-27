#!/usr/bin/env python3
# diag_2053_loc.py -- DIAGNOSTIC (not committed): localize the interior window mass
# of the committed functional.  Rebuilds the m in {400,1600} profiles on a fine
# grid over [-12,12] and reports per-unit-bin trapezoid integrals of ker*g plus
# the argmax of |ker g| in each bin.  Purpose: the 2053 probe's Q_sym(10) bin
# carries -3.4e12 at BOTH m while every stored sample in [0,10] has g <= 1e-23;
# this script measures where that mass actually lives instead of guessing.
import math, os, sys, time
import numpy as np

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(ROOT, "scripts"))
import fourpoint_owner_completion_1980 as r80
import fourpoint_owner_density_1959 as r59
import routea_g8h_basis_comparison_2037 as r37

K = 30.0
t0 = time.time()
rho, nodes, values, fam, xw, gram, a_mat, _, _ = r37.setup(False)
base, _bi = r37.min_h1(gram, a_mat, np.ones(len(nodes), complex))
corr, _ci = r37.min_h1(gram, a_mat, np.asarray(values, complex))
print("setup done (%.0fs)" % (time.time() - t0), flush=True)


def profile(m_prof, hh, lo, hi):
    xg = np.arange(lo, hi + hh / 2, hh)
    s = 0.5 - 2j * np.pi * xg
    xwm = [r59.phi_weights(a_, panels=6, m=m_prof) for a_, _t in fam]
    v = r80.family_values(fam, K, s, xwm)
    lb = base @ v
    cc = corr @ v
    p = np.real(r59.P_from_nodes(xg, r80.counterpart_nodes(rho)))
    g = p * p * np.abs(lb) ** 2 * np.abs(cc) ** 2
    ker = r59.rig.sigma_vec(2 * np.pi * xg)
    for num, w in r59.rig.prime_powers_up_to(math.exp(9.504)):
        ker = ker + 2 * w / math.sqrt(num) * np.cos(2 * np.pi * xg * math.log(num))
    fx = ker * g
    return xg, g, lb, cc, p, ker, fx


def trap(fx, hh):
    return float(np.sum(0.5 * (fx[1:] + fx[:-1]) * hh))


for m_prof in (1600, 400):
    hh = 0.005
    xg, g, lb, cc, p, ker, fx = profile(m_prof, hh, -12.0, 12.0)
    print("m=%d h=%.4f: Q[-12,12] = %+.6e   max|fx| = %.3e at xi=%+.4f  (%.0fs)"
          % (m_prof, hh, trap(fx, hh), np.max(np.abs(fx)),
             xg[int(np.argmax(np.abs(fx)))], time.time() - t0), flush=True)
    for b0 in range(-12, 12):
        if b0 == 11:
            msk = (xg >= b0) & (xg <= b0 + 1)
        else:
            msk = (xg >= b0) & (xg < b0 + 1)
        xb, fb, gb = xg[msk], fx[msk], g[msk]
        qb = trap(fb, hh) if len(fb) > 1 else 0.0
        i2 = int(np.argmax(gb))
        print("   bin [%+3d,%+3d): Q=%+.4e  max|fx|=%.3e  max g=%.3e at xi=%+.4f"
              "  (|lb|=%.2e |cc|=%.2e p=%.2e ker=%.3f)"
              % (b0, b0 + 1, qb, np.max(np.abs(fb)), gb[i2], xb[i2],
                 abs(lb[msk][i2]), abs(cc[msk][i2]), abs(p[msk][i2]), ker[msk][i2]),
              flush=True)

# fine pass over the m=1600 argmax unit bin
xg, g, lb, cc, p, ker, fx = profile(1600, 0.005, -12.0, 12.0)
b0 = int(math.floor(xg[int(np.argmax(np.abs(fx)))]))
print("fine scan of bin [%+d,%+d] at h=0.0005 ..." % (b0, b0 + 1), flush=True)
xg2, g2, lb2, cc2, p2, ker2, fx2 = profile(1600, 0.0005, float(b0), float(b0 + 1))
i2 = int(np.argmax(np.abs(fx2)))
print("   Q = %+.6e   max|fx| = %.3e at xi=%.5f  (|lb|=%.2e |cc|=%.2e p=%.2e ker=%.3f)"
      % (trap(fx2, 0.0005), np.max(np.abs(fx2)), xg2[i2],
         abs(lb2[i2]), abs(cc2[i2]), abs(p2[i2]), ker2[i2]), flush=True)
print("done (%.0fs)" % (time.time() - t0), flush=True)