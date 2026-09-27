#!/usr/bin/env python3
# routea_interval_kernel_2043.py — record 2043 (probe, verdict rules fixed
# before the run)
#
# RECORD 2041 LINK L2: per-panel interval enclosure of the signed Weil kernel
#
#   ker(xi) = sigma_arch(2 pi xi)
#             + sum_{k in book} 2*Lambda(k)/sqrt(k) * cos(2 pi xi log k)
#
# on the one-copy G8-H owner (rho = 0.6 + 40.9187190121475 i, scale 0.88,
# support radius 9.504, book = 1647 prime powers, record 2037).  The float
# side mirrors routea_g8h_basis_comparison_2037.qmat term for term
# (r59.rig.sigma_vec, r59.rig.prime_powers_up_to, r80.counterpart_nodes).
#
# S1 (interval sigma): sigma(u) = log pi - Re psi(1/4 - i u /2) in the
# committed 8-shift Stirling form, realized in rectangular complex interval
# arithmetic (only y^2 and y^2-combinations enter, so evenness in u is exact
# and negative panels need no mirroring):
#
#   psi(z) = psi(z+8) - sum_{j<8} 1/(z+j)
#   psi(w) = log w - 1/(2w) - sum_{n=1..6} B_{2n}/(2n w^{2n}) + R,
#   |R| <= (B_14/14)/|w|^14 for Re w > 0  (next-term bound in the right
#   half-plane; B_14/14 = 1/12, |w| >= 8.25 gives |R| <= 3.97e-15).
#
# Anchors: the interval sigma must CONTAIN the committed float
# r59.rig.sigma_vec at u in {0, 2 pi, 20 pi, 80 pi} (sigma(0) ~ 5.37).
#
# VERDICT RULES (record 2041, frozen before the run):
#
#   L2-WIDTH-OK   : kernel-side projected total width
#                     sum_panels width(ker panel) * g(panel) * dxi
#                   < 1e19  (10% of |Q| ~ 1.11e20) at the finest dxi,
#                   anchors contained.
#   L2-WIDTH-FAIL : projection > 1.11e20 at EVERY registered dxi,
#                   or an anchor misses containment (soundness defect).
#   otherwise     : L2-WIDTH-GRAY (refine before deciding).
#
# The projection uses float g = p^2 |lb|^2 |corr.v|^2 from the committed
# 2037 pipeline on the same grid; the h/p enclosure slack is link L1/L3
# business and is NOT counted here (kernel-side lower bound on the
# achievable total width).
#
# Nyquist print per AGENTS.md §5: book max log k = log(13383) ~ 9.20;
# per-panel oscillatory argument width = 2 pi dxi log k (<= 0.578 at
# dxi 0.01).  The panel ENCLOSURE is exact interval arithmetic, so the
# Nyquist defect of the float grid does not apply to the width reading.

import json, math, os, sys, time
import numpy as np
import mpmath as mp

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(ROOT, "scripts"))

import fourpoint_owner_completion_1980 as r80  # noqa: E402
import fourpoint_owner_density_1959 as r59     # noqa: E402
import routea_g8h_basis_comparison_2037 as r37  # noqa: E402

mp.iv.dps = 20
XI_MAX = 40.0
LADDER = (0.05, 0.02, 0.01)

BERNOULLI = [mp.mpf(1) / 12, -mp.mpf(1) / 120, mp.mpf(1) / 252,
             -mp.mpf(1) / 240, mp.mpf(1) / 132, mp.mpf(-691) / 32760]
# interval copies: a plain mpf on the LEFT of an ivmpf operand makes the mpf
# context try to convert a nonzero-width interval -> ValueError; keep every
# coefficient inside the iv context instead
BERNOULLI_IV = [mp.iv.mpf(c) for c in BERNOULLI]
REM = (mp.mpf(1) / 12) / mp.power(mp.mpf('8.25'), 14)   # <= 3.97e-15


def sigma_arch_iv(u):
    """sigma(u) = log pi - Re psi(1/4 - i u/2); u an iv.mpf interval.

    Rectangular complex interval arithmetic, w = z + 8 with z = 1/4 - i u/2.
    """
    iv = mp.iv
    x = iv.mpf(mp.mpf('8.25'))                  # Re w (exact)
    y = u / 2
    y2 = y * y
    m2 = x * x + y2                             # |w|^2 >= 8.25^2 > 0
    two = iv.mpf(2)
    re_psi = iv.log(m2) / two - x / (two * m2)  # Re[log w - 1/(2w)]
    # w^2 (rectangular); the Bernoulli ladder runs over EVEN powers w^{-2n}
    w2_re = x * x - y2
    w2_im = two * x * y
    pw_re, pw_im = w2_re, w2_im                 # holds w^{2n}, n = 1..
    for c in BERNOULLI_IV:
        pw2 = pw_re * pw_re + pw_im * pw_im
        re_psi = re_psi - (pw_re / pw2) * c
        nre = pw_re * w2_re - pw_im * w2_im     # advance w^{2n} -> w^{2n+2}
        nim = pw_re * w2_im + pw_im * w2_re
        pw_re, pw_im = nre, nim
    xq = iv.mpf(mp.mpf('0.25'))
    for j in range(8):
        xj = xq + iv.mpf(j)
        re_psi = re_psi - xj / (xj * xj + y2)   # subtract Re 1/(z+j)
    logpi = iv.log(iv.pi)
    sig_lo = logpi - (re_psi + REM)             # sigma = log pi - Re psi
    sig_hi = logpi - (re_psi - REM)
    return iv.mpf([mp.mpf(sig_lo.a), mp.mpf(sig_hi.b)])


def float_kernel_and_g(xi, fam, xw, base, corr, rho, ps):
    """The committed 2037 float path (qmat kernel + g) on one xi grid."""
    s = .5 - 2j * np.pi * xi
    v = r80.family_values(fam, r37.K, s, xw)
    lb = base @ v
    p = np.real(r59.P_from_nodes(xi, r80.counterpart_nodes(rho)))
    g = p * p * np.abs(lb) ** 2 * np.abs(corr @ v) ** 2
    ker = r59.rig.sigma_vec(2 * np.pi * xi)
    for num, w in ps:
        ker = ker + 2 * w / math.sqrt(num) * np.cos(2 * np.pi * xi * math.log(num))
    return ker, g


def main():
    iv = mp.iv
    smoke = "--smoke" in sys.argv
    rho, nodes, values, fam, xw, gram, a, _, _ = r37.setup(False)
    base, _ = r37.min_h1(gram, a, np.ones(len(nodes), complex))
    corr, _ = r37.min_h1(gram, a, np.asarray(values, complex))
    support = max(a_ for a_, _ in fam) * (r37.N + 2)
    ps = r59.rig.prime_powers_up_to(math.exp(support))

    anch = []
    for u_f in (0.0, 2 * np.pi, 20 * np.pi, 80 * np.pi):
        s_iv = sigma_arch_iv(iv.mpf([repr(u_f), repr(u_f)]))
        s_float = float(r59.rig.sigma_vec(np.array([u_f]))[0])
        anch.append({"u": u_f, "iv_lo": float(mp.mpf(s_iv.a)),
                     "iv_hi": float(mp.mpf(s_iv.b)),
                     "float_committed": s_float,
                     "contained": bool(mp.mpf(s_iv.a) <= s_float <= mp.mpf(s_iv.b))})
    print("anchors:", json.dumps(anch), flush=True)

    # precomputed per-k interval constants (2 pi log k, 2 Lambda(k)/sqrt(k))
    ck = [(iv.mpf(2) * iv.pi) * iv.log(iv.mpf(int(num))) for num, _ in ps]
    wk = [iv.mpf(2) * iv.mpf(int(w)) / iv.sqrt(iv.mpf(int(num))) for num, w in ps]

    ladder = (0.05,) if smoke else LADDER
    lo_line = 0.0 if smoke else -XI_MAX
    rows = []
    for dxi in ladder:
        t0 = time.time()
        n_pan = int(round((XI_MAX - lo_line) / dxi))
        edges = np.linspace(lo_line, XI_MAX, n_pan + 1)
        ker_f, g_f = float_kernel_and_g(edges, fam, xw, base, corr, rho, ps)
        g_mid = 0.5 * (g_f[:-1] + g_f[1:])
        q_float = float(np.sum(0.5 * (ker_f[:-1] + ker_f[1:]) * g_mid * dxi))
        widths = np.empty(n_pan)
        for i in range(n_pan):
            xi_iv = iv.mpf([repr(float(edges[i])), repr(float(edges[i + 1]))])
            ker_iv = sigma_arch_iv((iv.mpf(2) * iv.pi) * xi_iv)
            for j in range(len(ps)):
                ker_iv = ker_iv + wk[j] * iv.cos(ck[j] * xi_iv)
            widths[i] = float(mp.mpf(ker_iv.b) - mp.mpf(ker_iv.a))
        proj = float(np.sum(widths * g_mid * dxi))
        rows.append({
            "dxi": dxi, "panels": n_pan,
            "width_max": float(widths.max()), "width_mean": float(widths.mean()),
            "kernel_side_projected_total_width": proj,
            "float_Q_midpoint_reference": q_float,
            "seconds": round(time.time() - t0, 1),
        })
        print(json.dumps(rows[-1]), flush=True)

    ok_all = all(r_["contained"] for r_ in anch)
    finest = rows[-1]["kernel_side_projected_total_width"]
    if not ok_all:
        verdict = "L2-WIDTH-FAIL (anchor containment broken)"
    elif finest < 1e19:
        verdict = "L2-WIDTH-OK"
    elif all(r_["kernel_side_projected_total_width"] > 1.11e20 for r_ in rows):
        verdict = "L2-WIDTH-FAIL"
    else:
        verdict = "L2-WIDTH-GRAY"
    out = {
        "record": 2043, "status": verdict, "owner": "one-copy G8-H",
        "rho": [float(rho.real), float(rho.imag)], "scale": r37.SCALE,
        "support": support, "book_size": len(ps),
        "nyquist": {"max_log_k": math.log(max(n_ for n_, _ in ps)),
                    "arg_width_max_finest": 2 * math.pi * LADDER[-1]
                                            * math.log(max(n_ for n_, _ in ps)),
                    "note": "panel enclosure is interval arithmetic; the "
                            "float-grid Nyquist bound does not apply to widths"},
        "anchors": anch, "rows": rows,
        "nonclaims": ["kernel-side width projection only; L1/L3 slack not counted",
                      "no full-line tail (L4 separate)", "no coefficient enclosure",
                      "not a producer theorem", "not RH"],
    }
    path = os.path.join(ROOT, "results", "2043_interval_kernel_width.json")
    with open(path, "w", encoding="utf-8", newline="\n") as f:
        json.dump(out, f, indent=2)
        f.write("\n")
    print("VERDICT", verdict)
    print("RESULT", path)


if __name__ == "__main__":
    main()
