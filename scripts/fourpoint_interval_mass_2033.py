#!/usr/bin/env python3
"""Record 2033 P6: interval bracket for the k = 3 weighted seed mass.

Pre-registered in docs/proofs/2032_full_block_assault_preregistration.md
section 3 and repeated in docs/proofs/2033_gate_tail_pairing_preregistration.md.

Object.  A_k(a) = integral_0^1 e^{a u} |T^{(k)}(u)| du with T the Mathlib
smoothTransition T(u) = 1 / (1 + exp(1/u - 1/(1-u))), and

    W_k(a) = e^{-2a} A_k(a) + e^{2a} A_k(-a).

Instrument (registered).  Interval arithmetic (mpmath.iv, directed rounding)
for the sign-piece brackets of T'''.  On a panel on which T''' has constant
sign,

    integral_p^q |T'''| du = |T''(q) - T''(p)|                (exact),

so with e^{a u} <= e^{a q} for a >= 0 and <= e^{a p} for a <= 0,

    integral_p^q e^{a u}|T'''| du <= (max of e^{a u} on the panel)
                                      * sup |T''(q) - T''(p)|.

Panel assembly.  [END_DELTA, 1 - END_DELTA] is cut into NBASE equal panels and
each panel is handed to the mean-value enclosure

    T'''(u) in T'''(m) + (u - m) * T''''([p, q]),   m = (p + q)/2.

If that enclosure excludes zero, the sign of T''' is certified on the panel and
the panel is charged its exact FTC mass |T''(q) - T''(p)| carried as an
interval.  Otherwise the panel is charged the envelope bound
(q - p) * sup |T'''| on the panel, which is rigorous but loses the
cancellation.  The two root panels, and the panels where the recurrence is
below the interval resolution, fall in this class; their true mass is at most
the enclosure magnitude, which is many orders below the contribution of the
neighbouring certified panels.

Rewrite note (2026-09-27, instrument only; decision rule unchanged).  The first
version RECURSED on every panel whose enclosure straddled zero.  That does not
terminate in reasonable time: the mean-value enclosure also straddles zero on
both neighbours of a simple root, so the recursion branches on every panel of
the underflow region (u <~ 0.01 and u >~ 0.99) down to the width floor, and a
point scan for the roots was additionally polluted by cancellation near
u = 1 (spurious sign changes at u = 0.9895..0.9999).  The equal-panel envelope
charge below has no such failure mode and locates no roots at all.

End pieces.  On (0, END_DELTA] the recurrence terms obey
|T'''| <= 10 * u^{-6} * exp(-1/u) (the constant is generous; T <= exp(-1/u)
there and the recurrence contributes at most order u^{-6}), hence

    integral_0^END_DELTA |T'''| du
        <= 10 * (1/END_DELTA)^5 * exp(-1/END_DELTA) * 2,

which at END_DELTA = 1e-6 is exp(-1e6)-small.  The carried slack
END_SLACK = 1e-60 is added to the upper end and subtracted from the lower end.
The mirrored end piece obeys the same bound by T(1-u) = 1 - T(u), hence
T'''(1-u) = T'''(u).

Rounding.  Each bracket end is finally inflated (upper) or deflated (lower) by
CONV_CUSHION = 1e-12 relative.  That single cushion dominates (a) the double
exponential factors, (b) the mpf roundings inside the panel sums at 40 dps,
(c) the mpf-to-float conversion, and (d) the double-precision accumulation of
the strip sum, whose amplification is bounded by the exponent 10 on the seed
factor (about 1e-14 relative for the measured cells).
"""

from __future__ import annotations

import json
import math
import os
import sys
import time
from pathlib import Path

import numpy as np
from mpmath import iv, mp, mpf, binomial, factorial

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

import fourpoint_actual_owner_1980 as op  # noqa: E402

T0 = time.time()
iv.dps = 40
mp.dps = 40

Q = 2.0 ** -14
T_MIN, T_MAX, DT = 28.0, 200.0, 0.5
SIGMA_MAX = 1.0
SIGMA_STEP = 0.01
RHO = complex(0.55, 14.134725141734693)
N = 4
SEED0 = 3.0 ** 10
K = 3

END_DELTA = mpf(1) / 10 ** 6
NBASE = 20000
A_STEP = 0.01
A_LO, A_HI = -0.60, 0.60
HALF = mpf(1) / 2
END_SLACK = mpf(10) ** -60
CONV_CUSHION = 1e-12
SMOKE = bool(os.environ.get("RH_INTERVAL_MASS_SMOKE"))


def log(msg):
    print("[%7.1fs] %s" % (time.time() - T0, msg), flush=True)


def _binom_iv(n, j):
    return iv.mpf(int(binomial(n, j)))


def hD_iv(u, j):
    f = int(factorial(j))
    return iv.mpf((-1) ** j * f) / u ** (j + 1) - iv.mpf(f) / (1 - u) ** (j + 1)


def T_deriv_iv(u, k):
    """k-th derivative of the smoothTransition, interval arithmetic."""
    T = 1 / (1 + iv.exp(hD_iv(u, 0)))
    Ts, Gs = [T], [T - T * T]
    for n in range(k):
        acc = iv.mpf([0, 0])
        for j in range(n + 1):
            acc += _binom_iv(n, j) * hD_iv(u, j + 1) * Gs[n - j]
        Ts.append(-acc)
        m = n + 1
        g = Ts[m]
        for j in range(m + 1):
            g -= _binom_iv(m, j) * Ts[j] * Ts[m - j]
        Gs.append(g)
    return Ts[k]


def pt(x):
    return iv.mpf([x, x])


def deriv_at(x, k):
    """Enclosure of T^(k)(x), mirrored through T^(k)(1-u) = (-1)^(k+1) T^(k)(u)
    when x > 1/2, so that the recurrence never evaluates the 1/(1-u) wall.
    Without the mirror, T = 1/(1+exp(hD)) is an interval of width 1e-40 near
    u = 1, T - T^2 straddles zero, and the hD powers amplify that width by
    u^{-12}-scale factors: the panel u = [0.999949, 0.999999] carried an
    envelope mass of 1.18 against a true 3e-30."""
    xm = mpf(x)
    if xm > HALF:
        return ((-1) ** (k + 1)) * T_deriv_iv(pt(1 - xm), k)
    return T_deriv_iv(pt(xm), k)


def enclosure(p, q):
    """Rigorous enclosure of T''' on [p, q] via the mean-value form."""
    if mpf(p) > HALF:
        return enclosure(1 - mpf(q), 1 - mpf(p))
    m = (p + q) / 2
    return (T_deriv_iv(pt(m), K)
            + iv.mpf([p - m, q - m]) * T_deriv_iv(iv.mpf([p, q]), K + 1))


def contains_zero(enc):
    return not (end_hi(enc) < 0 or end_lo(enc) > 0)


def end_lo(enc):
    """Lower endpoint of an mpmath interval as a plain mpf."""
    return mpf(enc.a)


def end_hi(enc):
    """Upper endpoint of an mpmath interval as a plain mpf."""
    return mpf(enc.b)


def build_panels(n_base=NBASE):
    """Equal panels carrying a rigorous upper (and, when the sign of T''' is
    certified, lower) bound of integral_p^q |T'''| du, before the exponential
    factor of the requested a is applied."""
    step = (1 - 2 * END_DELTA) / n_base
    panels = []
    n_sign = n_env = 0
    for i in range(n_base):
        p = END_DELTA + i * step
        q = END_DELTA + (i + 1) * step
        enc = enclosure(p, q)
        if contains_zero(enc):
            supv = max(abs(end_lo(enc)), abs(end_hi(enc)))
            panels.append(("env", p, q, (q - p) * supv, mpf(0)))
            n_env += 1
        else:
            diff = deriv_at(q, 2) - deriv_at(p, 2)
            da, db = end_lo(diff), end_hi(diff)
            hi = max(abs(da), abs(db))
            lo = mpf(0) if (da <= 0 <= db) else min(abs(da), abs(db))
            panels.append(("sign", p, q, hi, lo))
            n_sign += 1
    return panels, n_sign, n_env


def A3_bracket(panels, a):
    """mpf bracket (lo, hi) of A_3(a) = integral_0^1 e^{a u}|T'''| du."""
    hi = END_SLACK
    lo = -END_SLACK
    for kind, p, q, vhi, vlo in panels:
        if a >= 0:
            hi += vhi * math.exp(a * float(q))
            lo += vlo * math.exp(a * float(p))
        else:
            hi += vhi * math.exp(a * float(p))
            lo += vlo * math.exp(a * float(q))
    return lo, hi


def widen_lo(x):
    f = float(x)
    return f - abs(f) * CONV_CUSHION - 1e-300


def widen_hi(x):
    f = float(x)
    return f + abs(f) * CONV_CUSHION + 1e-300


def build_a_grid(panels):
    grid = []
    a = A_LO
    while a <= A_HI + 1e-12:
        lo, hi = A3_bracket(panels, a)
        grid.append((a, widen_lo(lo), widen_hi(hi)))
        a = round(a + A_STEP, 10)
    return grid


def make_lookup(grid):
    """Monotone lookups.  A_3 is increasing in a, so an upper bound of A_3(x)
    is the bracket upper end of the smallest grid point >= x, and a lower
    bound is the bracket lower end of the largest grid point <= x."""
    def up_hi(x):
        if x < grid[0][0] - 1e-9 or x > grid[-1][0] + 1e-9:
            raise RuntimeError("a = %s outside the certified grid" % x)
        for a, _lo, hi in grid:
            if a >= x - 1e-9:
                return hi
        raise RuntimeError("a = %s has no grid point at or above it" % x)

    def down_lo(x):
        if x < grid[0][0] - 1e-9 or x > grid[-1][0] + 1e-9:
            raise RuntimeError("a = %s outside the certified grid" % x)
        best = grid[0][1]
        for a, lo, _hi in grid:
            if a <= x + 1e-9:
                best = lo
            else:
                break
        return best

    return up_hi, down_lo


def w3_upper(a, up_hi):
    """Upper end of W_3(a) = e^{-2a} A_3(a) + e^{2a} A_3(-a)."""
    return (math.exp(-2 * a) * up_hi(a) + math.exp(2 * a) * up_hi(-a))


def w3_lower(a, down_lo):
    return (math.exp(-2 * a) * down_lo(a) + math.exp(2 * a) * down_lo(-a))


def main():
    report = {
        "record": 2033,
        "phase": "P6 interval bracket for W_3",
        "status": "PENDING",
        "preregistration":
            "docs/proofs/2033_gate_tail_pairing_preregistration.md",
        "owner_model": "known-zero under-approximation (record 1980 rig)",
        "rho": [RHO.real, RHO.imag], "N": N, "k": K,
        "q": Q, "iv_dps": iv.dps, "mp_dps": mp.dps,
        "a_step": A_STEP, "sigma_step": SIGMA_STEP,
        "t_grid": [T_MIN, T_MAX, DT], "n_base": NBASE,
        "end_delta": float(END_DELTA), "end_slack": float(END_SLACK),
        "conv_cushion": CONV_CUSHION,
        "instrument_note": ("equal-panel envelope charge with an exact FTC mass "
                            "on every sign-certified panel; the recursive "
                            "panel builder of the first version was replaced "
                            "the same day because it did not terminate"),
    }

    log("building %d equal panels of T''' on the unit interval" % NBASE)
    panels, n_sign, n_env = build_panels()
    widths = [float(q - p) for _k, p, q, _h, _l in panels]
    report["panels"] = {"count": len(panels), "sign": n_sign, "env": n_env,
                        "width": widths[0]}
    log("panels: %d total, %d sign-certified, %d envelope; width %.3e"
        % (len(panels), n_sign, n_env, widths[0]))

    log("building A_3 interval brackets on the a-grid")
    grid = build_a_grid(panels)
    report["a_grid"] = [{"a": a, "A3_lo": lo, "A3_hi": hi}
                        for a, lo, hi in grid]
    up_hi, down_lo = make_lookup(grid)

    ref = {0.025: 78.9829335535928, 0.225: 83.63028482255264,
           0.275: 85.99233526194708, 0.525: 105.83438341394672}
    checks = []
    for a in sorted(ref):
        lo = w3_lower(a, down_lo)
        hi = w3_upper(a, up_hi)
        checks.append({"a": a, "W3_lo": lo, "W3_hi": hi,
                       "record_2031_value": ref[a],
                       "contains_2031": bool(lo <= ref[a] <= hi),
                       "rel_width": (hi - lo) / ref[a]})
    report["W3_bracket_checks"] = checks
    log("W3 self-check: %s" % [(c["a"], c["contains_2031"],
                                "%.2e" % c["rel_width"]) for c in checks])

    out = ROOT / "results" / "2033_interval_mass_w3.json"
    out.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    log("wrote %s (pre-scan dump of the panels and the a-grid)" % out)

    log("certified strip scan (k = 3, upper end of the bracket)")
    owner, targets, _radius, _known = op.build_owner(RHO, N)
    active = [(z, op.target_value(RHO, z)) for z in targets
              if abs(op.target_value(RHO, z)) > 0]
    weights = []
    for z, v in active:
        pzz = op.node_product(owner, z, z)
        weights.append((z, abs(v / (pzz * SEED0))))
    sig_list = [round(float(s), 6)
                for s in np.arange(0.0, SIGMA_MAX + 1e-9, SIGMA_STEP)]
    t_list = [round(float(t), 6)
              for t in np.arange(T_MIN, T_MAX + 1e-9, DT)]
    if SMOKE:
        sig_list, t_list = sig_list[:3], t_list[:4]
    best = None
    for sig in sig_list:
        pre = []
        for z, cabs in weights:
            a = (sig - z.real) / 2.0
            pre.append((z, cabs, a, w3_upper(a, up_hi)))
        for t in t_list:
            tot = 0.0
            for z, cabs, a, w3u in pre:
                y = (t - z.imag) / 2.0
                if abs(y) < 1e-12:
                    continue
                seedb = w3u / abs(complex(a, y)) ** K
                P = abs(op.node_product(owner, z, complex(sig, t)))
                tot += cabs * P * seedb ** 10
            if best is None or tot > best[0]:
                best = (tot, sig, t)
    bound = best[0] * (1 + CONV_CUSHION)
    report["certified_strip"] = {
        "k": K, "bound": bound, "sigma": best[1], "t": best[2],
        "margin_vs_q": Q / bound,
        "uncertified_2031_bound": 3.00164105722696e-07,
        "sigma_grid_points": len(sig_list), "t_grid_points": len(t_list),
        "smoke": SMOKE,
    }
    report["status"] = "MASS-BRACKETED" if Q / bound > 1.0 else "MASS-LOST"
    log("certified k=3 bound %.6e at (%.2f, %.1f); margin vs q = %.2f"
        % (bound, best[1], best[2], Q / bound))

    out = ROOT / "results" / "2033_interval_mass_w3.json"
    out.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    log("wrote %s" % out)
    print(json.dumps({"status": report["status"],
                      "certified_strip": report["certified_strip"],
                      "W3_bracket_checks": report["W3_bracket_checks"],
                      "panels": report["panels"]}, indent=2))


if __name__ == "__main__":
    main()
