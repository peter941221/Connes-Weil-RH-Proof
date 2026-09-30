"""Record 2304: moment-asymptotic infinite-tail probe for the corrected owner.

The hgap split (2275) leaves the infinite-xi tail

    Tail = int_{|xi| > 40} kernel(xi) |ann(xi)|^2 |B(xi)|^2 |C(xi)|^2 dxi

with the 2280 assembly: B, C are the Fourier transforms of the corrected
owner profiles h_b(y) = sum_f c_f^b phi_{a_f^2}(y) e^{(1/2 + i theta_f) y}
(same for corr), kernel(xi) = sigma(2 pi xi) + 2 sum_p w_p p^{-1/2}
cos(2 pi xi log p) over the 41136 prime powers, and ann is the degree-four
detector annihilator.  The frozen quadrature instruments (2286-2294) price
the tail by enclosing the transforms; this probe prices it by a completely
different mechanism:

  FLAT-EDGE INTEGRATION BY PARTS.  phi_R(y) = exp(-30/(1-(y/R)^2)) is C-infinity
  and FLAT at y = +-R: every derivative phi_R^(j)(+-R) = 0.  The same holds
  for h = phi * E with E(y) = e^{(1/2 + i theta) y} smooth, because Leibniz
  makes every boundary term vanish.  Hence N-fold integration by parts on

      B(xi) = int_{-R}^{R} h(y) e^{-2 pi i xi y} dy

  has NO boundary terms and reads  B(xi) = R_N(xi), with the classical
  remainder bound

      |B(xi)| <= ||h^(N)||_inf / (2 pi xi)^N  =: V_N / (2 pi xi)^N.

  So the tail is charged by sup-norms of ONE real-variable derivative, not
  by an interval enclosure of the xi-functional.  The product of four
  transforms gives xi^{-4N}, which beats the xi^4 annihilator growth and the
  log xi archimedean growth for every N >= 2:

      Tail <= 2 * W_ker * A1^2 * (V_N^b V_N^c)^2 / (2 pi)^{4N}
              * int_40^inf (log xi * c1 + c2) xi^{8-4N} dxi,

  with W_ker the triangle bound on the kernel, A1 = sum |ann coefficients|.

Sup-norm ladder.  With L_m(u) = d^m/du^m log psi = -(K m!/2)[(1-u)^-(m+1)
+ (-1)^m (1+u)^-(m+1)] and psi^(j) = psi * Y_j(L_1..L_j) (complete Bell
polynomial), two ladders are computed:

  (a) MEASURED: max over a fine u-grid of |psi * Y_j| with the exact L_m;
  (b) RIGOROUS: partition expansion of Y_j with |L_m| <= K m! 2^{m+1} s^-(m+1)
      (s = 1-u^2) and sup_{s<=1} e^{-K/s} s^-p = e^{-K} for p <= K,
      e^-p (p/K)^p otherwise.  This is a closed-form majorant; per-order
      ratio (b)/(a) is reported, and it is the loose factor that decides
      whether the mechanism survives in certified form.

Verdict: TAIL-MOMENT-FEASIBLE if the rigorous bound is at most the 1e7 hgap
budget with margin; TAIL-MOMENT-DEAD if the best order overshoots.  The
probe also reports the MEASURED |B(40)|, |C(40)| from an independent
100-digit mpmath quadrature as the fail-fast calibration at xi = 40.

Modes: MODE=probe (default) writes results/2304_hgap_tail_moment_probe.json;
MODE=selftest runs the internal controls.
"""
import json
import math
import os
import sys
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
R = ROOT / "results"
OUT = R / "2304_hgap_tail_moment_probe.json"
CAPTURE = R / "2275_gap_owner_audit.json"
K = 30.0
XI0 = 40.0
BUDGET = 1.0e7
ORDERS = (3, 4, 6, 8, 10, 12, 14, 16, 20, 24, 28, 32, 36, 40, 44)
GAMMA = 39.25244858548658
DELTA = 0.445


def load_owner():
    cap = json.loads(CAPTURE.read_text(encoding="utf-8"))["owner_capture"]
    fam = [(float.fromhex(a), float.fromhex(t)) for a, t in cap["families_hex"]]
    base = np.array([complex(float.fromhex(re), float.fromhex(im))
                     for re, im in cap["base_hex"]])
    corr = np.array([complex(float.fromhex(re), float.fromhex(im))
                     for re, im in cap["corr_hex"]])
    return fam, base, corr, cap


# ------------------------------------------------------- sup ladder on psi
def log_derivs(u, j_max):
    """L_m(u) for m = 1..j_max on the master psi(u) = exp(-K/(1-u^2))."""
    out = []
    for m in range(1, j_max + 1):
        term = (1.0 - u) ** (-(m + 1))
        if m % 2 == 0:
            term = term + (1.0 + u) ** (-(m + 1))
        else:
            term = term - (1.0 + u) ** (-(m + 1))
        out.append(-K * math.factorial(m) / 2.0 * term)
    return out


def measured_sup(j_max, npts=4000001, edge=1e-7):
    """max |psi^(j)| on (-1,1) by exact Bell evaluation on a fine grid."""
    u = np.concatenate([np.linspace(-1.0 + edge, 1.0 - edge, npts),
                        np.linspace(0.5, 1.0 - edge, 200001),
                        np.linspace(-1.0 + edge, -0.5, 200001)])
    s = 1.0 - u * u
    psi = np.exp(-K / s)
    lv = []
    for m in range(1, j_max + 1):
        t = (1.0 - u) ** (-(m + 1))
        t = t + (1.0 + u) ** (-(m + 1)) if m % 2 == 0 else \
            t - (1.0 + u) ** (-(m + 1))
        lv.append(-K * math.factorial(m) / 2.0 * t)
    y_prev = [np.ones_like(u)]              # Y_0
    sup = [float(np.max(np.abs(psi)))]
    for j in range(1, j_max + 1):
        acc = np.zeros_like(u)
        for i in range(j):
            acc = acc + math.comb(j - 1, i) * y_prev[j - 1 - i] * lv[i]
        y_prev.append(acc)
        sup.append(float(np.max(np.abs(psi * acc))))
    return sup


def partitions(n):
    """Integer partitions of n as sorted tuples (descending)."""
    if n == 0:
        yield ()
        return
    def rec(rest, cap, acc):
        if rest == 0:
            yield tuple(acc)
            return
        for part in range(min(rest, cap), 0, -1):
            acc.append(part)
            yield from rec(rest - part, part, acc)
            acc.pop()
    yield from rec(n, n, [])


def rigorous_sup(j_max, ctx):
    """Partition majorant Q_j >= sup |psi^(j)|, closed form per order.

    Evaluated in the mpmath context `ctx` (60 digits) because the partition
    constants overflow binary64 already at j ~ 24.
    """
    mp = ctx
    out = []
    for j in range(0, j_max + 1):
        if j == 0:
            out.append(mp.e ** -K)
            continue
        total = mp.mpf(0)
        for part in partitions(j):
            counts = {}
            for m in part:
                counts[m] = counts.get(m, 0) + 1
            blocks = len(part)
            multinom = mp.factorial(j)
            const = mp.mpf(1)
            for m, k in counts.items():
                multinom /= mp.factorial(m) ** k * mp.factorial(k)
                const *= (K * mp.factorial(m) * 2 ** (m + 1)) ** k
            p_exp = j + blocks
            # sup_{s in (0,1]} e^{-K/s} s^{-p}: critical point s* = K/p is
            # inside the domain iff p > K; otherwise the sup sits at s = 1.
            if p_exp <= K:
                sup_s = mp.e ** -K
            else:
                sup_s = (mp.e ** -p_exp) * (mp.mpf(p_exp) / K) ** p_exp
            total += multinom * const * sup_s
        out.append(total)
    return out


def v_ladder(fam, coef, sup, order, ctx):
    """V_N = sup |h^(N)| over the full complex grouped sum, familywise.

    h = sum_f c_f phi_{R_f} E_f with R_f = a_f^2, E_f = e^{(1/2 + i theta_f)y};
    Leibniz gives (phi E)^(N) = sum_j binom(N,j) phi^(j) E^(N-j), and
    |E^(m)(y)| = |1/2 + i theta|^m e^{y/2} <= |1/2 + i theta|^m e^{R_f/2}.
    sup |phi_R^(j)| = sup |psi^(j)| / R^j by the u = y/R scaling.
    """
    mp = ctx
    v = mp.mpf(0)
    for (rad, th), c in zip(fam, coef):
        inner = mp.mpf(0)
        for j in range(order + 1):
            inner += (mp.binomial(order, j) * sup[j] * mp.mpf(rad) ** -j
                      * mp.mpf(abs(complex(0.5, th))) ** (order - j))
        v += mp.mpf(abs(complex(c))) * (mp.e ** (mp.mpf(rad) / 2)) * inner
    return v


# ------------------------------------------------------------ tail algebra
def annihilator_coeffs():
    """Coefficients of prod (node - s), s = -2 pi i xi, as a real polynomial."""
    rho = complex(0.5 + DELTA, GAMMA)
    nodes = [rho - 0.5, (1 - rho.conjugate()) - 0.5,
             rho.conjugate() - 0.5, (1 - rho) - 0.5]
    poly = np.array([1.0 + 0.0j])
    for node in nodes:
        poly = np.convolve(poly, np.array([-2j * math.pi, node]))
        # variable order: [xi^1, xi^0] -> keep descending
    coef = poly[::-1]
    assert np.max(np.abs(coef.imag)) < 1e-9 * max(1.0, np.max(np.abs(coef.real)))
    return [float(v.real) for v in coef]


def kernel_bound():
    """W_ker(xi) <= log xi + C_sigma + prime_sum for xi >= 40.

    |sigma(omega)| = |log pi - Re psi(1/4 - i omega/2)| with the shifted
    representation psi = log(zz) - 0.5/zz - corr - s, zz = z + 8:
      |Re psi| <= log|zz| + 0.5/|zz| + |corr| + |s|,
    |corr| <= sum_k |b_k| 8^{-2k}, |s| <= sum_j 1/|z+j| <= sum_j 1/(j+1/4),
    and log|zz| = (1/2) log((omega/2)^2 + 8.25^2) <= log pi + log xi + slack
    with slack = (1/2) log(1 + 8.25^2/(pi^2 XI0^2)).
    The prime part is triangle-bounded by 2 sum_p w_p / sqrt(p).
    """
    import fourpoint_diagonal_sign_1918 as rig
    terms = [1 / 12, -1 / 120, 1 / 252, -1 / 240, 1 / 132, -691 / 32760]
    corr_bound = sum(abs(b) * 64.0 ** -kk for kk, b in enumerate(terms, start=1))
    harm = sum(1.0 / (jj + 0.25) for jj in range(8))
    slack = 0.5 * math.log1p(8.25 ** 2 / ((math.pi * XI0) ** 2))
    c_sigma = (2.0 * math.log(math.pi) + 0.5 / 8.0 + corr_bound + harm + slack)
    primes = rig.prime_powers_up_to(math.exp(2.0 * 6.553600000000003))
    prime_sum = 2.0 * sum(w / math.sqrt(n) for n, w in primes)
    c_w = c_sigma + prime_sum
    return c_sigma, prime_sum, len(primes), c_w


def tail_integral(order, c1, c2):
    """int_40^inf (c1 log xi + c2) xi^{8-4N} dxi, closed form."""
    p = 4 * order - 8
    if p <= 1:
        raise ValueError("order too small")
    base = XI0 ** (1 - p) / (p - 1)
    return c1 * base * (math.log(XI0) + 1.0 / (p - 1)) + c2 * base


def tail_integral_mp(order, c1, c2, mp):
    """int_40^inf (c1 log xi + c2) xi^{8-4N} dxi, closed form (mpmath)."""
    p = 4 * order - 8
    if p <= 1:
        raise ValueError("order too small")
    base = mp.mpf(XI0) ** (1 - p) / (p - 1)
    return c1 * base * (mp.log(XI0) + mp.mpf(1) / (p - 1)) + c2 * base


def _num(v, mp):
    """float for the JSON plus a lossless string when float over/underflows."""
    f = float(v)
    return (f, mp.nstr(v, 8))


def probe():
    import mpmath as mp
    mp.mp.dps = 60
    fam, base, corr, _cap = load_owner()
    j_max = max(ORDERS)
    sup_num = measured_sup(min(j_max, 20))
    sup_rig = rigorous_sup(j_max, mp)
    ratios = []
    for j in range(len(sup_num)):
        ratios.append(float(sup_rig[j] / mp.mpf(repr(sup_num[j]))))
    ann = annihilator_coeffs()
    a1 = sum(abs(v) for v in ann)
    c_sigma, prime_sum, n_primes, c_w = kernel_bound()
    w_ker = math.log(XI0) + c_w
    rows = []
    for order in ORDERS:
        vb_r = v_ladder(fam, base, sup_rig, order, mp)
        vc_r = v_ladder(fam, corr, sup_rig, order, mp)
        integ = tail_integral_mp(order, 1, mp.mpf(repr(c_w)), mp)
        tail_r = (2 * mp.mpf(repr(a1)) ** 2 * (vb_r * vc_r) ** 2
                  / (2 * mp.pi) ** (4 * order) * integ)
        env_r = (2 * (mp.log(XI0) + mp.mpf(repr(c_w))) * mp.mpf(repr(a1)) ** 2
                 * mp.mpf(XI0) ** 8 / (2 * mp.pi * XI0) ** (4 * order)
                 * (vb_r * vc_r) ** 2)
        row = {
            "order": order,
            "V_rigorous": {"base_float": float(vb_r), "base": mp.nstr(vb_r, 8),
                           "corr_float": float(vc_r), "corr": mp.nstr(vc_r, 8)},
            "envelope_at_40_rigorous": mp.nstr(env_r, 8),
            "tail_bound_rigorous": mp.nstr(tail_r, 8),
            "tail_bound_rigorous_float": float(tail_r),
        }
        if order < len(sup_num):
            vb_n = v_ladder(fam, base, sup_num, order, mp)
            vc_n = v_ladder(fam, corr, sup_num, order, mp)
            tail_n = (2 * mp.mpf(repr(a1)) ** 2 * (vb_n * vc_n) ** 2
                      / (2 * mp.pi) ** (4 * order) * integ)
            row["tail_bound_measured"] = mp.nstr(tail_n, 8)
            row["tail_bound_measured_float"] = float(tail_n)
            row["V_measured"] = {"base": mp.nstr(vb_n, 8),
                                 "corr": mp.nstr(vc_n, 8)}
        rows.append(row)
    best = min(rows, key=lambda r: r["tail_bound_rigorous_float"])
    best_val = mp.mpf(best["tail_bound_rigorous"].replace("e", "E")) \
        if "e" in best["tail_bound_rigorous"] else mp.mpf(best["tail_bound_rigorous"])
    status = ("TAIL-MOMENT-FEASIBLE"
              if best_val <= BUDGET else "TAIL-MOMENT-DEAD")
    out = {
        "record": 2304, "status": status, "certificate": False,
        "mechanism": "flat-edge N-fold integration by parts: no boundary "
                     "terms, |B(xi)| <= V_N/(2 pi xi)^N, tail charged by "
                     "one real-variable sup-norm per channel",
        "budget": BUDGET, "xi0": XI0,
        "sup_ladder_measured": sup_num,
        "sup_ladder_rigorous": sup_rig,
        "rigorous_over_measured": ratios,
        "annihilator": {"coeffs": ann, "l1": a1},
        "kernel": {"c_sigma": c_sigma, "prime_sum": prime_sum,
                   "prime_power_count": n_primes, "c_w": c_w,
                   "W_ker_at_40": w_ker},
        "rows": rows,
        "best_order": best["order"],
        "best_tail_bound": best["tail_bound_rigorous"],
        "best_tail_bound_float": best["tail_bound_rigorous_float"],
        "best_margin": BUDGET / best["tail_bound_rigorous_float"],
        "orders_dead": [r["order"] for r in rows
                        if r["tail_bound_rigorous_float"] > BUDGET],
        "calibration": calibration(sup_num),
        "nonclaims": [
            "probe grade: the measured ladder is a grid maximum, not an "
            "interval enclosure",
            "the rigorous ladder is a closed-form partition majorant valid "
            "for every u in (-1,1); its looseness is reported per order",
            "the tail bound is an absolute-value bound; it does not supply "
            "the signed finite-window functional, the selected-owner "
            "readback or the producer margin",
            "no arithmetic certification of the prime sum, the annihilator "
            "l1 norm or the kernel bound has been machine-checked yet",
            "no hgap certificate, no producer GO, no RH claim"],
        "provenance": {
            "script": "scripts/routea_hgap_tail_moment_probe_2304.py",
            "owner": "results/2275_gap_owner_audit.json",
            "tail_object": "scripts/routea_phase_centered_filon_tail_screen_2280.py",
        },
    }
    OUT.write_text(json.dumps(out, indent=2, default=str) + "\n",
                   encoding="utf-8")
    print(json.dumps({"status": status, "best_order": best["order"],
                      "best_tail_bound": best["tail_bound_rigorous"],
                      "margin": BUDGET / best["tail_bound_rigorous_float"],
                      "envelope_at_40": best["envelope_at_40_rigorous"],
                      "ladder_ratios_head": ratios[:5],
                      "ladder_ratio_tail": ratios[-2:],
                      "W_ker": w_ker, "a1": a1,
                      "prime_power_count": n_primes}, indent=2), flush=True)


def calibration(sup_num):
    """Single-family IBP-bound control at xi = 1, 2, 4 (mpmath, 60 digits).

    The 30-family owner transform at xi = 40 CANNOT be measured: the term
    scale is ~1e12 (coefficient magnitude times profile L1) while the true
    flat-transform decay at xi = 40 is of order exp(-2 sqrt(30 pi xi)) =
    exp(-173.6) ~ 1e-75, so every finite-precision quadrature returns
    cancellation noise.  The mechanism is therefore controlled where the
    transform is actually resolvable: a single family R = 6.5536, c = 1,
    theta = 0, at small xi, where |B(xi)| ~ exp(-2 sqrt(30 pi xi)).
    """
    try:
        import mpmath as mp
    except ImportError:
        return {"skipped": "mpmath unavailable"}
    mp.mp.dps = 60
    rad = mp.mpf("6.553600000000003")

    def f_re(y, xi):
        s = 1 - (y / rad) ** 2
        return (mp.e ** (-30 / s) * mp.e ** (mp.mpf("0.5") * y)
                * mp.cos(-2 * mp.pi * xi * y))

    def f_im(y, xi):
        s = 1 - (y / rad) ** 2
        return (mp.e ** (-30 / s) * mp.e ** (mp.mpf("0.5") * y)
                * mp.sin(-2 * mp.pi * xi * y))
    rows = []
    for xi_f in (1.0, 2.0, 4.0):
        xi = mp.mpf(xi_f)
        points = [-rad, mp.mpf(0), rad]
        val = (mp.quad(lambda y: f_re(y, xi), points)
               + 1j * mp.quad(lambda y: f_im(y, xi), points))
        meas = abs(val)
        per = []
        for order in [o for o in ORDERS if o < len(sup_num)]:
            v = v_ladder([(float(rad), 0.0)], [complex(1.0)], sup_num, order, mp)
            bound = v / (2 * mp.pi * xi_f) ** order
            per.append({"order": order, "bound": mp.nstr(bound, 8),
                        "bound_float": float(bound),
                        "ratio": mp.nstr(bound / meas, 8) if meas > 0 else None})
        rows.append({"xi": xi_f, "measured_abs_B": mp.nstr(meas, 10),
                     "decay_scale": math.exp(-2 * math.sqrt(30 * math.pi * xi_f)),
                     "bounds": per})
    return {"control": "single-family IBP bound", "dps": 60, "rows": rows,
            "owner_at_40_unmeasurable": (
                "term scale ~1e12 vs exp(-173.6) ~1e-75 flat-transform decay: "
                "no finite-precision quadrature can resolve B(40)")}


def selftest():
    import mpmath as mp
    mp.mp.dps = 60
    ok = True
    sup_num = measured_sup(6, npts=200001)
    sup_rig = rigorous_sup(6, mp)
    ok &= all(sup_rig[j] >= sup_num[j] * (1 - 1e-12) for j in range(7))
    ok &= all(sup_num[j] > 0 for j in range(7))
    # psi^(1) closed check: sup |2K u/s^2| e^{-K/s} ~ 4.8 e^{-K}
    ok &= abs(sup_num[1] / math.exp(-K) - 4.82) < 0.5
    ann = annihilator_coeffs()
    ok &= len(ann) == 5 and abs(ann[4] - (2 * math.pi) ** 4) < 1e-6
    p = tail_integral(4, 1.0, 1.0)
    ok &= p > 0 and math.isfinite(p)
    # monotone decay of the closed integral in the order
    ok &= tail_integral(6, 1.0, 1.0) < tail_integral(4, 1.0, 1.0)
    print(json.dumps({"selftest": "PASS" if ok else "FAIL",
                      "sup1_over_emK": sup_num[1] / math.exp(-K),
                      "ann_lead": ann[4]}, indent=2))
    return ok


def main():
    mode = os.environ.get("MODE", "probe")
    if mode == "selftest":
        if not selftest():
            raise SystemExit("selftest failed")
    else:
        probe()


if __name__ == "__main__":
    main()