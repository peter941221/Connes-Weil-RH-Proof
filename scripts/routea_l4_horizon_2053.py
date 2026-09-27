#!/usr/bin/env python3
# routea_l4_horizon_2053.py -- record 2053 (probe; verdict rules FROZEN before the run)
#
# ROUTE A LINK L2: L4 outcome (full-line tail) + the committed phi-quadrature
# resolution horizon.
#
# The committed family evaluator is the composite Gauss-Legendre rule
# r59.phi_weights(a, panels=6, m=400) (2400 nodes/family) fed through
# exp(wa X) @ (phi_fun W).  Its exactness bound on one panel of half-width
# h_p/2 = a/6 is omega_tilde = |Im w| a / 6 <= 2m = 800, i.e. a^2 |t| <= 4800
# (t = theta - 2 pi xi the shifted node argument).  Beyond that the rule
# aliases; below it the rule is exact up to the float64 summation floor.
# The truth is computed by G: composite GL on phase-pi panels of
# int_{-1}^{1} phi(u) e^{w a u} du, at working dps, with an a-priori
# per-panel error budget Gerr = (pi/2)^{2n}/(2n)! * Sabs (Sabs = L1 of the
# rule).  T (Taylor) was attempted first and RETIRED: the coefficient series
# of e^{-k/(1-u^2)} converges only like e^{-c sqrt j} and the K_n recursion
# loses all digits for n >> |w| (see record 2053 section on the retired
# method; the two-term recurrence draft summed (1-u^2)^k by mistake).
#
# VERDICT RULES (frozen):
#   C0 controls: (a) truth vs committed float at (a=1.76, t=2) rel <= 1e-3;
#                (b) probe Q_{m=400}(40) vs the committed record-2037 q_h1
#                    = -1.11119e20 (|Q| = 1.1111e20; cross-read -1.11126e20
#                    at record 2041): |Q_400| rel <= 2e-2 AND sign < 0;
#                else CONTROL-FAIL (no verdict).
#   C1 truth: G with two-level stability (n vs n+20 at same dps; dps vs dps+40):
#             rel <= 1e-20 at the pinning set; else truth-unresolved there.
#   C2 rule status at (family, t): OK iff |v_rule - v_true| <= 1e-3 |v_true|;
#      UNRESOLVED iff |v_rule - v_true| > 1e-3 max(|v_true|, Gerr)
#      and |v_rule| > 3 max(|v_true|, Gerr); else GRAY.
#      horizon H_j = smallest sampled t in {5,10,20,40,80,160} with UNRESOLVED.
#   C3 cliff: t*_j = 4800/a_j^2; rule-only: the m=400 value jumps by >= 1e6
#      between 0.9 t* and 1.1 t* while the m=6400 value does not.
#   C4 window: profiles at m in {400,1600,6400} over [-40,40]; the verdict
#      PHI-HORIZON-DOMINANT iff |Q_1600(40)| <= 0.5 |Q_400(40)| and
#      |Q_400(40) - Q_1600(40)| >= 1e19.
#   C5 L4: T_bnd(40) from the three landed rungs (1986/1987/1988) + the
#      kernel envelope C_book + |sigma|: L4-PRICE-FAIL iff T_bnd(40) > 1e19
#      (the record-2041 registered kill; also reported vs |Q| = 1.1111e20).
#
# Scope: measured statements about the committed evaluator and the landed
# rung constants at the registered owner; no producer theorem; not RH.

import json, math, os, sys, time
import numpy as np
import mpmath as mp

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(ROOT, "scripts"))
import fourpoint_owner_completion_1980 as r80
import fourpoint_owner_density_1959 as r59
import routea_g8h_basis_comparison_2037 as r37

K = 30.0
XI_MAX = 40.0
BUDGET = 1e19
Q_COMMITTED = 1.1111e20          # |q_h1|; committed q_h1 = -1.11119e20 (record 2037)
Q_COMMITTED_SIGN = -1.0          # sign of the committed q_h1 (2037; 1996/2041 both negative)
PANELS, M0 = 6, 400
T_GRID = (5.0, 10.0, 20.0, 40.0, 80.0, 160.0)

RUNG_N1 = 2 * math.exp(-4 * K / 3) + (16 * K / 9) * math.exp(-K)
RUNG_N2 = (532 * K * K + 398 * K) * math.exp(-K)
RUNG_N3 = (math.exp(-K) * (9500 * K ** 3 + 19400 * K ** 2 + 6500 * K)
           + 2196115 * K ** -4 + 16470860 * K ** -5 + 19765032 * K ** -6)
RUNGS = (RUNG_N1, RUNG_N2, RUNG_N3)

t0 = time.time()
OUT = {"record": 2053, "probe": "routea_l4_horizon_2053",
       "constants": {"K": K, "panels": PANELS, "m0": M0, "budget": BUDGET,
                     "Q_committed": Q_COMMITTED, "rungs": list(RUNGS),
                     "t_grid": list(T_GRID)}, "sections": {}}


def jnum(x, digits=10):
    """string form that survives 1e-400 and 1e+400 in JSON."""
    try:
        return mp.nstr(mp.mpf(x), digits)
    except Exception:
        return str(x)


def jf(x, digits=10):
    return float(mp.mpf(x)) if abs(mp.mpf(x)) < 1e300 and mp.mpf(x) != 0 else (0.0 if mp.mpf(x) == 0 else jnum(x))


# ---------------------------------------------------------------- truth: G

_GL = {}


def gl_nodes(npts, dps):
    key = (npts, dps)
    if key in _GL:
        return _GL[key]
    xs0, _ = np.polynomial.legendre.leggauss(npts)
    with mp.workdps(dps + 40):
        X, W = [], []
        for x0 in xs0:
            x = mp.mpf(repr(float(x0)))
            dP = mp.mpf(1)
            for _ in range(3):
                pk1, pk = mp.mpf(1), x
                for kk in range(2, npts + 1):
                    pk1, pk = pk, ((2 * kk - 1) * x * pk - (kk - 1) * pk1) / kk
                Pn, Pm1 = pk, pk1
                dP = npts * (x * Pn - Pm1) / (x * x - 1)
                x = x - Pn / dP
            W.append(2 / ((1 - x * x) * dP * dP))
            X.append(x)
    _GL[key] = (X, W)
    return X, W


def gerr_coef(npts):
    """per-panel relative error bound of GL-npts on a phase-pi panel."""
    return mp.e ** ((2 * npts) * mp.log(mp.pi / 2) - mp.loggamma(2 * npts + 1))


def G_int(a, t, npts=30, dps=80):
    """truth: int_{-1}^{1} phi(u) e^{w a u} du, w = a(0.5 + i t).
    returns (val, Sabs) with |error| <= gerr_coef(npts) * Sabs."""
    am = mp.mpf(repr(float(a)))
    Xn, Wn = gl_nodes(npts, dps)
    with mp.workdps(dps):
        w = am * (mp.mpf('0.5') + 1j * mp.mpf(repr(float(t))))
        wa = w * am
        imw = abs(mp.im(wa))
        if imw == 0:
            edges = [mp.mpf(-1), mp.mpf(1)]
        else:
            step = mp.pi / imw
            edges = [mp.mpf(-1)]
            u = mp.mpf(-1) + step
            while u < 1:
                edges.append(u)
                u += step
            edges.append(mp.mpf(1))
        tot = mp.mpf(0)
        sabs = mp.mpf(0)
        for lo, hi in zip(edges[:-1], edges[1:]):
            mid, half = (lo + hi) / 2, (hi - lo) / 2
            if half == 0:
                continue
            acc = mp.mpf(0)
            accus = mp.mpf(0)
            for x, wq in zip(Xn, Wn):
                uu = mid + half * x
                val = mp.e ** (-K / (1 - uu * uu)) * mp.e ** (wa * uu)
                acc += wq * val
                accus += abs(wq) * abs(val)
            tot += half * acc
            sabs += half * accus
        return tot, sabs


def g_truth_v(a, t, npts=30, dps=80):
    """committed convention: V = a * L(w) = a^2 * int_{-1}^{1} phi e^{w a u} du;
    returns (|v|, Gerr)."""
    val, sabs = G_int(a, t, npts, dps)
    am = mp.mpf(repr(float(a)))
    return abs(am * am * val), abs(am * am) * gerr_coef(npts) * sabs


# ------------------------------------------------------------ rule evaluators

_XF_CACHE = {}


def rule_xf(a, m):
    key = (a, m)
    if key not in _XF_CACHE:
        X, W = r59.phi_weights(a, panels=PANELS, m=m)
        f = r59.phi_fun(X, a, K) * W
        _XF_CACHE[key] = (X, f)
    return _XF_CACHE[key]


def rule_exact_v(a, t, m=M0, dps=60):
    """exact value of the committed rule sum (stored floats exact)."""
    X, f = rule_xf(a, m)
    with mp.workdps(dps):
        am = mp.mpf(repr(float(a)))
        w = am * (mp.mpf('0.5') + 1j * mp.mpf(repr(float(t))))
        s = mp.mpc(0)
        for xi_, fi in zip(X, f):
            s += mp.mpf(repr(float(fi))) * mp.e ** (w * mp.mpf(repr(float(xi_))))
        return abs(am * s)


_FW_CACHE = {}


def float_xw(a, m):
    key = (a, m)
    if key not in _FW_CACHE:
        _FW_CACHE[key] = r59.phi_weights(a, panels=PANELS, m=m)
    return _FW_CACHE[key]


def float_v(a, t, m=M0):
    X, W = float_xw(a, m)
    s = np.array([a * (0.5 + 1j * t)])
    return abs(a * r59.phi_laplace(a, K, s, XW=(X, W))[0])


def status_of(vr, vt, gerr):
    """frozen C2 status."""
    vr, vt, gerr = mp.mpf(vr), mp.mpf(vt), mp.mpf(gerr)
    fl = max(vt, gerr)
    if abs(vr - vt) <= mp.mpf('1e-3') * vt:
        return "OK"
    if abs(vr - vt) > mp.mpf('1e-3') * fl and abs(vr) > 3 * fl:
        return "UNRESOLVED"
    return "GRAY"


# ---------------------------------------------------------------- setup

print("setup...", flush=True)
rho, nodes, values, fam, xw, gram, a_mat, _, _ = r37.setup(False)
base, _bi = r37.min_h1(gram, a_mat, np.ones(len(nodes), complex))
corr, _ci = r37.min_h1(gram, a_mat, np.asarray(values, complex))
AFAM = [float(a_) for a_, _th in fam]
THFAM = [float(th) for _a, th in fam]
NFAM = len(fam)
print("fam:", [(round(a_, 3), round(th, 3)) for a_, th in fam], flush=True)
OUT["owner"] = {"rho": [float(rho.real), float(rho.imag)],
                "base_abs": [jnum(abs(b)) for b in base],
                "corr_abs": [jnum(abs(c)) for c in corr],
                "fam": [[round(a_, 4), round(th, 4)] for a_, th in fam]}

sec = OUT["sections"]

# C0 control (a)
vt0, ge0 = g_truth_v(1.76, 2.0, npts=30, dps=80)
vf0 = float_v(1.76, 2.0)
c0a = abs(vf0 - float(vt0)) / float(vt0)
print("C0a: truth=%.6e float=%.6e rel=%.3e" % (float(vt0), vf0, c0a), flush=True)
sec["C0a_soft_control"] = {"a": 1.76, "t": 2.0, "truth": jnum(vt0),
                           "float": jnum(vf0), "rel": c0a}

# ------------------------------------------------- C2: horizon table
print("C2 horizon table...", flush=True)
rows = []
for j in range(NFAM):
    a_, th_ = AFAM[j], THFAM[j]
    for t_ in T_GRID:
        vt, ge = g_truth_v(a_, t_, npts=30, dps=80)
        vr = rule_exact_v(a_, t_, m=M0, dps=70)
        st = status_of(vr, vt, ge)
        rows.append({"j": j + 1, "a": a_, "th": th_, "t": t_,
                     "vt": jnum(vt), "gerr": jnum(ge), "vr400": jnum(vr),
                     "rel": jnum(abs(vr - vt) / max(vt, ge)), "status": st})
    print("  fam %2d a=%.3f done (%.0fs)" % (j + 1, a_, time.time() - t0), flush=True)
sec["C2_horizon_rows"] = rows
hor = {}
for r in rows:
    if r["status"] == "UNRESOLVED":
        hor.setdefault(r["j"], r["t"])
sec["C2_horizon"] = {str(j): hor.get(j) for j in range(1, NFAM + 1)}

# ------------------------------------------------- C3: aliasing cliff
print("C3 cliff...", flush=True)
cliff = []
for j in range(NFAM):
    a_ = AFAM[j]
    ts = 4800.0 / (a_ * a_)
    v = []
    for f in (0.9, 1.0, 1.1):
        v.append((f, float_v(a_, f * ts, m=M0), float_v(a_, f * ts, m=6400)))
    jump400 = v[2][1] / max(v[0][1], 1e-300)
    cliff.append({"j": j + 1, "a": a_, "t_star": ts,
                  "v400_0p9": jnum(v[0][1]), "v400_1p0": jnum(v[1][1]),
                  "v400_1p1": jnum(v[2][1]), "jump400": jump400,
                  "v6400_1p1": jnum(v[2][2])})
print("  cliff done (%.0fs)" % (time.time() - t0), flush=True)
sec["C3_cliff"] = cliff

# ------------------------------------------------- C1: truth pinning set
print("C1 pinning...", flush=True)
PIN = [(1.76, 2.0), (1.76, 30.0), (1.76, 72.33), (2.288, 9.5), (2.288, 40.0),
       (2.992, 40.24), (3.696, 60.0), (4.048, 80.0), (4.752, 40.24),
       (4.752, 79.42), (4.752, 213.0), (4.752, 268.0)]
pin_rows = []
for (a_, t_) in PIN:
    v1, s1 = G_int(a_, t_, npts=60, dps=200)
    v2, _ = G_int(a_, t_, npts=80, dps=200)
    v3, _ = G_int(a_, t_, npts=60, dps=260)
    rel_n = abs(v1 - v2) / max(abs(v1), abs(v2))
    rel_d = abs(v1 - v3) / max(abs(v1), abs(v3))
    pin_rows.append({"a": a_, "t": t_, "G": jnum(abs(v1)),
                     "rel_npts": jnum(rel_n), "rel_dps": jnum(rel_d),
                     "pinned": bool(rel_n <= 1e-20 and rel_d <= 1e-20)})
    print("  pin a=%.3f t=%.2f G=%.6e reln=%.2e reld=%.2e" % (
        a_, t_, float(abs(v1)), float(rel_n), float(rel_d)), flush=True)
sec["C1_pinning"] = pin_rows

# ------------------------------------------------- C4: headline + profiles
print("C4 headline xi=35, xi=20 ...", flush=True)
head = {}
for XI_HEAD in (35.0, 20.0):
    hr = []
    for j in range(NFAM):
        a_, th_ = AFAM[j], THFAM[j]
        t_ = th_ - 2 * math.pi * XI_HEAD
        deep = abs(t_) > 150 and a_ > 3.9
        vt, ge = g_truth_v(a_, t_, npts=(130 if deep else 60), dps=(480 if deep else 200))
        vr = rule_exact_v(a_, t_, m=M0, dps=70)
        st = status_of(vr, vt, ge)
        v40 = float_v(a_, t_, m=M0)
        v16 = float_v(a_, t_, m=1600)
        v64 = float_v(a_, t_, m=6400)
        hr.append({"j": j + 1, "a": a_, "th": th_, "t": t_,
                   "vt": jnum(vt), "gerr": jnum(ge), "status": st,
                   "v400_float": jnum(v40), "v1600_float": jnum(v16),
                   "v6400_float": jnum(v64), "v400_exact": jnum(vr)})
    head[XI_HEAD] = hr
    print("  xi=%.1f done (%.0fs)" % (XI_HEAD, time.time() - t0), flush=True)
sec["C4_headline_rows"] = {str(k): v for k, v in head.items()}

# committed window profile via the committed 2037 path, m in {400,1600,6400}
print("C4 window profiles...", flush=True)
prof = {}
for m_prof, hh in ((400, 0.01), (1600, 0.01), (6400, 0.02)):
    xg = np.arange(-XI_MAX, XI_MAX + hh / 2, hh)
    s = 0.5 - 2j * np.pi * xg
    xwm = [r59.phi_weights(a_, panels=PANELS, m=m_prof) for a_, _t in fam]
    v = r80.family_values(fam, K, s, xwm)
    lb = base @ v
    cc = corr @ v
    p = np.real(r59.P_from_nodes(xg, r80.counterpart_nodes(rho)))
    g = p * p * np.abs(lb) ** 2 * np.abs(cc) ** 2
    ker = r59.rig.sigma_vec(2 * np.pi * xg)
    ps = r59.rig.prime_powers_up_to(math.exp(9.504))
    for num, w in ps:
        ker = ker + 2 * w / math.sqrt(num) * np.cos(2 * np.pi * xg * math.log(num))
    del v
    # cumulative Q(X) via trapezoid
    fx = ker * g
    Qcum = np.concatenate([[0.0], np.cumsum(0.5 * (fx[1:] + fx[:-1]) * hh)])
    Xs = [5, 10, 15, 20, 25, 30, 35, 40]
    # Q(X) symmetric window: integral over [-X, X]
    qsym = {}
    for X in Xs:
        i2 = int(round((X + XI_MAX) / hh))
        i1 = int(round((-X + XI_MAX) / hh))
        qsym[str(X)] = float(Qcum[i2] - Qcum[i1])
    samp = {}
    for X in (0, 5, 10, 15, 20, 25, 30, 35, 39.747):
        idx = int(np.argmin(np.abs(xg - X)))
        samp[str(X)] = {"lb": jnum(abs(lb[idx])), "cc": jnum(abs(cc[idx])),
                        "g": jnum(abs(g[idx])), "ker": jnum(abs(ker[idx]))}
    prof[str(m_prof)] = {"h": hh, "Q_sym": qsym,
                         "Q_full": float(Qcum[-1] - Qcum[0]),
                         "samples": samp,
                         "abs_mass_full": float(np.sum(np.abs(fx[:-1]) * hh)),
                         "C_max": jnum(np.max(np.abs(p) * np.abs(lb) * np.abs(cc))),
                         "max_g": jnum(np.max(g))}
    print("  profile m=%d h=%.2f Qfull=%.6e (%.0fs)" % (
        m_prof, hh, prof[str(m_prof)]["Q_full"], time.time() - t0), flush=True)
sec["C4_profiles"] = prof

# ------------------------------------------- C5: L4 tail from landed rungs
print("C5 L4 tail...", flush=True)
ps = r59.rig.prime_powers_up_to(math.exp(9.504))
C_book = sum(2.0 * w / math.sqrt(num) for num, w in ps)
NBUF = 1.0
sig_peak = 0.0
for xg2 in np.linspace(XI_MAX, 400.0, 2000):
    sig_peak = max(sig_peak, abs(float(r59.rig.sigma_vec(np.array([2 * np.pi * xg2]))[0])))
env_const = C_book + sig_peak + 2.0


def v_bound(a_, t_, r_):
    # rungs are for the u-integral: |int_{-1}^{1} phi e^{a s u} du|
    #   <= e^{|Re(a s)|} N_r / |a s|^r,  with |a s| = a^2 |0.5 + i t|;
    # committed convention V = a * L_phys = a^2 * (u-integral):
    #   |v| <= e^{0.5 a^2} N_r / (a^{2r-2} |0.5 + i t|^r).
    hw = math.hypot(0.5, t_)
    return math.exp(0.5 * a_ * a_) * RUNGS[r_ - 1] / (a_ ** (2 * r_ - 2) * hw ** r_)


def lb_cc_bounds(xi):
    lb = cc = 0.0
    for j in range(NFAM):
        t_ = THFAM[j] - 2 * math.pi * xi
        b = min(v_bound(AFAM[j], t_, 1), v_bound(AFAM[j], t_, 2), v_bound(AFAM[j], t_, 3))
        lb += abs(base[j]) * b
        cc += abs(corr[j]) * b
    return lb, cc


Tb = {}
for X in (40.0, 60.0, 100.0, 200.0):
    xg3 = np.linspace(X, X * 21.0, 4000)
    p3 = np.real(r59.P_from_nodes(xg3, r80.counterpart_nodes(rho)))
    lbv = np.empty_like(xg3)
    ccv = np.empty_like(xg3)
    for i_, xi_ in enumerate(xg3):
        lbv[i_], ccv[i_] = lb_cc_bounds(xi_)
    integ = env_const * p3 * p3 * lbv ** 2 * ccv ** 2
    Tb[str(X)] = float(np.sum(0.5 * (integ[1:] + integ[:-1]) * (xg3[1:] - xg3[:-1])))
    print("  T_bnd(%.0f)=%.6e  (%.0fs)" % (X, Tb[str(X)], time.time() - t0), flush=True)
sec["C5_L4"] = {"C_book": C_book, "sigma_peak": sig_peak, "env_const": env_const,
                "T_bnd": Tb, "kill_fires": bool(Tb["40.0"] > BUDGET)}

# ------------------------------------------------- verdicts
qv400 = prof["400"]["Q_full"]
qv1600 = prof["1600"]["Q_full"]
qv6400 = prof["6400"]["Q_full"]
c0b = abs(abs(qv400) - Q_COMMITTED) / Q_COMMITTED
sign_ok = (qv400 * Q_COMMITTED_SIGN > 0)
print("C0b: Q_400=%.10e vs committed q_h1=-1.11119e20 (|Q|=%.4e) rel=%.3e sign_ok=%s"
      % (qv400, Q_COMMITTED, c0b, sign_ok), flush=True)
sec["C0b_window_control"] = {"Q_400": qv400, "committed_abs": Q_COMMITTED,
                             "committed_sign": Q_COMMITTED_SIGN,
                             "committed_q_h1_2037": "-1.11119e20",
                             "rel": c0b, "sign_ok": bool(sign_ok)}


def overall():
    if c0a > 1e-3 or c0b > 2e-2 or not sign_ok:
        return "CONTROL-FAIL"
    v = []
    if sec["C5_L4"]["kill_fires"]:
        v.append("L4-PRICE-FAIL")
    dom = (abs(qv1600) <= 0.5 * abs(qv400)) and (abs(qv400 - qv1600) >= 1e19)
    v.append("PHI-HORIZON-DOMINANT" if dom else "PHI-HORIZON-NOT-DOMINANT")
    return " + ".join(v)


OUT["verdict"] = overall()
OUT["elapsed_s"] = round(time.time() - t0, 1)
print("VERDICT:", OUT["verdict"], flush=True)

os.makedirs(os.path.join(ROOT, "results"), exist_ok=True)
with open(os.path.join(ROOT, "results", "2053_l4_horizon.json"), "w") as fh:
    json.dump(OUT, fh, indent=1)
print("wrote results/2053_l4_horizon.json", flush=True)