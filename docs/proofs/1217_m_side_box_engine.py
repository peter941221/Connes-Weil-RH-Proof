"""1217 - certified M-box engine for the TRUE Lean gate matrix (prereg
1217, committed a32e53e BEFORE this run; law 42).

Certified quantity (same-parity entries; mixed entries are exact zeros
by D1 and take [0,0] boxes):

  M_ij = (log(4pi)+gamma) * C_ij(0)
       + int_0^4 [e^{y/2}(C_ij(y)+C_ij(-y)) - 2 C_ij(0)]/(e^y - e^-y) dy
       + C_ij(0) * log(tanh 2)
       + sum_{n<=53 prime powers} Lambda(n)/sqrt(n)
             * (C_ij(log n) + C_ij(-log n)),
  C_ij(x) = int_{-2}^{2} w_i(s) w_j(x+s) ds,
  w_k(u) = P_k(u/2) exp(-1/(1-(u/2)^2)) on |u| < 2, else 0.

Engine (registered): mpmath dps=45; inner correlation and outer arch
composite Gauss-Legendre, 16 panels x 200 nodes (half rule 16x100 for
the |GL_n - GL_{n/2}| <= 1e-12 gates at EVERY required point); the
arch integrand is evaluated as the SINGLE expression (removable
singularity at y=0 - no split-term cancellation); constants enclosed
at +/-1e-14; per-entry error budget accumulated from registered
per-point caps + measured half-rule deltas, asserted <= 5e-10; outward
dyadic rounding at denominator 2^72; whitened-top inflation check
against U = -1.043377e-06 with 1e-8 slack.

Loop structure: per j, build the weighted inner tables T[l, x] =
w_l * w_j(x + s_l) on both inner rules (shared across i); per (i, j)
the correlations are single dot products with w_i on each grid.

Run modes:  --smoke   tiny config, times and gate-checks one pair
            (default) full registered run, checkpointed per (j, i)
"""
import json
import os
import sys
import time
from fractions import Fraction

import numpy as np

import mpmath as mp

SMOKE = "--smoke" in sys.argv

HERE = os.path.dirname(os.path.abspath(__file__))
OUT_JSON = os.path.join(HERE, "1217_m_boxes_cert.json")
CKPT = os.path.join(HERE, "1217_m_boxes_checkpoint.json")

A = 2                      # window half-width a = 2
K = 8
PANELS = 4 if SMOKE else 16
N_IN = 25 if SMOKE else 200        # inner nodes per panel (full rule)
N_OUT = 25 if SMOKE else 200       # outer nodes per panel (full rule)
GATE = mp.mpf("1e-12")
PER_POINT = mp.mpf("1e-11")        # registered per-value budget
CONST_EPS = mp.mpf("1e-14")        # constant enclosures
ENTRY_BUDGET_CAP = mp.mpf("5e-10")
DPS_DEN = 2 ** 72                  # outward dyadic grid
DPS = 30 if SMOKE else 45
mp.mp.dps = DPS

L4PG = mp.log(4 * mp.pi) + mp.euler
LT2 = mp.log(mp.tanh(2))


def gauss_legendre(n_per_panel, lo, hi):
    """Composite Gauss-Legendre nodes/weights, PANELS equal panels."""
    gx, gw = np.polynomial.legendre.leggauss(n_per_panel)
    xs, ws = [], []
    for b in range(PANELS):
        a0 = lo + (hi - lo) * b / PANELS
        a1 = lo + (hi - lo) * (b + 1) / PANELS
        mid = (mp.mpf(a0) + mp.mpf(a1)) / 2
        half = (mp.mpf(a1) - mp.mpf(a0)) / 2
        for g, w in zip(gx, gw):
            xs.append(mid + half * mp.mpf(float(g)))
            ws.append(half * mp.mpf(float(w)))
    return xs, ws


S_X, S_W = gauss_legendre(N_IN, -A, A)
S_XH, S_WH = gauss_legendre(N_IN // 2, -A, A)
Y_X, Y_W = gauss_legendre(N_OUT, 0, 4 * A)
Y_XH, Y_WH = gauss_legendre(N_OUT // 2, 0, 4 * A)

PRIME_POWERS = []
for n in range(2, 54):
    for p in range(2, n + 1):
        if n % p == 0 and all(n % q for q in range(2, p)):
            m2, k = n, 0
            while m2 % p == 0:
                m2 //= p
                k += 1
            if m2 == 1:
                PRIME_POWERS.append((n, mp.log(p), mp.log(n)))
                break
PRIME_POWERS.sort()
assert len(PRIME_POWERS) == 24

NP = len(PRIME_POWERS)
NYF = len(Y_X)                    # full outer nodes
NYH = len(Y_XH)                   # half outer nodes

IDX0 = 0
IDX_P = 1                                    # +ln: 1..24, -ln: 25..48
IDX_YF = 1 + 2 * NP                          # +y full: NYF, -y: NYF
IDX_YH = IDX_YF + 2 * NYF                    # +y half: NYH, -y: NYH
NCOL = IDX_YH + 2 * NYH


def legendre_vals(k, t):
    if k == 0:
        return mp.mpf(1)
    p0, p1 = mp.mpf(1), t
    for n in range(0, k - 1):
        p0, p1 = p1, ((2 * n + 3) * t * p1 - (n + 1) * p0) / (n + 2)
    return p1


def window(k, u):
    if abs(u) >= A:
        return mp.mpf(0)
    t = u / A
    return legendre_vals(k, t) * mp.exp(-1 / (1 - t * t))


# arch single-expression coefficients (per outer node, both grids):
# f(y) = [e^{y/2}(C(y)+C(-y)) - 2 C(0)] / D(y); the C part enters via
# unit-weight column sums folded with w_i, so keep e^{y/2}/D(y) here.
AF = [w * mp.exp(y / 2) / (mp.exp(y) - mp.exp(-y)) for y, w in zip(Y_X, Y_W)]
AF_H = [w * mp.exp(y / 2) / (mp.exp(y) - mp.exp(-y))
        for y, w in zip(Y_XH, Y_WH)]
DIF = [mp.exp(y) - mp.exp(-y) for y in Y_X]
PRIME_W = [lam / mp.sqrt(n) for n, lam, _ in PRIME_POWERS]

print(f"SMOKE={SMOKE} dps={DPS} panels={PANELS} n_in={N_IN} "
      f"n_out={N_OUT} cols={NCOL}", flush=True)


def build_table(j, s_x, s_w):
    """T[l, x] = w_l * w_j(x + s_l) for every required column x."""
    T = []
    for x in XS_ALL:
        col = []
        for s, w in zip(s_x, s_w):
            u = s + x
            if -A < u < A:
                t = u / A
                col.append(w * legendre_vals(j, t)
                           * mp.exp(-1 / (1 - t * t)))
            else:
                col.append(mp.mpf(0))
        T.append(col)   # column-major: T[x][l]
    return T


XS_ALL = ([mp.mpf(0)]
          + [ln for _, _, ln in PRIME_POWERS]
          + [-ln for _, _, ln in PRIME_POWERS]
          + list(Y_X) + [-y for y in Y_X]
          + list(Y_XH) + [-y for y in Y_XH])

def wi_vals(i, s_x):
    return [window(i, s) for s in s_x]


def corr_dot(col, s_w, wiv):
    """corr(i, j, x) for one column: the column already carries the
    quadrature weight w_l, so fold in only w_i(s_l)."""
    acc = mp.mpf(0)
    for wi, cv in zip(wiv, col):
        if wi != 0 and cv != 0:
            acc += wi * cv
    return acc


if SMOKE:
    t0 = time.time()
    Tf = build_table(0, S_X, S_W)
    t1 = time.time()
    print(f"table build full: {t1-t0:.1f}s", flush=True)
    Th = build_table(0, S_XH, S_WH)
    print(f"table build half: {time.time()-t1:.1f}s", flush=True)
    wiv = wi_vals(0, S_X)
    wivh = wi_vals(0, S_XH)
    cf = [corr_dot(c, S_W, wiv) for c in Tf]
    ch = [corr_dot(c, S_WH, wivh) for c in Th]
    worst = max(abs(a - b) for a, b in zip(cf, ch))
    print(f"smoke inner max delta: {mp.nstr(worst, 5)}  "
          f"({mp.nstr(GATE, 2)} gate)", flush=True)
    # arch value both outer grids (single-expression integrand)
    C0 = cf[IDX0]

    def arch_of(y_x, off, weights):
        acc = mp.mpf(0)
        for t in range(len(y_x)):
            ip = off + t
            im = off + len(y_x) + t
            num = mp.exp(y_x[t] / 2) * (cf[ip] + cf[im]) - 2 * C0
            acc += weights[t] * num / (mp.exp(y_x[t]) - mp.exp(-y_x[t]))
        return acc

    a_full = arch_of(Y_X, IDX_YF, Y_W)
    a_half = arch_of(Y_XH, IDX_YH, Y_WH)
    print(f"smoke arch full={mp.nstr(a_full, 12)}  "
          f"half={mp.nstr(a_half, 12)}  "
          f"delta={mp.nstr(abs(a_full - a_half), 5)}", flush=True)
    print(f"smoke C0={mp.nstr(C0, 15)}", flush=True)
    print(f"smoke total {time.time()-t0:.1f}s", flush=True)
    sys.exit(0)

# ---------------- official run ----------------
results = {}
gate_data = {"inner_max_delta": 0.0, "outer_max_delta": 0.0,
             "parity_max": 0.0}
WIV = {i: wi_vals(i, S_X) for i in range(K)}
WIVH = {i: wi_vals(i, S_XH) for i in range(K)}

for j in range(K):
    tJ = time.time()
    Tf = build_table(j, S_X, S_W)
    Th = build_table(j, S_XH, S_WH)
    print(f"j={j} tables {time.time()-tJ:.1f}s", flush=True)
    for i in range(K):
        tE = time.time()
        cf = [corr_dot(c, S_W, WIV[i]) for c in Tf]
        ch = [corr_dot(c, S_WH, WIVH[i]) for c in Th]
        inner_worst = max(abs(a - b) for a, b in zip(cf, ch))
        if inner_worst > GATE:
            print(f"GATE FAIL inner i={i} j={j}: "
                  f"{mp.nstr(inner_worst, 5)}", flush=True)
            sys.exit(3)
        gate_data["inner_max_delta"] = max(
            gate_data["inner_max_delta"], float(inner_worst))

        C0 = cf[IDX0]
        c0_delta = abs(C0 - ch[IDX0])

        prime = mp.mpf(0)
        prime_err = mp.mpf(0)
        for t in range(NP):
            ip, im = IDX_P + t, IDX_P + NP + t
            prime += PRIME_W[t] * (cf[ip] + cf[im])
            prime_err += PRIME_W[t] * (
                2 * PER_POINT + abs(cf[ip] - ch[ip])
                + abs(cf[im] - ch[im]))
            gate_data["parity_max"] = max(
                gate_data["parity_max"],
                float(abs(cf[ip] - cf[im])))

        arch = mp.mpf(0)
        arch_err = mp.mpf(0)
        for t in range(NYF):
            y = Y_X[t]
            ip, im = IDX_YF + t, IDX_YF + NYF + t
            d_pair = (abs(cf[ip] - ch[ip]) + abs(cf[im] - ch[im]))
            arch += Y_W[t] * (mp.exp(y / 2) * (cf[ip] + cf[im]) - 2 * C0) \
                / (mp.exp(y) - mp.exp(-y))
            arch_err += abs(Y_W[t]) * (
                mp.exp(y / 2) * (2 * PER_POINT + d_pair)
                + 2 * (PER_POINT + c0_delta)) / (mp.exp(y)
                                                 - mp.exp(-y))
        arch_h = mp.mpf(0)
        for t in range(NYH):
            y = Y_XH[t]
            ip, im = IDX_YH + t, IDX_YH + NYH + t
            arch_h += Y_WH[t] * (mp.exp(y / 2) * (cf[ip] + cf[im])
                                 - 2 * C0) / (mp.exp(y) - mp.exp(-y))
        outer_delta = abs(arch - arch_h)
        if outer_delta > GATE:
            print(f"GATE FAIL outer i={i} j={j}: "
                  f"{mp.nstr(outer_delta, 5)}", flush=True)
            sys.exit(4)
        gate_data["outer_max_delta"] = max(gate_data["outer_max_delta"],
                                           float(outer_delta))

        c0_err = PER_POINT + c0_delta
        budget = (mp.absmax(L4PG) * c0_err + arch_err
                  + 2 * sum(abs(w) / (mp.exp(Y_X[t]) - mp.exp(-Y_X[t]))
                            for t, w in enumerate(Y_W)) * c0_err
                  + mp.absmax(LT2) * c0_err
                  + abs(C0) * 2 * CONST_EPS + mp.absmax(L4PG) * CONST_EPS
                  + abs(C0) * CONST_EPS + CONST_EPS + prime_err)
        value = L4PG * C0 + arch + C0 * LT2 + prime
        if budget > ENTRY_BUDGET_CAP:
            print(f"BUDGET FAIL i={i} j={j}: {mp.nstr(budget, 5)}",
                  flush=True)
            sys.exit(5)

        val_frac = Fraction(mp.nstr(value, 40))
        bud_frac = Fraction(mp.nstr(budget, 25))
        lo = val_frac - bud_frac
        hi = val_frac + bud_frac
        lo_n = (lo.numerator * DPS_DEN) // lo.denominator
        hi_n = -((-hi.numerator * DPS_DEN) // hi.denominator)
        results[f"{i},{j}"] = {
            "mid": mp.nstr(value, 40),
            "budget": mp.nstr(budget, 12),
            "lo": f"{lo_n}/{DPS_DEN}",
            "hi": f"{hi_n}/{DPS_DEN}",
            "inner_delta": mp.nstr(inner_worst, 8),
            "outer_delta": mp.nstr(outer_delta, 8),
            "secs": round(time.time() - tE, 1),
        }
        print(f"  M[{i}][{j}] = {mp.nstr(value, 14)}  "
              f"bud {mp.nstr(budget, 4)}  "
              f"({results[f'{i},{j}']['secs']}s)", flush=True)
        with open(CKPT, "w") as fh:
            json.dump({"stage": f"j={j}", "results": results}, fh)
    del Tf, Th

cert = {
    "record": "1217",
    "prereg": "1217_m_side_box_certificate_preregistration.md",
    "config": {"dps": DPS, "panels": PANELS, "n_in": N_IN,
               "n_out": N_OUT, "prime_powers": NP, "den": DPS_DEN,
               "gate": "1e-12", "per_point": "1e-11",
               "entry_budget_cap": "5e-10"},
    "constants": {"log4pi_gamma": mp.nstr(L4PG, 35),
                  "log_tanh2": mp.nstr(LT2, 35),
                  "enclosure": "1e-14"},
    "gates": gate_data,
    "entries": results,
}
with open(OUT_JSON, "w") as fh:
    json.dump(cert, fh, indent=1)
print(f"WROTE {OUT_JSON}", flush=True)

# --- whitened-top inflation check (float64, independent of quadrature)
d = json.load(open(os.path.join(HERE, "1112_cert.json")))["classes"][0]


def rat_matrix(rows):
    return np.array([[float(Fraction(v)) for v in row] for row in rows])


from scipy.linalg import null_space  # noqa: E402

R = np.array(d["R_mid"], dtype=float)
Zn = null_space(R)
G = np.array(d["G_mid"], dtype=float)
Mlo = np.array([[float(Fraction(results[f"{i},{j}"]["lo"]))
                 for j in range(8)] for i in range(8)])
Mhi = np.array([[float(Fraction(results[f"{i},{j}"]["hi"]))
                 for j in range(8)] for i in range(8)])
Mmid = np.array([[float(Fraction(results[f"{i},{j}"]["mid"]))
                  for j in range(8)] for i in range(8)])
Pz = Zn.T @ G @ Zn
L = np.linalg.cholesky((Pz + Pz.T) / 2)
Li = np.linalg.inv(L)


def wtop(M):
    ev = np.linalg.eigvalsh(Li @ Zn.T @ M @ Zn @ Li.T)
    return float(ev[-1])


Delta = (Mhi - Mlo) / 2
infl = float(np.linalg.norm(
    Li @ Zn.T @ Delta @ Zn @ Li.T, ord=2))
top = wtop(Mmid)
print(f"whitened top(mid) = {top:+.6e}; inflation radius = {infl:.3e}; "
      f"top + infl = {top + infl:+.6e} vs U = {d['U']:+.6e} - 1e-8",
      flush=True)
cert["whitened_check"] = {"top_mid_recomputed": top,
                          "inflation_radius": infl,
                          "top_plus_inflation": top + infl,
                          "U": d["U"],
                          "pass": bool(top + infl <= d["U"] - 1e-8)}
with open(OUT_JSON, "w") as fh:
    json.dump(cert, fh, indent=1)
print("FALSIFIER-B " + ("PASS" if top + infl <= d["U"] - 1e-8 else "FAIL"),
      flush=True)
