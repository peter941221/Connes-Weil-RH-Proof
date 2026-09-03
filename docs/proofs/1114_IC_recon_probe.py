"""1114b - I-C recon probe (MODEL, declared): detector-window radius
a_det(k) table + spectral band fraction f_band(k). Companion to
1114_IC_problem_statement.md and 1114_IC_recon_preregistration.md.
Everything is scaling reconnaissance; certifies nothing. RH NOT claimed.
"""
import json
import math
import os

import mpmath
import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
mpmath.mp.dps = 30

KPROBE = [1, 2, 3, 4, 5, 7, 10, 15, 20]
KMAX = 170                     # ball closure: max T+R = 284 at k=20,
                               # gamma_170 > 300 (run 1 truncated at 219)
A_CERT_MAX = 4.0               # 1112/1113 certified reach
HORIZON = 5.0                  # 1113 STRADDLE horizon (registered)

print("computing zeta zeros (mpmath zetazero, dps=30)...")
gammas = {}
for j in range(1, KMAX + 1):
    gammas[j] = float(mpmath.im(mpmath.zetazero(j)))
G1 = gammas[1]
print(f"gamma_1 = {G1:.6f}   gamma_{KMAX} = {gammas[KMAX]:.4f}")


def f_band(a, T, M=1 << 20):
    """Fraction of model-detector spectral energy inside |xi| <= gamma_1.
    g(u) = chi(u/a) cos(T u), zero-padded 4a span, rFFT bin energy."""
    x = np.linspace(-2.0 * a, 2.0 * a, M, endpoint=False)
    v = x / a
    chi = np.zeros_like(v)
    inside = (v > -1.0) & (v < 1.0)
    w = 1.0 - v[inside] ** 2
    chi[inside] = np.exp(-1.0 / w)
    g = chi * np.cos(T * x)
    G = np.fft.rfft(g)
    e = np.abs(G) ** 2
    total = e.sum()
    dxi = 2.0 * math.pi / (x[1] - x[0]) / M
    nb = int(math.floor(G1 / dxi)) + 1
    return float(e[:nb].sum() / total), dxi


rows = []
print("\n==== Part 1: a_det model table (declared MODEL, not certificates) ====")
print("  k   gamma_k      n0   R_ball   N_ball  dmin      "
      "log2C     n_lo  n_hi  a_det_lo  a_det_hi  def_lo  def_hi")
for k in KPROBE:
    T = gammas[k]
    n0 = math.ceil(math.log2(T)) - 1          # min n : T < 2^(n+1)
    assert T < 2.0 ** (n0 + 1), (k, n0)
    R = 2.0 ** (n0 + 1) + 2.0 + math.sqrt(1.5 ** 2 + T * T)
    assert gammas[KMAX] > T + R, f"ball OPEN at k={k}: T+R={T + R:.1f}"
    ball = []
    for j, gj in gammas.items():
        if j == k or gj > T + R:
            continue
        d = abs(gj - T)
        if d < R:
            ball.append(d)
    N_ball = len(ball)
    dmin = min(ball)
    logC = sum(math.log2(1.0 + R / d) for d in ball)
    n_hi = max(1, math.ceil(logC))
    n_lo = math.ceil(math.log2(T * T + 4.0))
    a_lo, a_hi = n_lo + 2, n_hi + 2
    fb_lo, dxi = f_band(a_lo, T)
    fb_hi, _ = f_band(a_hi, T)
    rows.append(dict(k=k, gamma=T, n0=n0, R=R, N_ball=N_ball, dmin=dmin,
                     log2C=logC, n_lo=n_lo, n_hi=n_hi, a_det_lo=a_lo,
                     a_det_hi=a_hi, f_band_lo=fb_lo, f_band_hi=fb_hi,
                     def_lo=a_lo - HORIZON, def_hi=a_hi - HORIZON))
    print(f" {k:3d} {T:9.4f}  {n0:3d} {R:8.2f} {N_ball:6d} {dmin:8.4f}  "
          f"{logC:8.1f}  {n_lo:4d} {n_hi:4d} {a_lo:8d} {a_hi:9d} "
          f"{a_lo - HORIZON:7.0f} {a_hi - HORIZON:7.0f}")

print("\n==== Part 2: spectral band fraction (favourable branch a_det_lo / "
      "a_det_hi) ====")
print("  k   T=gamma_k    f_band(a_lo)   f_band(a_hi)   bin xi-res (a_lo)")
for r in rows:
    print(f" {r['k']:3d} {r['gamma']:9.4f}   {r['f_band_lo']:.4e}     "
          f"{r['f_band_hi']:.4e}     {math.pi / r['a_det_lo']:.4f}")

print("\n==== registered expectation check (§2, REPORT only, no patch) ====")
ok_r1 = rows[0]["a_det_lo"] >= 8
print(f"R1 a_det_lo(k=1) = {rows[0]['a_det_lo']} >= 8: "
      f"{'OK' if ok_r1 else 'FALSIFIED - revisit 1114 framing'}")
mono = all(rows[i + 1]["a_det_lo"] >= rows[i]["a_det_lo"] - 2
           for i in range(len(rows) - 1))
print(f"R1b growth (tol 2): {'OK' if mono else 'reported'}")
fb1 = rows[0]["f_band_lo"]
in_range = 0.3 <= fb1 <= 0.7
print(f"R2a f_band(1) = {fb1:.3f} in [0.3, 0.7]: "
      f"{'OK' if in_range else 'FALSIFIED - report'}")
r2b = all(r["f_band_lo"] < 5e-2 for r in rows[1:])
dec = all(rows[i + 1]["f_band_lo"] < rows[i]["f_band_lo"]
          for i in range(1, len(rows) - 1))
print(f"R2b f_band(k>=2) < 5e-2: {'OK' if r2b else 'FALSIFIED - report'}; "
      f"monotone decreasing: {'OK' if dec else 'report'}")
r3 = all(r["def_hi"] >= 11 for r in rows)
print(f"R3 deficit_hi >= 11 all k: {'OK' if r3 else 'FALSIFIED - report'}")
print(f"horizon comparison: min a_det_lo = {min(r['a_det_lo'] for r in rows)} "
      f"(certified reach a_max = 4, horizon = 5)")

out = dict(record="1114b", model=True,
           constants=dict(KPROBE=KPROBE, KMAX=KMAX, G1=G1,
                          A_CERT_MAX=A_CERT_MAX, HORIZON=HORIZON),
           rows=rows)
path = os.path.join(HERE, "1114_IC_recon.json")
with open(path, "w") as f:
    json.dump(out, f, indent=1)
print(f"\nwrote {path}")
print("DONE (model reconnaissance; RH NOT claimed; no map change)")
