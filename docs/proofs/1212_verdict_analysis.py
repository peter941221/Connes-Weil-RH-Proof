"""1212 post-run verdict analysis (reads 1212_probe_results.json).

Registered questions (1212 preregistration, law 42: no rescoping):
  Q1  leading asymptotics c_n of T_n (candidate: linear in 2 R_n)
  Q2  does FP_n = T_n - c_n settle, and to what?
  H1  |FP_inf - qw(g)| <= 10 * eps_effective (measured, worst path)
  H2  FP settles outside the band, or fails to settle
  ABORTED-UNINFORMATIVE if Q1 does not separate from noise (1097)

Method (law 60: two-point fits only, no third-point prediction):
  physical trace Tn^cont = Tn * dt^2 -- TWO factors of dt: one from the
  trace sum tr_disc ~ tr_cont/dt, one from the kernel integral inside
  W[i,i] = sum_k |gt(t_k - t_i)|^2 win(t_k) ~ f0/dt (verified: bulk*dt^2
  = 2 R_n * f0 exactly).  slope alpha_[n1,n2] from CONSECUTIVE rungs on
  the COARSE grade; FP_n^fine = Tn^cont_fine(n) - alpha * 2 R_n on the
  FINE grade; eps_effective = worst |coarse - fine| relative discrepancy
  of Tn^cont across the ladder.
"""
import json

import os

HERE = os.path.dirname(os.path.abspath(__file__))

with open(os.path.join(HERE, "1212_probe_results.json")) as fh:
    d = json.load(fh)

rows = d["results"]
qw = d["qw"]["qw"]
coarse = [r for r in rows if r["N"] == 8192]
fine = [r for r in rows if r["N"] == 16384]
for g in (coarse, fine):
    g.sort(key=lambda r: r["n"])


def tc(r):
    return r["Tn"] * r["dt"] ** 2


print(f"qw(g) target = {qw:+.6e}")
print()
print("=== per-rung readouts (physical: Tn^cont = Tn*dt^2) ===")
print(f"{'n':>3} {'Rn':>7} {'N':>6} {'Tn^cont':>14} {'FP/bulk':>10} "
      f"{'bulk^cont=2Rn*f0':>18} {'tail_gap':>9}")
for r in coarse + fine:
    bc = r["bulk"] * r["dt"] ** 2
    print(f"{r['n']:3d} {r['Rn']:7.2f} {r['N']:6d} {tc(r):+14.6e} "
          f"{r['Tn']/r['bulk']:10.6f} {bc:18.6e} {r['tail_gap']:9.1e}")

print()
print("=== dt-invariance of Tn^cont at each rung (coarse vs fine) ===")
dt_rel = []
for a, b in zip(coarse, fine):
    rel = abs(tc(a) - tc(b)) / max(abs(tc(b)), 1e-300)
    dt_rel.append(rel)
    print(f"n={a['n']:3d}: coarse {tc(a):+.6e}  fine {tc(b):+.6e}  "
          f"rel {rel:.3e}")

print()
print("=== Q1: consecutive two-point slopes of Tn^cont (fine grade) ===")
alphas = []
for a, b in zip(fine, fine[1:]):
    al = (tc(b) - tc(a)) / (2 * b["Rn"] - 2 * a["Rn"])
    alphas.append(al)
    print(f"[n={a['n']},n={b['n']}]: alpha = {al:+.6e}  "
          f"(relative to the constant part: {al/max(abs(tc(fine[0])),1e-300):+.2e})")

print()
print("=== Q2: FP_n = Tn^cont - alpha_bracketing * 2 R_n (fine grade) ===")
fp = {}
for r in fine:
    cands = [al for al, (a, b) in zip(alphas, zip(fine, fine[1:]))
             if a["n"] <= r["n"] <= b["n"]]
    al = cands[0] if cands else alphas[-1] if alphas else 0.0
    fp[r["n"]] = tc(r) - al * 2 * r["Rn"]
    print(f"n={r['n']:3d}: FP_n = {fp[r['n']]:+.6e}  "
          f"FP_n/qw = {fp[r['n']]/qw:+.4f}")

if len(fp) >= 2 and dt_rel:
    ns = sorted(fp)
    diffs = [abs(fp[b] - fp[a]) for a, b in zip(ns, ns[1:])]
    eps_tc = max(dt_rel)
    print()
    print("=== verdict inputs ===")
    print(f"consecutive |dFP|: {['%.3e' % x for x in diffs]}")
    print(f"eps_effective (worst coarse-vs-fine rel Tn^cont): {eps_tc:.3e}")
    last = fp[ns[-1]]
    band = 10 * max(diffs[-1] if diffs else 0.0, abs(last) * eps_tc)
    print(f"FP_last = {last:+.6e}; qw = {qw:+.6e}; "
          f"|FP_last - qw| = {abs(last - qw):.3e}")
    print(f"H1 band (10 * eps_effective) ~ {band:.3e}")
    print()
    settled = diffs[-1] <= band
    if settled and abs(last - qw) <= band:
        print("VERDICT SIGNAL: H1 (settles within band of qw)")
    elif settled:
        print("VERDICT SIGNAL: H2 (settles, but OUTSIDE the qw band)")
    else:
        print("VERDICT SIGNAL: H2 (fails to settle under the full ladder)")
