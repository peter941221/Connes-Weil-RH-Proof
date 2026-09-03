"""1106 - in-house F-pack completion (F.4 ablation / F.5 coupling / F.6
pure compression). Uses the anchor-verified shared implementation
1105_weil_identity_bundle/f0.py; assertion layer per
docs/proofs/1106_fpack_completion_preregistration.md.
Diagnostic float64; RH not claimed."""
import os
import sys

import numpy as np

BUNDLE = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                      "1105_weil_identity_bundle")
sys.path.insert(0, BUNDLE)
import f0

PEAK = 5.372183

F1_ANCHORS = {
    (2.0, 8): dict(top_arch=0.854466, min_prime=-0.858729,
                    top_arch_minus_prime=1.712992),
    (4.0, 8): dict(top_arch=1.781109, min_prime=-1.781212,
                    top_arch_minus_prime=3.562321),
}

# external F.6 reference table (their report, same shared f0)
F6_REF = {1.0: (0.122845, 2.455647), 2.0: (0.854466, 3.412379),
          4.0: (1.781109, 4.311969), 6.0: (2.593877, 4.716738),
          10.0: (3.789978, 5.055632)}


def main():
    print("1106 in-house F-pack completion "
          "(pre-reg: 1106_fpack_completion_preregistration.md)")
    print(f"python={sys.version.split()[0]} numpy={np.__version__}")

    worst = 0.0
    for (a, K), ref in F1_ANCHORS.items():
        r = f0.tops(a, K)
        for key, val in ref.items():
            worst = max(worst, abs(r[key] - val))
    print(f"f0 anchor drift = {worst:.2e} (abort > 2e-3)")
    if worst > 2e-3:
        print("VERDICT: ABORT-ANCHOR")
        return

    # ---- F.4 ablation (a=2, K=8) ------------------------------------------
    subsets = [(), (0.0,), (0.5,), (1.0,), (0.0, 0.5), (0.0, 1.0),
               (0.5, 1.0), (0.0, 0.5, 1.0)]
    tops_by_drop = {}
    for sub in subsets:
        r = f0.tops(2.0, 8, drop_moments=sub)
        tops_by_drop[sub] = r["top_total"]
    base = tops_by_drop[()]
    print(f"\nF.4 ablation a=2 K=8 (baseline top_total={base:+.6f}):")
    singles = {}
    for s in (0.0, 0.5, 1.0):
        jump = tops_by_drop[(s,)] - base
        singles[s] = jump
        print(f"  drop {{{s:g}}}          top={tops_by_drop[(s,)]:+.6f} "
              f"jump={jump:+.6f}")
    for sub in [(0.0, 0.5), (0.0, 1.0), (0.5, 1.0), (0.0, 0.5, 1.0)]:
        name = ",".join(f"{x:g}" for x in sub)
        print(f"  drop {{{name:<5}}}     top={tops_by_drop[sub]:+.6f}")
    f4_i = singles[0.5] == max(singles.values()) and singles[0.5] > 0
    f4_ii = abs(tops_by_drop[(0.0, 1.0)]) <= 1e-3
    f4 = f4_i and f4_ii
    print(f"F.4: half-largest={f4_i} (jumps "
          f"{singles[0.0]:+.4f}/{singles[0.5]:+.4f}/{singles[1.0]:+.4f}), "
          f"drop-0-1 pinned={f4_ii} ({tops_by_drop[(0.0, 1.0)]:+.2e}) "
          f"=> {'PASS' if f4 else 'FAIL'}")

    # ---- F.5 weight coupling ----------------------------------------------
    deltas = [-0.1, -0.01, -0.001, 0.0, 0.001, 0.01, 0.1]
    f5 = True
    print("\nF.5 weight coupling:")
    for a in (2.0, 4.0):
        base_r = f0.tops(a, 8)
        A = base_r["top_arch"]
        vals = {d: f0.tops(a, 8, scale=1.0 + d)["top_total"] for d in deltas}
        slope = (vals[0.001] - vals[-0.001]) / 0.002
        ratio = slope / (-A)
        if vals[0.0] >= 0:
            dstar = 0.0
        else:
            neg = [d for d in deltas if vals[d] >= 0]
            dstar = min(neg, key=abs) if neg else float("nan")
        ok = not (0.8 <= ratio <= 1.2) and abs(dstar) <= 1e-3
        f5 = f5 and ok
        print(f"  a={a:g}: tops " +
              " ".join(f"{vals[d]:+.1e}" for d in deltas))
        print(f"       slope={slope:+.4f} ratio=slope/-A={ratio:+.3f} "
              f"delta*={dstar:+.1e} => {'PASS' if ok else 'FAIL'}")
    print(f"F.5: {'PASS' if f5 else 'FAIL'}")

    # ---- F.6 pure compression ----------------------------------------------
    f6 = True
    print("\nF.6 pure compression (no prime term), peak = "
          f"{PEAK:.6f}:")
    v_vals, full_vals = [], []
    for a in (1.0, 2.0, 4.0, 6.0, 10.0):
        v = f0.tops(a, 8, shifts=[], weights=[])["top_arch"]
        full = f0.tops(a, 8, drop_moments=(0.0, 0.5, 1.0),
                       shifts=[], weights=[])["top_arch"]
        v_vals.append(v); full_vals.append(full)
        ref_v, ref_f = F6_REF[a]
        ok_a = abs(v - ref_v) <= 1e-2 and abs(full - ref_f) <= 1e-2
        print(f"  a={a:<4g} V={v:+.6f} (gap {PEAK - v:+.3f})  "
              f"full={full:+.6f} (gap {PEAK - full:+.3f})  "
              f"ref-match={'ok' if ok_a else 'MISS'}")
        f6 = f6 and ok_a
    mono = (all(b > a for a, b in zip(v_vals, v_vals[1:])) and
            all(b > a for a, b in zip(full_vals, full_vals[1:])))
    f6 = f6 and mono
    print(f"F.6: monotone={mono}, refs matched => {'PASS' if f6 else 'FAIL'}")

    print(f"\nVERDICT: {'PASS' if (f4 and f5 and f6) else 'FAIL'}  "
          f"F4={f4} F5={f5} F6={f6}")
    print("DONE")


if __name__ == "__main__":
    main()
