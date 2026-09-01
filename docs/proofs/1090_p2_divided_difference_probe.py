# 1090 - PROBE-P2: does the divided-difference commutator give O(1) Hilbert-Schmidt legs?
#
# Design record: docs/proofs/1090_p2_divided_difference_gate.md (Q1 resolved by type
# argument; this probe answers Q2).  Reuses the 1067 rig via the committed 1068 module,
# so every identity gate and context build is byte-identical to record 1068.
#
# The pairData contract (PositiveTrace.lean:249-255) factors [C,K_S] = left^dagger . right
# with both legs square-summable; the OPTIMAL such split has leg HS-norm^2 equal to the
# nuclear norm, so l_tr1 (= ||[C,K_S]||_nuclear) is precisely the EXISTENCE WITNESS for an
# O(1)-leg pairData.  A term can supply its OWN bounded-leg pairData only if it is NUCLEAR
# (HS alone does not force bounded legs), so this probe decides Q2 by measuring, per octave:
#   anchors    l_hs_sq = ||L||_F^2 ,  l_tr1 = ||L||_nuclear          (reproduce 1068 s5.1)
#   named terms ck/kc : HS^2 AND nuclear norm of c@K_S and K_S@c       (per-term route test)
#   control    ks_unw = ||K_S||_F^2                                    (raw mass, expected grow)
# Decision:
#   anchor drift vs committed 1068            -> Q2-MISREAD (re-audit model first)
#   l_tr1 O(1) AND ck/kc nuclear O(1)         -> Q2-OPTIMAL-TERMS     (per-term pairData)
#   l_tr1 O(1) but ck/kc nuclear grow         -> Q2-OPTIMAL-COMBINED  (cancellation essential;
#                                                          named legs from the combined dD object)
# Deterministic; accept on the flushed log, not exit codes (AGENTS 7a).
#
# Run (WSL, log on the Linux side):
#   uv run --with numpy --with scipy python -u \
#     docs/proofs/1090_p2_divided_difference_probe.py > /tmp/1090_p2.log

import importlib.util
import json
import math
import os

import numpy as np

_HERE = os.path.dirname(os.path.abspath(__file__))


def _load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    assert spec is not None and spec.loader is not None, f"{path} not found"
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


# 1068 module: reuses the committed rig; exposes build_context / frob / trace_norm and its
# own `p` (the 1067 rig).  Its run() is __main__-guarded, so importing does not execute it.
m = _load("p1068", os.path.join(_HERE, "1068_root_commutator_ledger_probe.py"))

# Committed record-1068 s5.1 table for the DECIDING family {2,3,5}, k=1 (4-decimal source).
COMMITTED_1068 = {
    1025: dict(l_hs_sq=0.2086, l_tr1=1.3462),
    2049: dict(l_hs_sq=0.1855, l_tr1=1.3145),
    4097: dict(l_hs_sq=0.1739, l_tr1=1.2910),
    8193: dict(l_hs_sq=0.1688, l_tr1=1.2850),
}

ANCHOR_TOL = 2e-3          # deterministic rerun matches to ~1e-4; gate at 2e-3
O1_SLOPE = 0.15            # log-log slope threshold over the 8x window for "O(1)"


def measure_p2(F, ctx, c_amp):
    """One (grid) measurement on a built context: anchors + named terms + control."""
    K_S = ctx["K_S"]

    c = F.conj().T @ (c_amp[:, None] * F)          # C_k in t-basis (k=1), same as 1068 measure_k
    CK = c @ K_S                                   # named term  C o K_S
    KC = K_S @ c                                   # named term  K_S o C
    L = CK - KC                                    # [C, K_S] : the S2 ledger target

    out = dict(
        l_hs_sq=m.frob(L),                         # ||[C,K_S]||_F^2            (anchor)
        l_tr1=m.trace_norm(L),                     # ||[C,K_S]||_nuclear        (anchor + witness)
        ck_hs_sq=m.frob(CK),                       # named term C o K_S, HS^2
        kc_hs_sq=m.frob(KC),                       # named term K_S o C, HS^2
        ck_tr1=m.trace_norm(CK),                   # named term C o K_S, nuclear (per-term test)
        kc_tr1=m.trace_norm(KC),                   # named term K_S o C, nuclear (per-term test)
        ks_unw=m.frob(K_S),                        # raw K_S mass (control; expected to grow)
    )
    del c, CK, KC, L
    return out


def slope(first, last):
    """log-log growth exponent over the 8x sweep window; O(1) => ~0."""
    if first <= 0 or last <= 0:
        return float("nan")
    return (math.log(last / first)) / math.log(8.0)


def run():
    S = [2, 3, 5]                                   # deciding family only (per 1067/1068)
    K = 1.0                                         # primary Gaussian weight

    grid_list = json.loads(os.environ.get(
        "GRIDS_1090", "[[1025,20.0],[2049,20.0],[4097,20.0],[8193,20.0]]"))

    print("=== 1090 PROBE-P2: divided-difference two-HS-leg gate ({2,3,5}, k=1) ===")
    m.p.spotcheck_phase()

    rows = {}
    for (N, T) in grid_list:
        t, dt, xi, _dxi = m.p.grids(N, T)
        c_amp = np.exp(-0.25 * (K * xi) ** 2)       # C_k symbol amplitude (k=1), as in 1068

        F = m.p.dft_matrix(xi, t, N)
        E_diag = (t >= 0.0).astype(float)
        print(f"\n--- grid N={N} T={T:g} (dt={dt:.5f}, xi_max={abs(xi).max():.1f}) ---")

        phase = m.p.transport_phase(xi, S)
        gsym = float(np.max(np.abs(phase[::-1] - phase.conj())))
        assert gsym < 1e-10, f"transported phase loses reflection symmetry: {gsym:.2e}"
        print(f"[gate m-sym S={S}] {gsym:.2e}")

        HT = m.p.build_HT(phase, F, N)
        ctx = m.build_context(F, HT, E_diag, N, f"S={S}")
        r = measure_p2(F, ctx, c_amp)

        # ---- anchor cross-check vs committed record-1068 s5.1 (MODEL-MISREAD gate) ----
        ref = COMMITTED_1068[N]
        d_hs = abs(r["l_hs_sq"] - ref["l_hs_sq"])
        d_tr = abs(r["l_tr1"] - ref["l_tr1"])
        anchor_ok = d_hs < ANCHOR_TOL and d_tr < ANCHOR_TOL
        print(f"[anchor 1068] l_hs_sq {r['l_hs_sq']:.4f} vs {ref['l_hs_sq']} (d={d_hs:.2e}); "
              f"l_tr1 {r['l_tr1']:.4f} vs {ref['l_tr1']} (d={d_tr:.2e})  "
              f"=> {'OK' if anchor_ok else 'DRIFT -> MODEL MISREAD'}")
        assert anchor_ok, f"anchor drift vs committed 1068 at N={N}"

        del ctx, HT, F
        rows[N] = r
        print(f"SUMMARY|N{N}T{T:g}|S{S}|k={K:g}"
              f"|l_hs_sq={r['l_hs_sq']:.4f}|l_tr1={r['l_tr1']:.4f}"
              f"|ck_hs_sq={r['ck_hs_sq']:.4f}|kc_hs_sq={r['kc_hs_sq']:.4f}"
              f"|ck_tr1={r['ck_tr1']:.4f}|kc_tr1={r['kc_tr1']:.4f}"
              f"|ks_unw={r['ks_unw']:.4f}")

    # ---- decision table: per-octave values + 8x-window slope for each quantity --------
    Ns = sorted(rows)
    print("\n=== PROBE-P2 DECISION TABLE (S={2,3,5}, k=1; O(1) => |slope| < "
          f"{O1_SLOPE}) ===")
    header = "quantity                |" + "".join(f"N{N:<6}" for N in Ns) + " slope8x"
    print(header)
    print("-" * len(header))
    verdicts = {}
    for key, label in [("l_hs_sq", "||L||_F^2 (anchor)"), ("l_tr1", "||L||_nuc witness"),
                       ("ck_hs_sq", "C o K_S HS^2 (named)"), ("kc_hs_sq", "K_S o C HS^2 (named)"),
                       ("ck_tr1", "C o K_S nuclear"), ("kc_tr1", "K_S o C nuclear"),
                       ("ks_unw", "||K_S||_F^2 (control)")]:
        vals = [rows[N][key] for N in Ns]
        sl = slope(vals[0], vals[-1])
        verdicts[key] = sl
        line = f"{label:<23}|" + "".join(f"{v:9.4f}" for v in vals) + f"  {sl:+.3f}"
        print(line)

    # ---- dt-invariance pair (fixed window, k=1): quantities track WINDOW not grid ------
    dtinv = json.loads(os.environ.get("DTINV_GRIDS_1090", "[[4097,20.0],[8193,40.0]]"))
    if len(dtinv) >= 2:
        print("\n--- dt-invariance (fixed window, k=1, S={2,3,5}) ---")
        acc = {k: [] for k in ("l_hs_sq", "l_tr1", "ck_hs_sq", "kc_hs_sq")}
        for (N, T) in dtinv:
            t, _dt, xi, _ = m.p.grids(N, T)
            c_amp = np.exp(-0.25 * (K * xi) ** 2)
            F = m.p.dft_matrix(xi, t, N)
            E_diag = (t >= 0.0).astype(float)
            HT = m.p.build_HT(m.p.transport_phase(xi, S), F, N)
            ctx = m.build_context(F, HT, E_diag, N, f"S={S}")
            r = measure_p2(F, ctx, c_amp)
            for k in acc:
                acc[k].append(r[k])
            del ctx, HT, F
        parts = "  ".join(
            f"{k}: {acc[k][0]:.4f} vs {acc[k][1]:.4f} "
            f"(rel {abs(acc[k][0] - acc[k][1]) / max(abs(acc[k][0]), 1e-300):.2e})"
            for k in acc)
        print(f"SUMMARY|dtinv|S{S}|{parts}")

    # ---- the verdict (machine-readable; human reads the log, AGENTS 7a) ---------------
    o1 = abs(verdicts["l_tr1"]) < O1_SLOPE                 # nuclear witness O(1)?
    terms_nuclear_flat = (abs(verdicts["ck_tr1"]) < O1_SLOPE and
                          abs(verdicts["kc_tr1"]) < O1_SLOPE)
    print("\n=== VERDICT ===")
    if not o1:
        print(f"Q2-PARTIAL/MISREAD: nuclear witness slope {verdicts['l_tr1']:+.3f} (not O(1)); "
              f"escalate with numbers.")
    elif terms_nuclear_flat:
        print("Q2-OPTIMAL-TERMS: L nuclear O(1) AND both named terms are NUCLEAR O(1) "
              f"(ck_tr1 slope {verdicts['ck_tr1']:+.3f}, kc_tr1 {verdicts['kc_tr1']:+.3f}); "
              "Lean brick may use PER-TERM pairData + isTraceClassAlong_add.")
    else:
        print(f"Q2-OPTIMAL-COMBINED: L nuclear O(1) (witness slope {verdicts['l_tr1']:+.3f}) but named "
              f"terms are NOT individually nuclear-O(1) (ck_tr1 {verdicts['ck_tr1']:+.3f}, kc_tr1 "
              f"{verdicts['kc_tr1']:+.3f}; control ks_unw {verdicts['ks_unw']:+.3f}); cancellation is the "
              "mechanism -> Lean legs come from the COMBINED divided-difference object (the classical "
              "commutator-smoothing argument), not per-term.")

    print("\n=== done: grep 'SUMMARY|' and 'VERDICT' in this log for the decision ===")


if __name__ == "__main__":
    run()
