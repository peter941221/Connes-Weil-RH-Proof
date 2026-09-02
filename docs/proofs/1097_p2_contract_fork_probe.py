# 1097 - P2 CONTRACT FORK probe: is A-in-HS schedulable, and what replaces it?
#
# Design record: docs/proofs/1097_p2_contract_fork_preregistration.md (committed
# BEFORE this run).  Reuses the committed 1068 module (and its 1067 rig) so every
# anchor gate runs byte-identical to records 1067/1068/1090.
#
# H1 observable  tr_ks = trace(K_S).real          (raw trace, the 1096 primitive;
#                                   = the 1067 "Tr M - d" path up to 2.6e-11)
# H2 observables p_hs = trace(C^dag K_S C).real   (= ||A C||_HS^2, law-16 (a))
#                l_tr1 = ||[C,K_S]||_nuclear       (law-16 (b) witness; SVD only
#                                                  at N <= 8193, pre-registered)
# controls       ks_frob2 = ||K_S||_F^2 = Tr(K_S^2);  src-family trace (anchor).
#
# Deep octave: (16385, T=20) reaches xi_max = 204.8; the dt-invariance pair
# (8193, T=10) vs (16385, T=20) shares dt AND xi_max (law 15/17 discipline).
# At 16385 the LEAN builder applies the four pre-registered deviations of the
# design record (broadcast E, Frobenius gates, no SVD rows, identity gates).
# The lean builder itself is anchored at (8193, T=20) against COMMITTED_1067.
#
# Deterministic; accept on the flushed log, not exit codes (AGENTS 7a).
#
# Run (WSL, log on the Linux side):
#   uv run --with numpy --with scipy \
#     python -u docs/proofs/1097_p2_contract_fork_probe.py > /tmp/1097_fork.log

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


# Committed 1068 module: byte-identical rig; exposes m.p (the 1067 rig),
# build_context, frob, trace_norm, COMMITTED_1067, and its own `p`.
m = _load("p1068", os.path.join(_HERE, "1068_root_commutator_ledger_probe.py"))

# Committed record-1068 s5.1 table for {2,3,5}, k=1 (hard anchor gate, 2e-3).
COMMITTED_1068 = {
    1025: dict(l_hs_sq=0.2086, l_tr1=1.3462),
    2049: dict(l_hs_sq=0.1855, l_tr1=1.3145),
    4097: dict(l_hs_sq=0.1739, l_tr1=1.2910),
    8193: dict(l_hs_sq=0.1688, l_tr1=1.2850),
}

# Committed 1068 s5.1 p_hs_sq endpoints for {2,3,5}, k=1 (hard gate, 2e-3).
COMMITTED_PHS_ENDPOINTS = {1025: 3.5661, 8193: 3.5356}

ANCHOR_TOL = 2e-3      # 1068-table / p_hs endpoints
TRACE_TOL = 5e-3       # 1067-table trace anchors (the 1067 k=0 gate tolerance)
REL_TOL_DT = 2e-3      # G-dt: deep dt-invariance pair
REL_TOL_SRC = 5e-2     # G-src: source-family flatness at the new octave
O1_SLOPE = 0.15        # the 1068/1090 O(1) slope threshold over a sweep
K = 1.0                # primary Gaussian weight (as 1068/1090)


def slope(first, last, factor):
    if first <= 0 or last <= 0:
        return float("nan")
    return math.log(last / first) / math.log(factor)


def rel(a, b):
    return abs(a - b) / max(abs(a), abs(b), 1e-300)


def measure(F, ctx, c_amp):
    """Anchors + H1 + H2 observables on a built context (committed rig)."""
    K_S = ctx["K_S"]
    tr_ks = float(np.trace(K_S).real)
    ks_frob2 = m.frob(K_S)
    c = F.conj().T @ (c_amp[:, None] * F)
    CK = c @ K_S
    KC = K_S @ c
    L = CK - KC
    T1 = K_S @ c
    p_hs = float(np.einsum("ki,ki->", c.conj(), T1).real)
    del T1
    out = dict(
        tr_ks=tr_ks,
        ks_frob2=ks_frob2,
        p_hs=p_hs,
        l_hs_sq=m.frob(L),
        l_tr1=m.trace_norm(L),
        ck_hs_sq=m.frob(CK),
        kc_hs_sq=m.frob(KC),
    )
    del c, CK, KC, L
    return out


def build_lean_context(F, phase, t, S):
    """Memory-lean deep-window builder (pre-registered deviations).

    Same algebra as the committed 1068 build_context: Q_S = HT ED HT with
    HT = F^* M_phase Flip F, e = (t >= 0), M = ED Q_S ED, K_S = M - R_S, with
    R_S the meet projection from the Hermitian U-block spectrum.  Deviations:
    broadcast E instead of dense ED; Frobenius gates; direct identity gates.
    """
    N = F.shape[0]
    gsym = float(np.max(np.abs(phase[::-1] - phase.conj())))
    assert gsym < 1e-10, f"transported phase loses m-symmetry: {gsym:.2e}"
    print(f"[gate m-sym S={S}] {gsym:.2e}")

    tmp = phase[:, None] * F[::-1, :]
    HT = F.conj().T @ tmp
    del tmp
    e = (t >= 0.0).astype(float)

    Q_S = HT @ (e[:, None] * HT)
    del HT
    qsad = float(np.sqrt(m.frob(Q_S - Q_S.conj().T)))
    qid = float(np.sqrt(m.frob(Q_S @ Q_S - Q_S)))
    print(f"[gate Q_S self-adjoint (F)] {qsad:.2e}   [gate Q_S idempotent (F)] "
          f"{qid:.2e}")
    assert qsad < 1e-5 and qid < 1e-5, "Q_S Frobenius gates failed (lean path)"

    Uidx = np.nonzero(e)[0]
    Bfull = Q_S[np.ix_(Uidx, Uidx)]
    B = 0.5 * (Bfull + Bfull.conj().T)
    lam, vecs = np.linalg.eigh(B)
    del Bfull, B
    assert float(lam[0]) > -1e-6, "positivity gate (B) failed (lean path)"
    d = int(np.sum(lam > 1.0 - 1e-9))
    print(f"[meet count d] {d}")
    W = np.zeros((N, max(d, 1)), dtype=complex)
    if d:
        W[Uidx, :] = vecs[:, -d:]
    del vecs, lam
    R_S = W @ W.conj().T
    del W
    rsad = float(np.sqrt(m.frob(R_S - R_S.conj().T)))
    rid = float(np.sqrt(m.frob(R_S @ R_S - R_S)))
    rtr = float(np.trace(R_S).real)
    print(f"[gate R_S self-adjoint (F)] {rsad:.2e}   [gate R_S idempotent (F)] "
          f"{rid:.2e}   [trace R_S = d] {rtr:.6f} vs {d}")
    assert rsad < 1e-5 and rid < 1e-5 and abs(rtr - d) <= max(1e-6, 1e-9 * d)

    M = e[:, None] * (Q_S * e[None, :])
    tr_M = float(np.sum(e * np.real(np.diagonal(Q_S))))
    del Q_S
    K_S = M - R_S
    del M, R_S
    ksad = float(np.sqrt(m.frob(K_S - K_S.conj().T)))
    tr_ks = float(np.trace(K_S).real)
    print(f"[gate K_S self-adjoint (F)] {ksad:.2e}")
    assert ksad < 1e-5
    ident = abs(tr_ks - (tr_M - d))
    print(f"[identity trace K_S = Tr M - d] {tr_ks:.6f} vs {tr_M - d:.6f} "
          f"(abs {ident:.2e})")
    assert ident <= 1e-6 * max(1.0, abs(tr_ks)), "identity gate failed (lean)"
    return K_S


def lean_observables(K_S, F, c_amp):
    tr_ks = float(np.trace(K_S).real)
    ks_frob2 = m.frob(K_S)
    c = F.conj().T @ (c_amp[:, None] * F)
    T1 = K_S @ c
    p_hs = float(np.einsum("ki,ki->", c.conj(), T1).real)
    del T1, c
    return dict(tr_ks=tr_ks, ks_frob2=ks_frob2, p_hs=p_hs)


def run():
    S = [2, 3, 5]
    SRC = []
    anchor_grids = json.loads(os.environ.get(
        "ANCHOR_GRIDS_1097",
        "[[1025,20.0],[2049,20.0],[4097,20.0],[8193,20.0]]"))
    cross_grids = json.loads(os.environ.get("CROSS_GRIDS_1097", "[[8193,20.0]]"))
    deep_grids = json.loads(os.environ.get("DEEP_GRIDS_1097",
                                           "[[8193,10.0],[16385,20.0]]"))

    print("=== 1097 P2 CONTRACT FORK probe ({2,3,5} deciding, k=1) ===")
    m.p.spotcheck_phase()

    # ---- stage 1: committed-rig anchors (hard gates) -------------------------
    rows = {}
    for (N, T) in anchor_grids:
        t, dt, xi, _dxi = m.p.grids(N, T)
        c_amp = np.exp(-0.25 * (K * xi) ** 2)
        F = m.p.dft_matrix(xi, t, N)
        E_diag = (t >= 0.0).astype(float)
        print(f"\n--- anchor grid N={N} T={T:g} (dt={dt:.5f}, "
              f"xi_max={abs(xi).max():.1f}) ---")
        HT = m.p.build_HT(m.p.transport_phase(xi, S), F, N)
        ctx = m.build_context(F, HT, E_diag, N, f"S={S}")
        del HT
        r = measure(F, ctx, c_amp)
        del ctx, F
        ref_trace = m.COMMITTED_1067[("2,3,5", N)]
        d_tr = abs(r["tr_ks"] - ref_trace) / max(abs(ref_trace), 1e-300)
        ref = COMMITTED_1068[N]
        d_hs = abs(r["l_hs_sq"] - ref["l_hs_sq"])
        d_ltr = abs(r["l_tr1"] - ref["l_tr1"])
        phs_ref = COMMITTED_PHS_ENDPOINTS.get(N)
        d_phs = abs(r["p_hs"] - phs_ref) if phs_ref is not None else None
        ok = d_tr < TRACE_TOL and d_hs < ANCHOR_TOL and d_ltr < ANCHOR_TOL and (
            d_phs is None or d_phs < ANCHOR_TOL)
        print(f"[anchor 1067 trace] {r['tr_ks']:.4f} vs {ref_trace} "
              f"(rel {d_tr:.2e})")
        print(f"[anchor 1068] l_hs_sq {r['l_hs_sq']:.4f} vs {ref['l_hs_sq']} "
              f"(d={d_hs:.2e}); l_tr1 {r['l_tr1']:.4f} vs {ref['l_tr1']} "
              f"(d={d_ltr:.2e})")
        if d_phs is not None:
            print(f"[anchor 1068 p_hs] {r['p_hs']:.4f} vs {phs_ref} "
                  f"(d={d_phs:.2e})")
        assert ok, f"anchor gate failed at N={N}"
        rows[(N, T)] = r
        print(f"SUMMARY|anchor|S{S}|N{N}T{T:g}|tr_ks={r['tr_ks']:.4f}"
              f"|p_hs={r['p_hs']:.4f}|l_hs_sq={r['l_hs_sq']:.4f}"
              f"|l_tr1={r['l_tr1']:.4f}|ks_frob2={r['ks_frob2']:.4f}")

    # ---- stage 2: lean-builder cross-rig anchor at (8193, 20) ----------------
    for (N, T) in cross_grids:
        for (fam, key) in ((S, "2,3,5"), (SRC, "src")):
            t, dt, xi, _dxi = m.p.grids(N, T)
            c_amp = np.exp(-0.25 * (K * xi) ** 2)
            F = m.p.dft_matrix(xi, t, N)
            print(f"\n--- lean cross-anchor N={N} T={T:g} family {key} ---")
            KS = build_lean_context(F, m.p.transport_phase(xi, fam), t, fam)
            r = lean_observables(KS, F, c_amp)
            del KS, F
            ref_trace = m.COMMITTED_1067[(key, N)]
            d_tr = abs(r["tr_ks"] - ref_trace) / max(abs(ref_trace), 1e-300)
            print(f"[lean anchor 1067 trace] {r['tr_ks']:.4f} vs {ref_trace} "
                  f"(rel {d_tr:.2e})")
            assert d_tr < TRACE_TOL, f"lean cross-anchor failed at N={N} {key}"
            print(f"SUMMARY|lean_cross|{key}|N{N}T{T:g}|tr_ks={r['tr_ks']:.4f}"
                  f"|p_hs={r['p_hs']:.4f}|ks_frob2={r['ks_frob2']:.4f}")

    # ---- stage 3: deep octaves via the lean path (both families) -------------
    deep = {}
    for (N, T) in deep_grids:
        for (fam, key) in ((S, "2,3,5"), (SRC, "src")):
            t, dt, xi, _dxi = m.p.grids(N, T)
            c_amp = np.exp(-0.25 * (K * xi) ** 2)
            F = m.p.dft_matrix(xi, t, N)
            print(f"\n--- deep grid N={N} T={T:g} (dt={dt:.5f}, "
                  f"xi_max={abs(xi).max():.1f}) family {key} ---")
            KS = build_lean_context(F, m.p.transport_phase(xi, fam), t, fam)
            r = lean_observables(KS, F, c_amp)
            del KS, F
            deep[(N, T, key)] = r
            print(f"SUMMARY|deep|{key}|N{N}T{T:g}|tr_ks={r['tr_ks']:.4f}"
                  f"|p_hs={r['p_hs']:.4f}|ks_frob2={r['ks_frob2']:.4f}")

    # ---- stage 4: gates and verdict ------------------------------------------
    print("\n=== DECISION TABLE ===")
    Ns = [g[0] for g in anchor_grids]
    tr_seq = [rows[(N, anchor_grids[i][1])]["tr_ks"] for i, N in enumerate(Ns)]
    phs_seq = [rows[(N, anchor_grids[i][1])]["p_hs"] for i, N in enumerate(Ns)]
    ltr_seq = [rows[(N, anchor_grids[i][1])]["l_tr1"] for i, N in enumerate(Ns)]
    tr_deep = deep[(16385, 20.0, "2,3,5")]["tr_ks"]
    tr16 = tr_seq + [tr_deep]
    span16 = slope(tr16[0], tr16[-1], 16.0)
    span8 = slope(tr16[0], tr16[-2], 8.0)
    inc_last = tr16[-1] - tr16[-2]
    inc_prev = tr16[-2] - tr16[-3]
    phs8 = slope(phs_seq[0], phs_seq[-1], 8.0)
    ltr8 = slope(ltr_seq[0], ltr_seq[-1], 8.0)
    print(f"tr_ks sequence (12.8..102.4 committed + 204.8): "
          f"{['%.4f' % v for v in tr16]}")
    print(f"H1 slope16x={span16:+.3f} (>= +{O1_SLOPE} fires) | "
          f"slope8x={span8:+.3f} | "
          f"inc_last/inc_prev={inc_last / inc_prev:.3f} (>= 0.5 fires)")
    print(f"H2 p_hs slope8x={phs8:+.3f} | l_tr1 slope8x={ltr8:+.3f} "
          f"(O(1) iff |slope| < {O1_SLOPE})")

    g_dt = {}
    for key in ("2,3,5", "src"):
        a = deep[(8193, 10.0, key)]
        b = deep[(16385, 20.0, key)]
        g_dt[key] = max(rel(a["tr_ks"], b["tr_ks"]),
                        rel(a["ks_frob2"], b["ks_frob2"]),
                        rel(a["p_hs"], b["p_hs"]))
        print(f"G-dt {key}: tr_ks {a['tr_ks']:.4f} vs {b['tr_ks']:.4f}; "
              f"ks_frob2 {a['ks_frob2']:.4f} vs {b['ks_frob2']:.4f}; "
              f"p_hs {a['p_hs']:.4f} vs {b['p_hs']:.4f} "
              f"=> max rel {g_dt[key]:.2e}")
    src_deep = deep[(16385, 20.0, "src")]["tr_ks"]
    src_ref = m.COMMITTED_1067[("src", 8193)]
    src_rel = abs(src_deep - src_ref) / abs(src_ref)
    print(f"G-src: src trace at 16385/20 {src_deep:.4f} vs committed "
          f"8193/20 {src_ref:.4f} (rel {src_rel:.2e}, gate {REL_TOL_SRC})")

    gates_ok = (g_dt["2,3,5"] <= REL_TOL_DT and g_dt["src"] <= REL_TOL_DT
                and src_rel <= REL_TOL_SRC)
    h1_fires = (span16 >= O1_SLOPE) or (inc_last >= 0.5 * inc_prev)
    h2_passes = abs(phs8) < O1_SLOPE and abs(ltr8) < O1_SLOPE

    print("\n=== VERDICT ===")
    if not gates_ok:
        print(f"ABORT: G-dt/G-src failed (dt max rel {g_dt}, src rel "
              f"{src_rel:.2e}) - grid artifact; no verdict (law 15).")
    elif h1_fires and h2_passes:
        print(f"H1-REJECTED / H2-CONFIRMED: raw trace keeps the power law "
              f"(slope16x {span16:+.3f}, inc ratio {inc_last / inc_prev:.3f}) "
              f"while law-16 (a)/(b) stay O(1) (p_hs {phs8:+.3f}, l_tr1 "
              f"{ltr8:+.3f}).  The record-1096 A-in-HS primitive is CLOSED for "
              f"continuum scheduling (numerical guard, 1063-standard); the "
              f"canonical S2 primitive set = (a) AC in HS + (b) commutator "
              f"trace legality.")
    elif not h1_fires:
        print(f"H1-OPEN: the raw trace BENDS at the new octave (slope16x "
              f"{span16:+.3f}, inc ratio {inc_last / inc_prev:.3f}); the 1096 "
              f"primitive stays canonical and its discharge is schedulable.")
    else:
        print(f"H2-REJECTED / escalation: raw trace fires but law-16 legs are "
              f"not O(1) (p_hs {phs8:+.3f}, l_tr1 {ltr8:+.3f}); no re-route "
              f"without a new pre-registration.")
    print("\n=== done: grep 'SUMMARY|' and 'VERDICT' in this log ===")


if __name__ == "__main__":
    run()
