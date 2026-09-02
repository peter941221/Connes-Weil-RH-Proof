# 1097b - deep-octave certification by BRACKET DIRECTION (re-run of the 1097
# pipeline with a replaced certification gate; H1/H2 criteria unchanged).
#
# Design record: docs/proofs/1097b_p2_deep_octave_bracket_preregistration.md
# (committed BEFORE this run).  Record 1097 fired its pre-registered ABORT
# because its dt-pair varies dxi (0.05 -> 0.0125) and t-extent (10 -> 20)
# jointly, and the next dxi refinement (32769, T=40) is out of memory budget
# (17.2 GiB per complex matrix).  The replacement certification is a signed
# direction test on the trace-class observables, stated before the run.
#
# Gates evaluated here:
#   G-anc   anchors + lean cross-anchor reproduce COMMITTED_1067/1068 (1097)
#   G-src   source trace at the FINE deep point vs committed, rel <= 5e-2
#   G-brkt  coarse member > fine member strictly on tr_ks and ks_frob2,
#           both families (p_hs EXCLUDED - its coarse/fine direction is not
#           signed; see prereg section 3)
#   G-conf  coarse source trace sits OUTSIDE the G-src band around committed
#   G-H1/G-H2  byte-identical to record 1097 section 3
#
# Run (WSL, log on the Linux side):
#   uv run --with numpy --with scipy --with mpmath \
#     python -u docs/proofs/1097b_p2_deep_octave_bracket_probe.py > /tmp/1097b.log

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

# Record-1097 run-log deep-grid values (soft cross-run reproducibility check;
# NOT a gate - threaded BLAS may differ at the 1e-12 level).
RUN_1097_DEEP = {
    ("2,3,5", "coarse"): dict(tr_ks=42.5025, p_hs=3.0641, ks_frob2=12.5637),
    ("2,3,5", "fine"): dict(tr_ks=41.0499, p_hs=3.5345, ks_frob2=11.2312),
    ("src", "coarse"): dict(tr_ks=7.6327, p_hs=2.3832, ks_frob2=6.9943),
    ("src", "fine"): dict(tr_ks=6.5620, p_hs=2.3835, ks_frob2=5.9933),
}

ANCHOR_TOL = 2e-3      # 1068-table / p_hs endpoints
TRACE_TOL = 5e-3       # 1067-table trace anchors (the 1067 k=0 gate tolerance)
REL_TOL_SRC = 5e-2     # G-src: source-family flatness at the fine deep point
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
    """Memory-lean deep-window builder (record-1097 deviations, unchanged).

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
    deep_coarse = json.loads(os.environ.get("DEEP_COARSE_1097", "[[8193,10.0]]"))
    deep_fine = json.loads(os.environ.get("DEEP_FINE_1097", "[[16385,20.0]]"))

    print("=== 1097b BRACKET-DIRECTION probe ({2,3,5} deciding, k=1) ===")
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

    # ---- stage 3: the bracket pair via the lean path (both families) ---------
    deep = {}
    for tag, grids in (("coarse", deep_coarse), ("fine", deep_fine)):
        for (N, T) in grids:
            for (fam, key) in ((S, "2,3,5"), (SRC, "src")):
                t, dt, xi, _dxi = m.p.grids(N, T)
                c_amp = np.exp(-0.25 * (K * xi) ** 2)
                F = m.p.dft_matrix(xi, t, N)
                print(f"\n--- deep {tag} grid N={N} T={T:g} (dt={dt:.5f}, "
                      f"xi_max={abs(xi).max():.1f}) family {key} ---")
                KS = build_lean_context(F, m.p.transport_phase(xi, fam), t, fam)
                r = lean_observables(KS, F, c_amp)
                del KS, F
                deep[(key, tag)] = r
                ref = RUN_1097_DEEP[(key, tag)]
                dd = max(rel(r["tr_ks"], ref["tr_ks"]),
                         rel(r["p_hs"], ref["p_hs"]),
                         rel(r["ks_frob2"], ref["ks_frob2"]))
                print(f"[soft vs run-1097 log] max rel {dd:.2e}")
                print(f"SUMMARY|deep_{tag}|{key}|N{N}T{T:g}"
                      f"|tr_ks={r['tr_ks']:.4f}|p_hs={r['p_hs']:.4f}"
                      f"|ks_frob2={r['ks_frob2']:.4f}")

    # ---- stage 4: bracket gates and verdict ----------------------------------
    print("\n=== DECISION TABLE ===")
    Ns = [g[0] for g in anchor_grids]
    tr_seq = [rows[(N, anchor_grids[i][1])]["tr_ks"] for i, N in enumerate(Ns)]
    phs_seq = [rows[(N, anchor_grids[i][1])]["p_hs"] for i, N in enumerate(Ns)]
    ltr_seq = [rows[(N, anchor_grids[i][1])]["l_tr1"] for i, N in enumerate(Ns)]
    tr_fine = deep[("2,3,5", "fine")]["tr_ks"]
    inc_last = tr_fine - tr_seq[-1]
    inc_prev = tr_seq[-1] - tr_seq[-2]
    span16 = slope(tr_seq[0], tr_fine, 16.0)
    phs8 = slope(phs_seq[0], phs_seq[-1], 8.0)
    ltr8 = slope(ltr_seq[0], ltr_seq[-1], 8.0)
    print(f"tr_ks sequence (12.8..102.4 committed + fine 204.8): "
          f"{['%.4f' % v for v in tr_seq + [tr_fine]]}")
    print(f"H1 slope16x={span16:+.3f} (>= +{O1_SLOPE} fires) | "
          f"inc_last={inc_last:.4f} inc_prev={inc_prev:.4f} "
          f"ratio={inc_last / inc_prev:.3f} (>= 0.5 fires)")
    print(f"H2 p_hs slope8x={phs8:+.3f} | l_tr1 slope8x={ltr8:+.3f} "
          f"(O(1) iff |slope| < {O1_SLOPE})")

    src_fine = deep[("src", "fine")]["tr_ks"]
    src_ref = m.COMMITTED_1067[("src", 8193)]
    src_rel = abs(src_fine - src_ref) / abs(src_ref)
    print(f"G-src: src trace at FINE (16385,20) {src_fine:.4f} vs committed "
          f"(8193,20) {src_ref:.4f} (rel {src_rel:.2e}, gate {REL_TOL_SRC})")

    g_brkt_ok = True
    for key in ("2,3,5", "src"):
        co, fi = deep[(key, "coarse")], deep[(key, "fine")]
        d_tr = co["tr_ks"] - fi["tr_ks"]
        d_fr = co["ks_frob2"] - fi["ks_frob2"]
        ok = d_tr > 0 and d_fr > 0
        g_brkt_ok = g_brkt_ok and ok
        print(f"G-brkt {key}: tr_ks {co['tr_ks']:.4f} vs {fi['tr_ks']:.4f} "
              f"(coarse-fine {d_tr:+.4f}); ks_frob2 {co['ks_frob2']:.4f} vs "
              f"{fi['ks_frob2']:.4f} ({d_fr:+.4f}) "
              f"=> {'PASS' if ok else 'FAIL'} (p_hs excluded: "
              f"{co['p_hs']:.4f} vs {fi['p_hs']:.4f})")
    src_coarse = deep[("src", "coarse")]["tr_ks"]
    outside = abs(src_coarse - src_ref) / abs(src_ref) > REL_TOL_SRC
    print(f"G-conf: src COARSE trace {src_coarse:.4f} vs committed "
          f"{src_ref:.4f} (rel {abs(src_coarse - src_ref) / abs(src_ref):.2e}) "
          f"=> {'PASS (outside band, coarse is the artifact)' if outside else 'FAIL'}")

    gates_ok = g_brkt_ok and outside and src_rel <= REL_TOL_SRC
    h1_fires = (span16 >= O1_SLOPE) or (inc_last >= 0.5 * inc_prev)
    h2_passes = abs(phs8) < O1_SLOPE and abs(ltr8) < O1_SLOPE

    print("\n=== VERDICT ===")
    if not gates_ok:
        print(f"ABORT: G-brkt/G-conf/G-src failed (brkt {g_brkt_ok}, conf "
              f"{outside}, src rel {src_rel:.2e}) - fine point not certified; "
              f"no verdict.")
    elif h1_fires and h2_passes:
        print(f"H1-REJECTED / H2-CONFIRMED: the raw trace keeps the power law "
              f"at the certified fine point (slope16x {span16:+.3f}, inc ratio "
              f"{inc_last / inc_prev:.3f}) while law-16 (a)/(b) stay O(1) "
              f"(p_hs {phs8:+.3f}, l_tr1 {ltr8:+.3f}).  The record-1096 "
              f"A-in-HS primitive is CLOSED for continuum scheduling "
              f"(numerical guard, 1063-standard); the canonical S2 primitive "
              f"set = (a) AC in HS + (b) commutator trace legality.")
    elif not h1_fires:
        print(f"H1-OPEN: the raw trace BENDS at the certified fine point "
              f"(slope16x {span16:+.3f}, inc ratio {inc_last / inc_prev:.3f}); "
              f"the 1096 primitive stays canonical and its discharge is "
              f"schedulable.")
    else:
        print(f"H2-REJECTED / escalation: raw trace fires but law-16 legs are "
              f"not O(1) (p_hs {phs8:+.3f}, l_tr1 {ltr8:+.3f}); no re-route "
              f"without a new pre-registration.")
    print("\n=== done: grep 'SUMMARY|' and 'VERDICT' in this log ===")


if __name__ == "__main__":
    run()
