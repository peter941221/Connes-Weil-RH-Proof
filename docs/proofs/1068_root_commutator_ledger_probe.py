# 1068 - four-branch ledger + root-commutator probe (the D-weighted re-route's
# unmeasured bone), in the 1067 rig.
#
# Measures, per (grid, family, weight k), the two contracts the 1067 ROUTE B
# re-route consumes (design record 1068 s0-s2):
#   P := C† K_S C   (right sandwich, positive)   -> S1' = HS of F_K C
#   L := [C, K_S]   (root commutator, signed)    -> S2 supply via HS legs
#   S := C† L                                      -> S2 proper
#   T := D K_S = P + S                            -> the capstone predicate
# with D_k = F* diag(exp(-(k xi)^2 / 2)) F, C_k = F* diag(exp(-(k xi)^2 / 4)) F
# (1063b convention; k = 0 gives C = I and reproduces 1067 as the anchor).
#
# Identities reproduced (Lean-proven, design record s2):
#   ID-1 T = P + S;  ID-2 L + (outer + second + refl - prol) = 0;
#   ID-3 ||F_K C||_F^2 = Tr(P);  ID-4 k=0 anchor vs committed 1067 table;
#   ID-5 absdiag <= trace norm in every measured case (SVD cross-check).
#
# Deterministic. Memory-lean (aggressive del): ~6 dense N^2 context matrices
# plus <= 6 per-weight temporaries (~13 GB peak at N=8193) plus SVD workspace.
# Run (WSL, ONE command, log on the Linux side):
#   MSYS_NO_PATHCONV=1 wsl.exe --cd /home/peter/rh /home/peter/.local/bin/uv run \
#     --with numpy --with scipy --with mpmath python -u \
#     docs/proofs/1068_root_commutator_ledger_probe.py > /home/peter/1068_full.log
# Env: GRIDS_1068 SLIST_1068 WEIGHTS_1068 DTINV_GRIDS_1068 SVD_K3_NMAX OUTDIR

import importlib.util
import json
import os

import numpy as np

_HERE = os.path.dirname(os.path.abspath(__file__))
_spec = importlib.util.spec_from_file_location(
    "p1067", os.environ.get("P1067", os.path.join(_HERE, "1067_fk_hs_direct_trace_probe.py")))
assert _spec is not None and _spec.loader is not None, "1067 rig file not found"
p = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(p)

# Committed 1067 s5.1 table: Tr(K_S)_model, for the k=0 anchor gate (5e-3).
COMMITTED_1067 = {
    ("src", 1025): 6.1786, ("src", 2049): 6.4329, ("src", 4097): 7.1208, ("src", 8193): 6.4740,
    ("2", 1025): 9.0332, ("2", 2049): 11.1247, ("2", 4097): 12.7980, ("2", 8193): 13.3688,
    ("2,3", 1025): 13.7400, ("2,3", 2049): 16.3261, ("2,3", 4097): 19.1989, ("2,3", 8193): 22.8190,
    ("2,3,5", 1025): 16.1996, ("2,3,5", 2049): 20.1700, ("2,3,5", 4097): 26.8715,
    ("2,3,5", 8193): 34.2696,
}

SVD_K3_NMAX = 2049      # k=3 SVDs only up to this N (budget knob)


def frob(A):
    return float(np.vdot(A, A).real)


def rel(a, b):
    return abs(a - b) / max(1.0, abs(a), abs(b))


def absdiag_xi(F, T):
    # diag(F T F*)_k = <row_k(F T), row_k(F)>: one matmul + one einsum.
    FT = F @ T
    d = np.abs(np.einsum("kj,kj->k", FT, F.conj()))
    del FT
    return float(np.sum(d))


def trace_norm(A):
    return float(np.sum(np.linalg.svd(A, compute_uv=False)))


def build_context(F, HT, E_diag, N, name):
    """Build Q_S, R_S (meet), K_S, FK once per (grid, family) - the 1067 rig."""
    ED = np.diag(E_diag)
    Q_S = HT @ ED @ HT
    qid = float(np.linalg.norm(Q_S @ Q_S - Q_S, ord=2))
    qsad = float(np.linalg.norm(Q_S - Q_S.conj().T, ord=2))
    assert qid < 4e-8 and qsad < 4e-8, f"Q_S gate failed for {name}: {qid:.2e} {qsad:.2e}"

    Uidx = np.nonzero(E_diag)[0]
    B = p.hermitian_part(Q_S[np.ix_(Uidx, Uidx)])
    lam, vecs = np.linalg.eigh(B)
    assert float(lam[0]) > -1e-6, f"positivity gate (B) failed for {name}"
    d = int(np.sum(lam > 1.0 - 1e-9))
    W_full = np.zeros((N, max(d, 1)), dtype=complex)
    if d:
        W_full[Uidx, :] = vecs[:, -d:]
    R_S = W_full @ W_full.conj().T
    del W_full, vecs, B, lam

    M = ED @ Q_S @ ED
    K_S = M - R_S
    del M
    FK = Q_S @ (ED - R_S)
    QEd = Q_S @ ED
    return dict(ED=ED, Q_S=Q_S, R_S=R_S, K_S=K_S, FK=FK, QEd=QEd, d=d,
                fk_unw=frob(FK))


def measure_k(F, ctx, N, k, c_amp, w_amp, fam_key):
    """One (family, k) measurement on a built context. Returns scalar dict."""
    ED, Q_S, R_S, K_S = ctx["ED"], ctx["Q_S"], ctx["R_S"], ctx["K_S"]
    out = dict(d=ctx["d"], fk_unw=ctx["fk_unw"])

    if k == 0.0:
        # C = I: L = 0, S = 0, P = T = K_S (positive): trace norm = absdiag.
        s_ad_t = 0.0
        t_ad_t = float(np.sum(np.abs(np.diagonal(K_S))))
        t_ad_x = absdiag_xi(F, K_S)
        t_tr1 = t_ad_t
        out.update(p_hs_sq=ctx["fk_unw"], p_trace=t_ad_t, l_hs_sq=0.0, s_hs_sq=0.0,
                   l_tr1=float("nan"), s_tr1=float("nan"), t_tr1=t_tr1,
                   s_ad_t=s_ad_t, s_ad_x=0.0, t_ad_t=t_ad_t, t_ad_x=t_ad_x,
                   t_trace_re=t_ad_t, t_trace_im=0.0, ratio_s=float("nan"),
                   ratio_t=float("nan"), res_id1=0.0, res_ledger=0.0, res_id3=0.0,
                   br_out=0.0, br_sec=0.0, br_refl=0.0, br_prol=0.0)
        ck = COMMITTED_1067.get(fam_key)
        if ck is not None:
            assert abs(t_ad_t - ck) < 5e-3, \
                f"k=0 anchor mismatch vs 1067 at {fam_key}: {t_ad_t:.4f} vs {ck}"
        return out

    # ---- convolution root and detector (Hermitian positive contractions) ----
    assert float(w_amp.max()) <= 1 + 1e-15 and float(w_amp.min()) >= 0.0
    assert float(c_amp.max()) <= 1 + 1e-15 and float(c_amp.min()) >= 0.0
    c = F.conj().T @ (c_amp[:, None] * F)
    Dd = F.conj().T @ (w_amp[:, None] * F)

    # ---- four-branch ledger pieces (ID-2), each Frobenius'd then dropped ----
    Ec = ED @ c
    Ec = Ec - c @ ED                                     # [E, C]
    QC = Q_S @ c
    CQ = c @ Q_S
    b_sec = ED @ ((QC - CQ) @ ED)                        # E [Q, C] E
    del QC, CQ
    b_out = ED @ (Q_S @ Ec)                              # E Q [E, C]
    b_refl = Ec @ ctx["QEd"]                             # [E, C] Q E
    br_out = frob(b_out)
    br_sec = frob(b_sec)
    br_refl = frob(b_refl)
    b_prol = R_S @ c - c @ R_S                           # [R, C]
    br_prol = frob(b_prol)
    ledger = (b_out + b_sec + b_refl) - b_prol
    del b_out, b_sec, b_refl, b_prol, Ec

    CK = c @ K_S
    KC = K_S @ c
    P_mat = c @ KC
    L = CK - KC                                          # [C, K_S]
    del CK, KC

    res2 = float(np.linalg.norm(L + ledger)) / max(1.0, float(np.linalg.norm(L)))
    assert res2 < 1e-10, f"ID-2 ledger identity residual {res2:.2e}"
    del ledger

    p_hs = frob(ctx["FK"] @ c)                           # ||F_K C||_F^2
    S_op = c @ L                                         # C† [C, K_S]  (C† = C)
    del c
    l_hs = frob(L)
    s_hs = frob(S_op)

    T = Dd @ K_S
    del Dd
    p_trace = float(np.trace(P_mat).real)
    res3 = rel(p_hs, p_trace)
    assert res3 < 1e-10, f"ID-3 sandwich HS/trace residual {res3:.2e}"
    res1 = float(np.linalg.norm(T - (P_mat + S_op))) / max(1.0, float(np.linalg.norm(T)))
    assert res1 < 1e-10, f"ID-1 active-order residual {res1:.2e}"
    del P_mat

    t_tr = complex(np.trace(T))
    t_ad_t = float(np.sum(np.abs(np.diagonal(T))))
    t_ad_x = absdiag_xi(F, T)

    t_tr1 = trace_norm(T)
    l_tr1 = trace_norm(L)
    s_tr1 = trace_norm(S_op)
    s_ad_t = float(np.sum(np.abs(np.diagonal(S_op))))
    s_ad_x = absdiag_xi(F, S_op)
    # ID-5: the named-basis-agnostic absolute bound
    assert s_ad_t <= s_tr1 * (1 + 1e-8) + 1e-8, "ID-5 absdiag>tr1 (S, t-basis)"
    assert s_ad_x <= s_tr1 * (1 + 1e-8) + 1e-8, "ID-5 absdiag>tr1 (S, xi-basis)"
    assert t_ad_t <= t_tr1 * (1 + 1e-8) + 1e-8, "ID-5 absdiag>tr1 (T, t-basis)"
    assert t_ad_x <= t_tr1 * (1 + 1e-8) + 1e-8, "ID-5 absdiag>tr1 (T, xi-basis)"
    del L, S_op, T

    out.update(p_hs_sq=p_hs, p_trace=p_trace, l_hs_sq=l_hs, s_hs_sq=s_hs,
               l_tr1=l_tr1, s_tr1=s_tr1, t_tr1=t_tr1,
               s_ad_t=s_ad_t, s_ad_x=s_ad_x, t_ad_t=t_ad_t, t_ad_x=t_ad_x,
               t_trace_re=t_tr.real, t_trace_im=t_tr.imag,
               ratio_s=s_ad_t / max(t_tr1, 1e-300), ratio_t=t_ad_t / max(t_tr1, 1e-300),
               res_id1=res1, res_ledger=res2, res_id3=res3,
               br_out=br_out, br_sec=br_sec, br_refl=br_refl, br_prol=br_prol)
    return out


def run():
    global SVD_K3_NMAX
    SVD_K3_NMAX = int(os.environ.get("SVD_K3_NMAX", "2049"))
    print("=== 1068 four-branch ledger + root-commutator probe (1067 rig) ===")
    p.spotcheck_phase()
    outdir = os.environ.get("OUTDIR", "/tmp")

    grid_list = json.loads(os.environ.get(
        "GRIDS_1068", "[[1025,20.0],[2049,20.0],[4097,20.0],[8193,20.0]]"))
    slists_raw = os.environ.get("SLIST_1068")
    if slists_raw:
        slists = []
        for part in slists_raw.split(";"):
            nums = part.strip().strip("[]")
            slists.append([int(x) for x in nums.split(",") if x.strip()] if nums else [])
    else:
        slists = [[], [2], [2, 3], [2, 3, 5]]
    weights = json.loads(os.environ.get("WEIGHTS_1068", "[0.0, 1.0, 3.0]"))

    src_p = []                       # (k=1.0, src p_hs_sq) flatness track
    for (N, T) in grid_list:
        t, dt, xi, _dxi = p.grids(N, T)
        F = p.dft_matrix(xi, t, N)
        E_diag = (t >= 0.0).astype(float)
        print(f"\n--- grid N={N} T={T:g} (dt={dt:.5f}, xi_max={abs(xi).max():.1f}) ---")
        for S in slists:
            phase = p.transport_phase(xi, S)
            name = "S=" + (",".join(str(x) for x in S) if S else "src")
            fam_key = (",".join(str(x) for x in S) if S else "src", N)
            gsym = float(np.max(np.abs(phase[::-1] - phase.conj())))
            assert gsym < 1e-10, "transported phase loses reflection symmetry"
            HT = p.build_HT(phase, F, N)
            if not S:
                g1 = float(np.linalg.norm(HT @ HT - np.eye(N), ord=2))
                g2 = float(np.linalg.norm(HT - HT.conj().T, ord=2))
                assert g1 < 1e-8 and g2 < 1e-8, "HT not a self-adjoint involution"
                print(f"[gate HT^2=I] {g1:.2e}   [gate HT=HT*] {g2:.2e}   "
                      f"[gate m-sym] {gsym:.2e}")
            else:
                print(f"[gate m-sym {name}] {gsym:.2e}")

            ctx = build_context(F, HT, E_diag, N, name)
            print(f"[meet ladder] d={ctx['d']}   [FK unw fp-unweighted] "
                  f"{ctx['fk_unw']:.4f}")
            amps = {}
            for k in weights:
                amps[k] = (None, None) if k == 0.0 else (
                    np.exp(-0.25 * (k * xi) ** 2), np.exp(-0.5 * (k * xi) ** 2))

            for k in weights:
                r = measure_k(F, ctx, N, k, amps[k][0], amps[k][1], fam_key)
                if k == 1.0 and not S:
                    src_p.append(r["p_hs_sq"])
                np.savez(
                    f"{outdir}/1068_case_N{N}_T{T:g}_"
                    f"{name.strip('S=').replace(',', '_') or 'src'}_k{k:g}.npz",
                    **{kk: vv for kk, vv in r.items()})
                print(
                    f"SUMMARY|N{N}T{T:g}|{name}|k={k:g}|d={r['d']}"
                    f"|p_hs_sq={r['p_hs_sq']:.4f}|p_trace={r['p_trace']:.4f}"
                    f"|l_hs_sq={r['l_hs_sq']:.4f}|s_hs_sq={r['s_hs_sq']:.4f}"
                    f"|l_tr1={r['l_tr1']:.4f}|s_tr1={r['s_tr1']:.4f}|t_tr1={r['t_tr1']:.4f}"
                    f"|s_ad_t={r['s_ad_t']:.4f}|s_ad_x={r['s_ad_x']:.4f}"
                    f"|t_ad_t={r['t_ad_t']:.4f}|t_ad_x={r['t_ad_x']:.4f}"
                    f"|t_tr_re={r['t_trace_re']:.4f}|t_tr_im={r['t_trace_im']:.4f}"
                    f"|br_out={r['br_out']:.3e}|br_sec={r['br_sec']:.3e}"
                    f"|br_refl={r['br_refl']:.3e}|br_prol={r['br_prol']:.3e}"
                    f"|res1={r['res_id1']:.1e}|res2={r['res_ledger']:.1e}"
                    f"|res3={r['res_id3']:.1e}"
                    f"|ratio_s={r['ratio_s']:.3f}|ratio_t={r['ratio_t']:.3f}")
            del ctx, HT
        del F

    if src_p:
        flat = max(src_p) / max(min(src_p), 1e-300)
        print(f"\n[gate src anchor flat k=1] p_hs_sq src octave ratio = "
              f"{flat:.3f} (gate <= 1.5)")
        assert flat <= 1.5, "SOURCE ANCHOR GROWS at k=1 -> model misread, trust nothing"

    # ---- dt-invariance pair (fixed window, k=1.0) ---------------------------
    dtinv = json.loads(os.environ.get("DTINV_GRIDS_1068", "[[4097,20.0],[8193,40.0]]"))
    if len(dtinv) >= 2:
        print("\n--- dt-invariance (fixed window, k=1.0) ---")
        for S in slists:
            name = "S=" + (",".join(str(x) for x in S) if S else "src")
            acc = {kk: [] for kk in ("p_hs_sq", "l_hs_sq", "s_tr1", "t_tr1")}
            for (N, T) in dtinv:
                t, _dt, xi, _ = p.grids(N, T)
                F = p.dft_matrix(xi, t, N)
                E_diag = (t >= 0.0).astype(float)
                HT = p.build_HT(p.transport_phase(xi, S), F, N)
                ctx = build_context(F, HT, E_diag, N, name)
                r = measure_k(F, ctx, N, 1.0,
                              np.exp(-0.25 * xi ** 2), np.exp(-0.5 * xi ** 2),
                              (",".join(str(x) for x in S) if S else "src", N))
                for kk in acc:
                    acc[kk].append(r[kk])
                del ctx, HT, F
            parts = "  ".join(
                f"{kk}: {acc[kk][0]:.4f} vs {acc[kk][1]:.4f} "
                f"(rel {abs(acc[kk][0] - acc[kk][1]) / max(abs(acc[kk][0]), 1e-300):.2e})"
                for kk in acc)
            print(f"SUMMARY|dtinv|{name}|{parts}")

    print("\n=== done: grep 'SUMMARY|' in this log for the decision table ===")


if __name__ == "__main__":
    run()
