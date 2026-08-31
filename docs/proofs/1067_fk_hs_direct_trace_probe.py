# 1067 - F1' direct trace probe: measure Tr(K_S)_model = Tr(M - R_S) directly.
#
# Same rig as record 1063 (every line pinned in docs/proofs/1067 s1):
#   E    = diag(t >= 0),  U = range(E)                       CCM24LogRadialSupport.lean:67-69
#   HT_S = F^* M_{m_S} Flip F, self-adjoint involution       CCM24HardyTitchmarsh.lean (1063 s1)
#   Q_S  = HT_S E HT_S, star projection; V = range(Q_S)      CCM24FiniteSProjectionTrace.lean:86-91
#   R_S  = P_W with W = U ∩ V                                CCM24SemilocalFourierSupport.lean:134-137
#            (star projection of the MEET logRadial ⊓ semilocalFourier)
#   K_S  = M - R_S_model, M := E Q_S E;  FK = Q_S (E - R_S), K_S = FK^* FK
#
# THE NUMBER (design record s2): Tr(K_S)_model = SUM_{theta>0} cos^2(theta)
# = Tr(M) - dim(U ∩ V), measured THREE independent ways and compared:
#   A spectrum : eigh of B := Hermitian U-block of Q_S; sum entries <= 1-tol, > floor
#   B trace    : Re Tr(M) - d ; eigvalsh(hermitian(M - R_S_model)) summed above floor
#   C direct   : ||FK||_F^2 with FK = Q_S (E - R_S_model), entry-level Frobenius sum
# Consistency flag = max pairwise relative deviation; BRIDGE 1 closes when < 1e-8.
#
# Gates (AGENTS 7c, 1063 style): positivity of the positive operator is a hard
# assert; source S={} is the ANCHOR - if it does not plateau, the model reading
# is wrong and NOTHING here is trusted. Deterministic.
#
# Run (WSL): OUTDIR=... GRIDS_1067='[[1025,20],...]' SLIST_1067='[];[2];...' \
#   uv run --with numpy --with scipy python docs/proofs/1067_fk_hs_direct_trace_probe.py

import json
import math
import os

import numpy as np
from scipy.special import loggamma

TOL_MEET = 1e-9      # eigenvalue threshold for the lambda ~= 1 ladder of B
FLOOR    = 1e-12     # numerical floor: below this an eigenvalue is zero


def grids(N, T):
    dt = 2.0 * T / N
    t = (np.arange(N) - N // 2) * dt
    dxi = 1.0 / (N * dt)
    xi = (np.arange(N) - N // 2) * dxi
    return t, dt, xi, dxi


def dft_matrix(xi, t, N):
    # unitary symmetric DFT: F[k,j] = exp(-2 pi i xi_k t_j)/sqrt(N)
    return np.exp(-2j * np.pi * np.outer(xi, t)) / math.sqrt(N)


def archimedean_phase(xi):
    # m = A/conj A = exp(2 i Im logA),  A = pi^{-z/2} Gamma(z/2),  z = 1/2-2 pi i xi
    z = 0.5 - 2j * np.pi * xi
    logA = -(z / 2.0) * math.log(math.pi) + loggamma(z / 2.0)
    return np.exp(2j * np.imag(logA))


def mu_transport(xi, S):
    mu = np.ones_like(xi, dtype=complex)
    for p in S:
        cp = p ** -0.5
        mu = mu * (1.0 - cp * np.exp(-2j * np.pi * xi * math.log(p)))
    return mu


def transport_phase(xi, S):
    m = archimedean_phase(xi)
    if not S:
        return m
    mu = mu_transport(xi, S)
    mu_neg = mu_transport(-xi, S)
    return m * (mu / mu_neg)


def build_HT(phase, F, N):
    # HT = F^* . M_phase . P_flip . F  (all unitary/permutation)
    flip = np.arange(N)[::-1]  # xi grid symmetric about 0: v(xi)->v(-xi)
    return F.conj().T @ (phase[:, None] * (np.eye(N)[flip] @ F))


def spotcheck_phase():
    import mpmath as mp
    mp.mp.dps = 50
    for x in (0.25, 1.0, 4.0):
        z = mp.mpc("0.5") - 2j * mp.pi * mp.mpf(x)
        logA = -(z / 2) * mp.log(mp.pi) + mp.log(mp.gamma(z / 2))
        mmp = mp.exp(2j * mp.im(logA))
        zn = 0.5 - 2j * np.pi * x
        logA_n = -(zn / 2) * math.log(math.pi) + complex(loggamma(zn / 2))
        mnp = np.exp(2j * np.imag(logA_n))
        d = abs(complex(mmp) - complex(mnp))
        print(f"[spot m({x})] |scipy-mpmath| = {d:.2e}")
        assert d < 1e-12, "phase evaluator disagrees with mpmath"


def hermitian_part(A):
    return 0.5 * (A + A.conj().T)


def gap_split_stats(vals_desc, g=0.02):
    # 1063-style diagnostic: first gap > g separates the lambda ~= 1 ladder;
    # report its size and the sum of the rest (the 1063 nonmeet-sum statistic).
    js = [j for j in range(len(vals_desc) - 1) if vals_desc[j] - vals_desc[j + 1] > g]
    jstar = js[0] + 1 if js else 0
    rest = vals_desc[jstar:]
    return jstar, float(np.sum(rest[rest > FLOOR]))


def fkhs_probe(HT, E_diag, N):
    """One (grid, S) case: build Q_S, R_S_model, measure Tr(K_S)_model 3 ways."""
    ED = np.diag(E_diag)
    Q_S = HT @ ED @ HT                       # star projection in the model
    qid = float(np.linalg.norm(Q_S @ Q_S - Q_S, ord=2))
    qsad = float(np.linalg.norm(Q_S - Q_S.conj().T, ord=2))
    print(f"[gate Q_S idempotent] {qid:.2e}   [gate Q_S self-adjoint] {qsad:.2e}")

    Uidx = np.nonzero(E_diag)[0]             # ON basis of U is the coordinate frame on t >= 0
    B = hermitian_part(Q_S[np.ix_(Uidx, Uidx)])     # A_U := P_U Q_S|_U (Hermitian on U)
    lam, vecs = np.linalg.eigh(B)             # ascending; last d entries near 1
    d = int(np.sum(lam > 1.0 - TOL_MEET))
    meet_lam_min = float(lam[-d]) if d else float("nan")

    W_full = np.zeros((N, max(d, 1)), dtype=complex)
    if d:                                     # eigenvectors live in U; zero-pad outside
        W_full[Uidx, :] = vecs[:, -d:]
    w_res = float(np.linalg.norm(Q_S @ W_full - W_full, ord=2))

    # ---- PATH A (spectrum of B): the direct number --------------------------
    fk_hs_sq = float(np.sum(lam[(lam <= 1.0 - TOL_MEET) & (lam > FLOOR)]))

    # ---- PATH B (trace identity + explicit M - R_S spectrum) -----------------
    M = ED @ Q_S @ ED                         # = E Q_S E, the 1063 matrix
    tr_M = float(np.real(np.trace(M)))
    R_S_model = W_full @ W_full.conj().T      # orthogonal projector onto U ∩ V (rank d)
    kv = np.linalg.eigvalsh(hermitian_part(M - R_S_model))
    khs_eigsum = float(np.sum(kv[kv > FLOOR]))
    tr_M_minus_d = tr_M - d
    mvals = np.sort(np.linalg.eigvalsh(hermitian_part(M)))[::-1]   # 1063-style diagnostics

    # ---- PATH C (Hilbert-Schmidt direct, no spectrum) ------------------------
    FK = Q_S @ (ED - R_S_model)               # Lean: K_S = FK^* FK (Dev C1Prolate:88-92)
    fk_hs_sq_direct = float(np.vdot(FK, FK).real)

    vals_desc = np.sort(lam)[::-1]
    meet_gap, nonmeet_1063style = gap_split_stats(vals_desc)

    three = [fk_hs_sq, tr_M_minus_d, khs_eigsum, fk_hs_sq_direct]
    scale = max(1.0, max(abs(x) for x in three))
    consistency = max(abs(a - b) for a in three for b in three) / scale

    return dict(lam=lam, mvals=mvals, d=d, meet_lam_min=meet_lam_min, w_res=w_res,
                qid=qid, qsad=qsad, fk_hs_sq=fk_hs_sq, tr_M_minus_d=tr_M_minus_d,
                khs_eigsum=khs_eigsum, fk_hs_sq_direct=fk_hs_sq_direct,
                consistency=consistency, meet_gap=meet_gap, nonmeet_1063style=nonmeet_1063style,
                lam_min_B=float(lam[0]))


def run():
    print("=== 1067 F1' direct trace probe (Tr(M - R_S) in the 1063 rig) ===")
    spotcheck_phase()
    outdir = os.environ.get("OUTDIR", "/tmp")

    # ODD N REQUIRED (1063): an even grid misses Nyquist and breaks the
    # reflection symmetry m(-xi)=conj(m(xi)), silently destroying the HT
    # involution (observed 8e-1 gate failure at N=1024 vs 3e-12 at N=1025).
    grid_list = json.loads(os.environ.get(
        "GRIDS_1067", "[[1025,20.0],[2049,20.0],[4097,20.0],[8193,20.0]]"))
    slists_raw = os.environ.get("SLIST_1067")
    if slists_raw:
        out, slists = [], []
        for part in slists_raw.split(";"):
            nums = part.strip().strip("[]")
            slists.append([int(x) for x in nums.split(",") if x.strip()] if nums else [])
    else:
        slists = [[], [2], [2, 3], [2, 3, 5]]

    for (N, T) in grid_list:
        t, dt, xi, _dxi = grids(N, T)
        F = dft_matrix(xi, t, N)
        E_diag = (t >= 0.0).astype(float)
        print(f"\n--- grid N={N} T={T:g} (dt={dt:.5f}, xi_max={abs(xi).max():.1f}) ---")
        for S in slists:
            phase = transport_phase(xi, S)
            name = "S=" + ",".join(str(p) for p in S) or "src"
            gsym = np.max(np.abs(phase[::-1] - phase.conj()))
            HT = build_HT(phase, F, N)
            if not S:
                # gates on the source operator (anchor case carries them all)
                g1 = float(np.linalg.norm(HT @ HT - np.eye(N), ord=2))
                g2 = float(np.linalg.norm(HT - HT.conj().T, ord=2))
                print(f"[gate HT^2=I] {g1:.2e}   [gate HT=HT*] {g2:.2e}   [gate m-sym] {gsym:.2e}")
            else:
                g1 = g2 = float("nan")
                print(f"[gate m-sym S={S}] {gsym:.2e}")
            assert gsym < 1e-10, "transported phase loses reflection symmetry"
            if not S:
                assert g1 < 1e-8 and g2 < 1e-8, "HT is not a self-adjoint involution"

            r = fkhs_probe(HT, E_diag, N)
            print(f"[gate positivity B] lambda_min(B) = {r['lam_min_B']:.3e}   "
                  f"[meet ladder] d={r['d']}  min-meet-lambda={r['meet_lam_min']:.10f}")
            if r["lam_min_B"] < -1e-6:
                print(f"[gate] FAIL: B has negative eigenvalue for {name} -> model misread, STOP")
                raise SystemExit(2)
            print(f"[W invariance] ||(I-Q_S) W|| = {r['w_res']:.3e}   "
                  f"(scale d~{r['d']}, N={N})")
            # 1063-style cross-validation diagnostics (report, not gate): the M
            # spectrum was already decomposed inside fkhs_probe - reuse it.
            mgap, mnonmeet = gap_split_stats(r["mvals"])
            print(f"[cross 1063] M-spectrum meet count={mgap} (expect {r['d']}), "
                  f"M nonmeet-sum={mnonmeet:.4f} vs fk_hs_sq={r['fk_hs_sq']:.4f}")

            np.save(f"{outdir}/1067_Bspec_N{N}_T{T:g}_{name.replace('S=', '').replace(',', '_') or 'src'}.npy",
                    r["lam"])
            print(f"SUMMARY|N{N}T{T:g}|{name}|d={r['d']}|fk_hs_sq={r['fk_hs_sq']:.4f}"
                  f"|trM_minus_d={r['tr_M_minus_d']:.4f}|khs_eigsum={r['khs_eigsum']:.4f}"
                  f"|fk_direct={r['fk_hs_sq_direct']:.4f}|consistency={r['consistency']:.2e}"
                  f"|meet_gap_count={mgap}|nonmeet_1063style={mnonmeet:.4f}")

    # ---- dt-invariance pair: same xi_max window at two resolutions -----------
    dtinv = json.loads(os.environ.get("DTINV_GRIDS_1067", "[[4097,20.0],[8193,40.0]]"))
    if len(dtinv) < 2:
        print("\n--- dt-invariance skipped (fewer than two grids given) ---")
        return
    print("\n--- dt-invariance (fixed window; M depends on N alone in this rig) ---")
    for S in slists:
        name = "S=" + ",".join(str(p) for p in S) or "src"
        vals = []
        for (N, T) in dtinv:
            t, _dt, xi, _dxi = grids(N, T)
            F = dft_matrix(xi, t, N)
            E_diag = (t >= 0.0).astype(float)
            phase = transport_phase(xi, S)
            HT = build_HT(phase, F, N)
            r = fkhs_probe(HT, E_diag, N)
            vals.append(r["fk_hs_sq"])
        rel = abs(vals[0] - vals[1]) / max(abs(vals[0]), 1e-300)
        print(f"SUMMARY|dtinv|{name}|fk_hs_sq={vals[0]:.4f} vs {vals[1]:.4f} | "
              f"rel-diff={rel:.2e}")

    print("\n=== done: grep 'SUMMARY|' in this log for the decision table ===")


if __name__ == "__main__":
    run()
