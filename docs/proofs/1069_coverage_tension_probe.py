# 1069 - LINE (5) coverage-positivity tension probe (LEVEL-2), in the 1068 rig.
#
# Design record: 1069_line5_coverage_idea_ledger.md s3 (fork stated BEFORE the
# run). Question: does the continuum detector-mass function
#     f(k) := lim_{Xi->inf} t_tr1(k, Xi)        (T = D_k K_S trace norm)
# blow up as k ↓ 0 (H1: f(k) ~ k^(-0.4), the pass-band model inheriting 1067's
# raw ~ Xi^0.4) or stay bounded (H2)?  A FIXED-grid k-sweep cannot see this
# (D_k -> I as k -> 0, so t_tr1 saturates at the finite-grid raw value).  The
# discriminating measurement is the CONSTANT-PRODUCT ray k*Xi = kappa0:
# along it H1 predicts t_tr1 ~ Xi^0.4 GROWTH, H2 predicts flatness.  Points
# with k*Xi >= 6.4 pool onto f(k); the log-log slope b of t_tr1 vs k there is
# the fork statistic (H1: b in [-(0.5), -(0.3)]; H2: |b| small, t within ~2x
# of its k=1 value).
#
# Also printed: the zero-coverage matrix w_k(xi_j), xi_j = gamma_j / (2 pi),
# gamma_j from mpmath zetazero (j up to 100), and the k needed for w >= 1/2.
#
# Reuses the 1068 rig verbatim (build_context + measure_k; every Lean identity
# gate ID-1/2/3/5 stays live inside measure_k).  k = 1 rows cross-validate the
# committed 1068 s5.1 table (5e-3).  Deterministic, no npz output; acceptance
# = the SUMMARY/MATRIX/SLOPE/COV lines in the flushed log, never exit codes.
#
# Run (WSL, ONE command, log on the Linux side):
#   MSYS_NO_PATHCONV=1 wsl.exe --cd /home/peter/rh sh -c \
#     'env P1068=/home/peter/rh/docs/proofs/1068_root_commutator_ledger_probe.py \
#      /home/peter/.local/bin/uv run --with numpy --with scipy --with mpmath \
#      python -u docs/proofs/1069_coverage_tension_probe.py \
#      > /home/peter/1069_probe.log 2>&1; echo DONE-RC=$?'
# Env: GRIDS_1069 KS_1069 K8193_1069 SLIST_1069 KCOV_1069 JLIST_1069 KXIMIN_1069

import importlib.util
import json
import os

import numpy as np
from mpmath import mp, zetazero

_HERE = os.path.dirname(os.path.abspath(__file__))
_spec = importlib.util.spec_from_file_location(
    "p1068", os.environ.get("P1068",
                            os.path.join(_HERE, "1068_root_commutator_ledger_probe.py")))
assert _spec is not None and _spec.loader is not None, "1068 rig file not found"
p8 = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(p8)

# Committed 1068 s5.1 table: t_tr1 at k = 1.0, family {2,3,5} (anchor, 5e-3).
COMMITTED_1068_T = {1025: 3.7836, 2049: 3.7527, 4097: 3.7376, 8193: 3.7319}


def run():
    print("=== 1069 coverage-positivity tension probe (1068 rig, LEVEL-2) ===")
    mp.dps = 30
    p8.p.spotcheck_phase()

    grid_list = json.loads(os.environ.get(
        "GRIDS_1069", "[[1025,20.0],[2049,20.0],[4097,20.0],[8193,20.0]]"))
    ks_full = json.loads(os.environ.get("KS_1069", "[1.0, 0.5, 0.25, 0.125]"))
    ks_8193 = json.loads(os.environ.get("K8193_1069", "[0.5, 0.25]"))
    slists_raw = os.environ.get("SLIST_1069")
    if slists_raw:
        slists = []
        for part in slists_raw.split(";"):
            nums = part.strip().strip("[]")
            slists.append([int(x) for x in nums.split(",") if x.strip()] if nums else [])
    else:
        slists = [[], [2, 3, 5]]
    kcov = json.loads(os.environ.get("KCOV_1069", "[1.0, 0.5, 0.25, 0.125, 0.05, 0.02]"))
    jlist = json.loads(os.environ.get("JLIST_1069", "[1, 2, 3, 5, 10, 20, 30, 50, 100]"))
    kximin = float(os.environ.get("KXIMIN_1069", "6.4"))

    matrix = []                      # (fam_key, N, k, kxi, t_tr1, l_tr1, s_tr1, p_hs_sq)
    for (N, T) in grid_list:
        t, dt, xi, _dxi = p8.p.grids(N, T)
        F = p8.p.dft_matrix(xi, t, N)
        E_diag = (t >= 0.0).astype(float)
        xi_max = float(abs(xi).max())
        print(f"\n--- grid N={N} T={T:g} (dt={dt:.5f}, xi_max={xi_max:.1f}) ---")
        for S in slists:
            phase = p8.p.transport_phase(xi, S)
            name = "S=" + (",".join(str(x) for x in S) if S else "src")
            fam_key = ",".join(str(x) for x in S) if S else "src"
            gsym = float(np.max(np.abs(phase[::-1] - phase.conj())))
            assert gsym < 1e-10, "transported phase loses reflection symmetry"
            HT = p8.p.build_HT(phase, F, N)
            if not S:
                g1 = float(np.linalg.norm(HT @ HT - np.eye(N), ord=2))
                g2 = float(np.linalg.norm(HT - HT.conj().T, ord=2))
                assert g1 < 1e-8 and g2 < 1e-8, "HT not a self-adjoint involution"
                print(f"[gate HT^2=I] {g1:.2e}   [gate HT=HT*] {g2:.2e}   "
                      f"[gate m-sym] {gsym:.2e}")
            else:
                print(f"[gate m-sym {name}] {gsym:.2e}")

            ctx = p8.build_context(F, HT, E_diag, N, name)
            print(f"[meet ladder] d={ctx['d']}   [FK unw fp-unweighted] "
                  f"{ctx['fk_unw']:.4f}")
            ks = ks_full if N < 8193 else ks_8193
            for k in ks:
                c_amp = np.exp(-0.25 * (k * xi) ** 2)
                w_amp = np.exp(-0.5 * (k * xi) ** 2)
                r = p8.measure_k(F, ctx, N, float(k), c_amp, w_amp, (fam_key, N))
                kxi = k * xi_max
                if k == 1.0 and fam_key == "2,3,5":
                    ref = COMMITTED_1068_T.get(N)
                    if ref is not None:
                        assert abs(r["t_tr1"] - ref) < 5e-3, \
                            f"k=1 anchor mismatch vs 1068 at N={N}: " \
                            f"{r['t_tr1']:.4f} vs {ref}"
                matrix.append((fam_key, N, float(k), float(kxi), r["t_tr1"],
                               r["l_tr1"], r["s_tr1"], r["p_hs_sq"]))
                print(
                    f"SUMMARY|N{N}T{T:g}|{name}|k={k:g}|kxi={kxi:.2f}"
                    f"|t_tr1={r['t_tr1']:.4f}|l_tr1={r['l_tr1']:.4f}"
                    f"|s_tr1={r['s_tr1']:.4f}|p_hs_sq={r['p_hs_sq']:.4f}"
                    f"|res1={r['res_id1']:.1e}|res2={r['res_ledger']:.1e}"
                    f"|res3={r['res_id3']:.1e}")
                del c_amp, w_amp, r
            del ctx, HT
        del F

    # ---- the fork statistic: log-log slope of t_tr1 vs k on pooled asymptotic
    #      points (k*Xi >= kximin), plus the k <= 0.5 sub-decade ---------------
    print("\n--- fork statistic (t_tr1 vs k, pooled k*Xi >= "
          f"{kximin:g}) ---")
    for fam_key in sorted({m[0] for m in matrix}):
        rows = [m for m in matrix if m[0] == fam_key and m[3] >= kximin]
        if len(rows) < 3:
            continue
        for tag, subset in (
                ("all", rows),
                ("kle05", [m for m in rows if m[2] <= 0.5])):
            if len(subset) < 3:
                continue
            lk = np.log(np.array([m[2] for m in subset]))
            lt = np.log(np.array([m[4] for m in subset]))
            b, loga = np.polyfit(lk, lt, 1)
            res = lt - (loga + b * lk)
            print(f"SLOPE|{fam_key}|{tag}|n={len(subset)}|b={b:+.3f}"
                  f"|amp={np.exp(loga):.4f}|maxres={float(np.abs(res).max()):.4f}")
        # constant-product diagonals: flat in Xi => these ARE f(k) values
        for kap in sorted({round(m[3], 2) for m in rows}):
            diag = sorted([m for m in rows if abs(m[3] - kap) < 0.26],
                          key=lambda m: m[1])
            if len(diag) >= 2:
                vals = [m[4] for m in diag]
                line = " ".join(f"N{m[1]}:{m[4]:.4f}" for m in diag)
                print(f"DIAG|{fam_key}|kxi={kap:g}|maxmin="
                      f"{max(vals) / max(min(vals), 1e-300):.3f}|{line}")

    # ---- zero-coverage matrix: w_k(xi_j), xi_j = gamma_j / (2 pi) ----------
    print("\n--- coverage matrix w_k(xi_j) = exp(-(k xi_j)^2 / 2) ---")
    khalf = mp.sqrt(2 * mp.log(2))
    hdr = " ".join(f"k={k:g}".rjust(8) for k in kcov)
    print(f"COVHDR|{hdr}")
    for j in jlist:
        gam = mp.im(zetazero(int(j)))
        xij = gam / (2 * mp.pi)
        row = " ".join(f"{float(mp.exp(-0.5 * (k * xij) ** 2)):.4f}".rjust(8)
                       for k in kcov)
        print(f"COV|j={j}|gamma={float(gam):.4f}|xi={float(xij):.4f}"
              f"|k_half={float(khalf / xij):.4f}|{row}")

    print("\n=== done: grep 'SUMMARY|SLOPE|DIAG|COV' in this log for the fork ===")


if __name__ == "__main__":
    run()
