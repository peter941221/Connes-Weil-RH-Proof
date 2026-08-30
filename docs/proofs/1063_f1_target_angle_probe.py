# 1063 - F1 target-angle probe: discretize M = P_E Q_S P_E and read the principal
# angle spectrum (cos^2 theta_n) for S = {}, {2}, {2,3}, {2,3,5}.
#
# Model (each line pinned to a Lean definition, see record 1063 section 1):
#   H    = L2(R, dt)                                  GlobalLogHaar.lean:30
#   E    = multiplication by chi_{t >= 0}             CCM24LogRadialSupport.lean:67-69 (lambda=1)
#   m(xi)= GammaR(1/2-2*pi*i*xi)/conj(...)           CCM24HardyTitchmarsh.lean:43-106
#   HT   = F^* M_m Flip F (unitary involution)        CCM24HardyTitchmarsh.lean:331-365
#   T_S  = prod_p (1 - p^{-1/2} Shift_{-log p})       CCM24EulerTransport.lean:182-206
#   HT_S = T_S HT T_S^{-1} = F^* M_{m_S} Flip F,
#          m_S(xi) = m(xi) * mu(xi)/conj(mu(xi)),     (derivation, record 1063)
#          mu(xi) = prod_p (1 - p^{-1/2} e^{-2 pi i xi log p})
#   Q_S  = HT_S E HT_S ;  F1 <=> lambda_n(M_S) in l1
#
# Gates (AGENTS 7c): positivity of the positive operator is a hard assert;
# resolution AND interval sweeps must agree before any verdict is trusted;
# the source case S={} is the ANCHOR - if the anchor contradicts the repo's
# proven theorem (sourceProlateHilbertSchmidtFactor_unit_summable), the model
# reading is wrong and NOTHING here is trusted.
#
# Deterministic. Run: python 1063_f1_target_angle_probe.py

import math
import numpy as np
from scipy.special import loggamma

SQRT2 = math.sqrt(2.0)


def grids(N: int, T: float):
    dt = 2.0 * T / N
    t = (np.arange(N) - N // 2) * dt
    dxi = 1.0 / (N * dt)
    xi = (np.arange(N) - N // 2) * dxi
    return t, dt, xi, dxi


def dft_matrix(xi: np.ndarray, t: np.ndarray, N: int) -> np.ndarray:
    # unitary symmetric DFT: F[k,j] = exp(-2 pi i xi_k t_j)/sqrt(N)
    return np.exp(-2j * np.pi * np.outer(xi, t)) / math.sqrt(N)


def archimedean_phase(xi: np.ndarray) -> np.ndarray:
    # m = A/conj A = exp(2 i Im logA),  A = pi^{-z/2} Gamma(z/2),  z = 1/2-2 pi i xi
    z = 0.5 - 2j * np.pi * xi
    logA = -(z / 2.0) * math.log(math.pi) + loggamma(z / 2.0)
    return np.exp(2j * np.imag(logA))


def mu_transport(xi: np.ndarray, S: list) -> np.ndarray:
    mu = np.ones_like(xi, dtype=complex)
    for p in S:
        cp = p ** -0.5
        mu = mu * (1.0 - cp * np.exp(-2j * np.pi * xi * math.log(p)))
    return mu


def transport_phase(xi: np.ndarray, S: list) -> np.ndarray:
    m = archimedean_phase(xi)
    if not S:
        return m
    mu = mu_transport(xi, S)
    mu_neg = mu_transport(-xi, S)
    return m * (mu / mu_neg)


def build_HT(phase: np.ndarray, F: np.ndarray, N: int) -> np.ndarray:
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


def hermitian_part(A: np.ndarray) -> np.ndarray:
    return 0.5 * (A + A.conj().T)


def spectrum(E_diag: np.ndarray, HT: np.ndarray) -> np.ndarray:
    ED = np.diag(E_diag)
    M = ED @ HT @ ED @ HT @ ED  # E (HT E HT) E since HT^2 = I
    vals = np.linalg.eigvalsh(hermitian_part(M))
    return np.sort(vals)[::-1]


def summarize(name: str, vals: np.ndarray, N: int):
    top = vals[:8]
    ssum = float(np.sum(np.clip(vals, 0.0, None)))
    n_bulk = int(np.sum(vals > 0.99))
    n_half = int(np.sum(vals > 0.5))
    tail = float(np.sum(np.clip(vals, 0.0, None)[N // 2:]))
    print(f"[{name}] top8 = {np.array2string(top, precision=6)}")
    print(f"[{name}] sum(clip>=0) = {ssum:.4f}   #>0.99 = {n_bulk}   #>0.5 = {n_half}   "
          f"tail-sum(second half) = {tail:.4f}")
    # gap-based meet split: the leading block of eigenvalues >= 1-... is
    # separated from the genuine non-meet spectrum by a gap; fixed
    # thresholds like 0.99 mix the grid boundary layer into the meet.
    # banded sums are threshold-robust when a clean gap separates the
    # meet ladder (lambda near 1) from the genuine tail: report per band
    # so resolution growth (AC hypothesis) vs decay (TC hypothesis) is
    # directly comparable across grids.
    for lo in (0.003, 0.01, 0.05, 0.15, 0.5):
        hi = min(2.0 * lo, 0.95)
        b = vals[(vals > lo) & (vals <= hi)]
        print(f"[{name}] band({lo:.3f},{hi:.3f}]: count={len(b):4d}  sum={float(np.sum(b)):.4f}")
    g = 0.02
    jstar = 0
    for j in range(len(vals) - 1):
        if vals[j] - vals[j + 1] > g:
            jstar = j + 1
            break
    rest = vals[jstar:]
    rest = rest[rest > 1e-12]
    print(f"[{name}] meet block(first gap>{g}) = {jstar}   nonmeet-sum = {float(np.sum(rest)):.4f}   "
          f"top-nonmeet = {float(rest[0]) if len(rest) else 0.0:.6f}   "
          f"nextgap = {float(vals[jstar-1]-vals[jstar]) if jstar and jstar < len(vals) else 0.0:.4f}")


def parse_slist(raw):
    # "[];[2];[2,3,5]" -> [[], [2], [2,3,5]]
    out = []
    for part in raw.split(";"):
        nums = part.strip().strip("[]")
        out.append([int(x) for x in nums.split(",") if x.strip()] if nums else [])
    return out


def nonmeet_sum(vals: np.ndarray, g: float = 0.02):
    """(meet block size, sum of the rest) split by the FIRST gap > g."""
    js = [j for j in range(len(vals) - 1) if vals[j] - vals[j + 1] > g]
    jstar = js[0] + 1 if js else 0
    rest = vals[jstar:]
    return jstar, float(np.sum(rest[rest > 1e-12]))


def run():
    print("=== 1063 F1 target-angle probe ===")
    spotcheck_phase()
    import json
    import os
    outdir = os.environ.get("OUTDIR", "/tmp")
    # ODD N REQUIRED: an even grid misses the Nyquist point and breaks the
    # reflection symmetry m(-xi)=conj(m(xi)), silently destroying the HT
    # involution (observed: 8e-1 gate failure at N=1024 vs 3e-12 at N=1025).
    grid_list = json.loads(os.environ.get(
        "GRIDS_1063", "[[1025,20.0],[2049,20.0],[4097,20.0],[2049,40.0],[4097,40.0]]"))
    slists = parse_slist(os.environ.get(
        "SLIST_1063", "[];[2];[2,3];[2,3,5]")) if os.environ.get("SLIST_1063") \
        else [[], [2], [2, 3], [2, 3, 5]]
    for (N, T) in grid_list:
        t, dt, xi, _dxi = grids(N, T)
        F = dft_matrix(xi, t, N)
        E_diag = (t >= 0.0).astype(float)
        print(f"\n--- grid N={N} T={T} (dt={dt:.4f}, xi_max={abs(xi).max():.1f}) ---")
        for S in slists:
            phase = transport_phase(xi, S)
            # gate: the defining symmetry of the phase must hold on THIS grid
            gsym = np.max(np.abs(phase[::-1] - phase.conj()))
            HT = build_HT(phase, F, N)
            if not S:
                # gates on the source operator
                g1 = np.linalg.norm(HT @ HT - np.eye(N), ord=2)
                g2 = np.linalg.norm(HT - HT.conj().T, ord=2)
                print(f"[gate HT^2=I] {g1:.2e}   [gate HT=HT*] {g2:.2e}   "
                      f"[gate m-sym] {gsym:.2e}")
                assert g1 < 1e-8 and g2 < 1e-8 and gsym < 1e-10, \
                    "HT is not a self-adjoint involution"
            else:
                print(f"[gate m-sym S={S}] {gsym:.2e}")
                assert gsym < 1e-10, "transported phase loses reflection symmetry"
            vals = spectrum(E_diag, HT)
            lo = float(np.min(vals))
            print(f"[gate positivity] lambda_min = {lo:.3e} (S={S})")
            if lo < -1e-6:
                print(f"[gate] FAIL: negative eigenvalue for S={S} -> model misread, STOP")
                raise SystemExit(2)
            name = "S=" + ",".join(str(p) for p in S)
            summarize(name, vals, N)
            jb, st = nonmeet_sum(vals)
            print(f"SUMMARY|N{N}T{T:g}|{name}|meet={jb}|nonmeet-sum={st:.4f}")
            np.save(f"{outdir}/1063_spec_N{N}_T{T:g}_{name.replace('=','').replace(',','_') or 'src'}.npy",
                    vals)
    # H1 (plateau, F1 true) vs H2 (window-driven growth, F1 false) is read
    # from the SUMMARY lines: dt-halving at FIXED xi_max must not move the
    # sum (artifact check), and xi_max doubling must not bend it down.
    print("\n=== done: grep 'SUMMARY|' in this log for the decision table ===")


if __name__ == "__main__":
    run()
