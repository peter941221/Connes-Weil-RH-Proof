#!/usr/bin/env python3
"""Annular Gram trace rig (record 1675; map 044 sec 4 item 1).

Committed objects being modeled (read from the Lean tree, record-1675
derivation):

  space     finiteSCarrier = L^2(R, du), u = log variable
  kernel C  = rootConvolution owner = cc20GlobalLogConvolution g*, the
            convolution by the compactly supported involution test g*
            (SelectedWeilSquare.lean:25; support radius R)
  window    P_n = kernelIntervalProjection (-(n:R)) (n:R) 0 = M_{1_{[-n,n]}}
            (SelectedCrossingOperatorBridge.lean:1564)
  H         ccm24ArchimedeanHardyTitchmarsh: (Hu)^ (xi) = m(xi) * uhat(-xi),
            m(s) = Gamma_R(1/2 - i s) / Gamma_R(1/2 + i s),
            Gamma_R(s) = pi^{-s/2} Gamma(s/2)
            (CCM24HardyTitchmarsh.lean:104, :365; involutive)
  carrier   archimedeanSoninCarrier(lambda) = range(E) meet range(H^-1 E H),
            E = M_{1_{[log lambda, infinity)}}  (CCM24HardyTitchmarsh.lean:352)
  object    sourceRootAnnularGram trace along the carrier basis
            = SUM_i || 1_{N <= |u| <= n} C e_i ||^2 = tr(W* W R_0)
            (C1G8R3SourceRootFiniteWindowCriterion.lean:61-108)

Question (map 044 decision gate): does B(N) = T(N, n_max) decay with N
(kernel-diagonal attack viable) or saturate at a positive constant (the S3
face needs genuine cancellation; shift weight to the witness front)?

Method: block alternating projections V <- orth(E Q E V) converge to the top
principal directions of (E, Q); the Rayleigh spectrum IS the meet spectrum
(sigma = 1 directions are exact carrier vectors).  The trace is read on the
sigma >= 1 - tau family; defects are quoted (F52: degenerate floors report
nothing).

Controls (F43):
  (a) m = 1: H degenerates to the reflection u -> u(-.), the carrier is
      exactly L^2[-a, a], a = log(1/lambda), and B(N) = 0 for N >= a + R
      by support algebra.  The grid must read live mass below a + R and
      exact zero past it (liveness + floor in one control).
  (b) H involution H^2 = I on the grid (m(xi) m(-xi) = 1 exactly).
  (c) |m| = 1 on the real line.
  (d) K = F^{-1}(m(-.)) mass fraction on x < 0 vs the 1633 reading 98.4%.
  (e) aliasing floor: one real row rerun at doubled resolution.
"""

import json
import numpy as np
from scipy.sparse import diags
from scipy.special import loggamma

# ----------------------------------------------------------------------
# grid and committed symbol (module-level, rebuilt for resolution runs)
# ----------------------------------------------------------------------

L_DOMAIN = 40.0
M_GRID = 4096
DU = 2.0 * L_DOMAIN / M_GRID
U = -L_DOMAIN + DU * np.arange(M_GRID)
XI = np.fft.fftfreq(M_GRID, d=DU)
SQRT_M = np.sqrt(M_GRID)
IDX_REV = (-np.arange(M_GRID)) % M_GRID


def rebuild_grid(L, M):
    global L_DOMAIN, M_GRID, DU, U, XI, SQRT_M, IDX_REV
    L_DOMAIN, M_GRID = L, M
    DU = 2.0 * L / M
    U = -L + DU * np.arange(M)
    XI = np.fft.fftfreq(M, d=DU)
    SQRT_M = np.sqrt(M)
    IDX_REV = (-np.arange(M)) % M


def log_gamma_R(s):
    s = np.asarray(s, dtype=complex)
    return -0.5 * s * np.log(np.pi) + loggamma(0.5 * s)


def m_symbol(xi):
    """m(xi) = Gamma_R(1/2 - 2 pi i xi) / Gamma_R(1/2 + 2 pi i xi)."""
    t = 2.0 * np.pi * np.asarray(xi, dtype=complex)
    return np.exp(log_gamma_R(0.5 - 1j * t) - log_gamma_R(0.5 + 1j * t))


def unitary_fft(v):
    return np.fft.fft(v) / SQRT_M


def unitary_ifft(w):
    return np.fft.ifft(w) * SQRT_M


def make_phase():
    """Committed scattering phase on the grid, with the Nyquist/DC modes
    pinned to 1: +-1/(2 du) is a single FFT sample that is not its own
    conjugate-reversal image, so m(xi) m(-xi) = 1 cannot hold there.
    Pinning one unit-modulus mode keeps H exactly involutive on the grid."""
    ph = m_symbol(XI).astype(complex)
    ph[0] = 1.0
    ph[M_GRID // 2] = 1.0
    return ph


def apply_H(v, phase, adj=False):
    """(Hv)^ (xi) = phase(xi) * vhat(-xi); v may be a matrix of columns.

    adj=True returns the adjoint/inverse: (H* v)^ = conj(phase(-xi)) vhat(-xi).
    For involutive phases (committed m, m = 1) this equals the forward map."""
    vhat = unitary_fft(v)
    if adj:
        ph = np.conj(phase)[IDX_REV]
    else:
        ph = phase
    if vhat.ndim == 1:
        return unitary_ifft(ph * vhat[IDX_REV])
    return unitary_ifft(ph[:, None] * vhat[IDX_REV, :])


def norm2(v):
    return DU * float(np.sum(np.abs(v) ** 2))


# ----------------------------------------------------------------------
# self-tests
# ----------------------------------------------------------------------

def self_tests():
    out = {}
    rng = np.random.default_rng(1637)
    v = rng.standard_normal(M_GRID) + 1j * rng.standard_normal(M_GRID)

    ph = make_phase()
    hh = apply_H(apply_H(v, ph), ph)
    out["H2_rel_err"] = float(np.linalg.norm(hh - v) / np.linalg.norm(v))

    mm = m_symbol(XI)
    out["max_abs_m_minus_1"] = float(np.max(np.abs(np.abs(mm) - 1.0)))

    left = U < 0
    for name, sym in [("K_minus_left_mass", -XI), ("K_plus_left_mass", XI)]:
        kk = unitary_ifft(m_symbol(sym)) * SQRT_M / DU
        out[name] = float(np.sum(np.abs(kk[left]) ** 2)
                          / np.sum(np.abs(kk) ** 2))
    out["K_left_mass_reference_1633"] = 0.984

    print("[self-test]", json.dumps(out))
    assert out["H2_rel_err"] < 1e-10, "H involution failed on the grid"
    assert out["max_abs_m_minus_1"] < 1e-12, "m not unimodular"
    return out


# ----------------------------------------------------------------------
# kernels, projections, the meet
# ----------------------------------------------------------------------

def bump_kernel(R):
    g = np.zeros_like(U)
    inside = np.abs(U) < R
    g[inside] = np.exp(-1.0 / (1.0 - (U[inside] / R) ** 2))
    g /= np.sqrt(DU * np.sum(g ** 2))
    return g


def conv_operator(R):
    """Toeplitz convolution by the R-supported kernel, zero-extension bounds.

    C[i, j] = du * g(u_i - u_j); constant diagonals du * g(off * du)."""
    bw = int(np.ceil(R / DU)) + 1
    offs = np.arange(-bw, bw + 1)
    vals = [DU * float(np.exp(-1.0 / (1.0 - (min(abs(o * DU), R - 1e-9) / R) ** 2)))
            if abs(o * DU) < R else 0.0 for o in offs]
    return diags(vals, offs, shape=(M_GRID, M_GRID), format="csr")


def apply_Q(v, mask, phase):
    """Q = H^-1 E H; v may be a matrix of columns."""
    return apply_H(mask[:, None] * apply_H(v, phase), phase, adj=True)


def meet_block(lam, phase, dim=12, iters=400, seed=1637):
    """Top principal directions of (E, Q); Rayleigh spectrum = meet spectrum."""
    rng = np.random.default_rng(seed + int(round(1e3 * lam)))
    mask = (U >= np.log(lam)).astype(float)
    V = rng.standard_normal((M_GRID, dim)) + 1j * rng.standard_normal((M_GRID, dim))
    V, _ = np.linalg.qr(V)
    hist = []
    for it in range(iters):
        W = mask[:, None] * apply_Q(mask[:, None] * V, mask, phase)
        V, _ = np.linalg.qr(W)
        if it % 50 == 0 or it == iters - 1:
            R = V.conj().T @ (mask[:, None] * apply_Q(mask[:, None] * V, mask, phase))
            ev = np.real(np.linalg.eigvalsh(0.5 * (R + R.conj().T)))[::-1]
            hist.append((it, float(np.clip(ev[0], 0.0, 1.0))))
    R = V.conj().T @ (mask[:, None] * apply_Q(mask[:, None] * V, mask, phase))
    evals, evecs = np.linalg.eigh(0.5 * (R + R.conj().T))
    order = np.argsort(evals)[::-1]
    evals = np.clip(np.real(evals[order]), 0.0, 1.0)
    return V @ evecs[:, order], evals, hist


# ----------------------------------------------------------------------
# the trace
# ----------------------------------------------------------------------

def annular_trace(Cmat, V, N_values, n_values):
    W = Cmat @ V
    table = {}
    for N in N_values:
        row = {}
        for n in n_values:
            if n <= N:
                continue
            msk = (np.abs(U) >= N) & (np.abs(U) <= n)
            row[n] = float(DU * np.sum(np.abs(W[msk, :]) ** 2))
        table[N] = row
    density = DU * np.sum(np.abs(W) ** 2, axis=1)
    return table, density


def slope_loglog(ns, ys, kmin=3):
    ns = np.asarray(ns, float)
    ys = np.asarray(ys, float)
    good = ys > 0
    if good.sum() < kmin + 1:
        return None
    x = np.log(ns[good])
    y = np.log(ys[good])
    k = max(kmin, len(x) // 3)
    return float(np.polyfit(x[-k:], y[-k:], 1)[0])


# ----------------------------------------------------------------------
# one scale
# ----------------------------------------------------------------------

def run_scale(lam, R, L=40.0, M=4096, dim=12, iters=400, tag=""):
    rebuild_grid(L, M)
    a = float(np.log(1.0 / lam))
    nmax = L - R - 1.0
    Ns = [round(x, 3) for x in
          [0.5 * a, 0.8 * a,
           a + R + 0.5, a + R + 3.0, a + R + 8.0, a + R + 16.0, a + R + 26.0]
          if x < nmax - 2.0]
    n_grid = sorted({round(N + 2.0, 3) for N in Ns} | {round(nmax, 3)})

    phase_real = make_phase()
    phase_one = np.ones_like(XI, dtype=complex)
    Cmat = conv_operator(R)

    res = {"lambda": float(lam), "a": a, "R": R, "L": L, "M": M_GRID,
           "du": DU, "tag": tag, "N_values": Ns, "n_max": nmax}

    # ---- model control m = 1 ----
    V1, ev1, _ = meet_block(lam, phase_one, dim=dim, iters=iters)
    res["model_rayleigh_top3"] = [round(float(x), 10) for x in ev1[:3]]
    res["model_accept_dim"] = int(np.sum(ev1 >= 1.0 - 1e-2))
    res["model_dim_reference"] = int(2 * a / DU)
    t1, d1 = annular_trace(Cmat, V1, Ns, n_grid)
    res["model_T"] = {str(N): t1[N] for N in Ns}
    tail_rows = [N for N in Ns if N >= a + R]
    inner_rows = [N for N in Ns if N < a + R]
    res["model_B_max_past_edge"] = max((t1[N][nmax] for N in tail_rows), default=None)
    res["model_B_min_inner"] = min((t1[N][nmax] for N in inner_rows), default=None)

    # ---- real phase ----
    Vr, evr, hist = meet_block(lam, phase_real, dim=dim, iters=iters)
    res["real_rayleigh_top8"] = [round(float(x), 8) for x in evr[:8]]
    res["real_sigma_top"] = round(float(np.sqrt(evr[0])), 8)
    res["real_convergence_history"] = hist[:6]
    fam = Vr[:, evr >= 1.0 - 1e-2]
    res["family_note"] = ("exact-at-tau=1e-2" if fam.shape[1]
                          else "top-3 approximate (defect quoted)")
    if fam.shape[1] == 0:
        fam = Vr[:, :3]
    res["family_dim"] = int(fam.shape[1])

    tr, dens = annular_trace(Cmat, fam, Ns, n_grid)
    res["real_T"] = {str(N): tr[N] for N in Ns}
    res["real_B_tail"] = {str(N): tr[N][nmax] for N in tail_rows}
    res["real_B_slope_loglog_tail"] = slope_loglog(tail_rows,
                                                   [tr[N][nmax] for N in tail_rows])
    res["real_saturation_ratio"] = {
        str(N): ((tr[N][nmax] / tr[N][round(N + 2.0, 3)])
                 if tr[N][round(N + 2.0, 3)] > 0 else None) for N in Ns}
    inner = np.abs(U) < a + R
    res["real_inner_mass"] = float(DU * np.sum(dens[inner]))
    res["real_total_mass"] = float(DU * np.sum(dens))

    print(f"[scale{tag}] lam={lam:.4f} a={a:.3f} "
          f"model_accept={res['model_accept_dim']}/{res['model_dim_reference']} "
          f"model_B_past_edge={res['model_B_max_past_edge']:.3e} "
          f"model_B_inner_min={res['model_B_min_inner']:.3e} | "
          f"sigma_top={res['real_sigma_top']:.6f} fam={res['family_dim']} "
          f"B_slope={res['real_B_slope_loglog_tail']} "
          f"sat_ratio_last={list(res['real_saturation_ratio'].values())[-1]}")
    return res


def run_meet_dimension_control(lam, R, dim=40, tag="-dim40"):
    """Decision control for the forced-meet mechanism.

    Dimension counting: on the grid, dim E = dim Q = (L + a)/du, so
    dim(E meet Q) >= dim E + dim Q - M = 2a/du FORCED, for ANY conjugating
    unitary of the form H = (phase . reflection).  Prediction: the real
    committed phase, the m = 1 phase, and a GENERIC random unit-modulus
    phase all show the same forced meet dimension and sigma = 1 readings.
    If the committed phase were special at grid level (a genuine carrier
    signal), its count would exceed the random-phase control."""
    rebuild_grid(40.0, 4096)
    a = float(np.log(1.0 / lam))
    rng = np.random.default_rng(929)
    rand_phase = np.exp(2j * np.pi * rng.random(M_GRID))
    rand_phase[0] = 1.0
    rand_phase[M_GRID // 2] = 1.0

    out = {"lambda": float(lam), "forced_dim_reference": int(2 * a / DU),
           "block_dim": dim}
    for name, ph in [("real", make_phase()),
                     ("model", np.ones_like(XI, dtype=complex)),
                     ("random", rand_phase)]:
        V, ev, _ = meet_block(lam, ph, dim=dim, iters=600, seed=777)
        out[f"{name}_accepted_dim"] = int(np.sum(ev >= 1.0 - 1e-8))
        out[f"{name}_sigma_top"] = round(float(np.sqrt(ev[0])), 10)
        out[f"{name}_rayleigh_tail"] = round(float(ev[-1]), 10)
        # u-support width of the top vector (where 99.9% of |v|^2 lives)
        w = np.abs(V[:, 0]) ** 2
        cum = np.cumsum(w) / np.sum(w)
        lo = float(U[int(np.searchsorted(cum, 0.0005))])
        hi = float(U[int(np.searchsorted(cum, 0.9995))])
        out[f"{name}_top_support_width"] = [round(lo, 3), round(hi, 3)]
        print(f"[dim40-{name}] accepted={out[f'{name}_accepted_dim']}"
              f" sigma_top={out[f'{name}_sigma_top']}"
              f" tail_rayleigh={out[f'{name}_rayleigh_tail']}"
              f" support=[{lo:.2f},{hi:.2f}] forced_ref={out['forced_dim_reference']}")
    return out


def main():
    tests = self_tests()
    allout = {"self_tests": tests, "scales": []}

    R = 1.0
    for lam in [0.5, float(np.exp(-1.0)), 0.2]:
        allout["scales"].append(run_scale(lam, R))

    # (e) aliasing floor: doubled resolution, same row
    allout["scales"].append(run_scale(float(np.exp(-1.0)), R, M=8192, tag="-hi"))

    # B1/B2 lean: sigma_top vs window length
    allout["scales"].append(run_scale(float(np.exp(-1.0)), R, L=20.0, M=2048,
                                      tag="-shortL"))

    # forced-meet decision control: real vs model vs generic random phase
    allout["meet_dimension_control"] = run_meet_dimension_control(
        float(np.exp(-1.0)), R)

    with open("annular_gram_trace_1675_results.json", "w") as fh:
        json.dump(allout, fh, indent=1, default=float)
    print("[done] results written to annular_gram_trace_1675_results.json")


if __name__ == "__main__":
    main()
