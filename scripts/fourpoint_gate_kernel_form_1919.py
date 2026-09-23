#!/usr/bin/env python3
# fourpoint_gate_kernel_form_1919.py — record 1919
#
# Exact reformulation probe for the 103 Cut-2 gate determinant.
#
# Claim tested here (paper derivation; engines from the 1918 rig, imported):
# the whole gate functional on the annihilator-detector span is a single
# spectral pairing ICgate(F) = ∫ K(ξ)·F̂(ξ) dξ with the EXPLICIT kernel
#
#   K(ξ) = σ(2πξ) + 2 Σ_{visible n} (Λ(n)/sqrt(n))·cos(2πξ log n),
#   σ(u) = log π − Re ψ(1/4 − i u/2),
#
# and on the owner pair (u = P(D)g, W = |ĝ|²) the three gate entries are
#
#   D = ICgate(u*⋆u) = ∫ K·P²·W,  B01 = ICgate(u*⋆g) = ∫ K·P·W,
#   C = ICgate(g*⋆g) = ∫ K·W,
#
# with the real even quartic
#
#   P(ξ) = (δ² + γ² − (2πξ)²)² + 4δ²(2πξ)²,   (ρ = (1/2 + δ) + iγ).
#
# Consequences verified numerically per case:
#   (1) the three kernel-form integrals reproduce the engine readings;
#   (2) the exact variance identity for the signed measure μ = K·W dξ,
#       A = μ(R):   det = D·C − B01² = A²·Var_ν(P) with ν = μ/A and
#       Var_ν(P) = (1+f)Var_+ − f·Var_− − f(1+f)·Δ²,
#       f = μ_−/A the negative mass ratio, Δ = mean_+ − mean_−;
#   (3) the sufficient sign criterion f·Δ² > Var_+ (implies det < 0).
# The same decomposition is reported for the arch channel μ_a = σ W dξ.
#
# No gate sign is proved here.

import json
import math
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import numpy as np  # noqa: E402

import fourpoint_diagonal_sign_1918 as rig  # noqa: E402


def ghat_grid(g):
    """ĝ(ξ) = ∫ g(x) e^{−2πiξx} dx on the padded FFT grid (E3 convention)."""
    Fp = np.zeros(rig.NF, dtype=complex)
    Fp[:rig.N] = g
    Fh = rig.DU * np.fft.fft(Fp)
    xi = np.fft.fftfreq(rig.NF, d=rig.DU)
    Fh = Fh * np.exp(2j * np.pi * xi * rig.LX)
    return xi, Fh


def kernel_grid(xi, S_pair):
    """K(ξ) = σ(2πξ) + 2 Σ_visible (Λ(n)/√n) cos(2πξ log n)."""
    K = rig.sigma_vec(2.0 * np.pi * xi)
    for n, lam in rig.prime_powers_up_to(math.exp(S_pair)):
        K = K + 2.0 * lam / math.sqrt(n) * np.cos(2.0 * np.pi * xi * math.log(n))
    return K


def stats(mu, x):
    """Mass/mean/variance of the positive and negative parts of a signed
    grid-measure mu with test function x."""
    mp = mu[mu > 0].sum()
    mm = -mu[mu < 0].sum()
    xp = (mu * x)[mu > 0].sum() / mp
    xm = -(mu * x)[mu < 0].sum() / mm
    vp = (mu * x * x)[mu > 0].sum() / mp - xp * xp
    vm = -(mu * x * x)[mu < 0].sum() / mm - xm * xm
    return mp, mm, xp, xm, vp, vm


def main():
    rig.log("record 1919 — gate kernel form and the determinant variance identity")
    with open("results/1918_fourpoint_diagonal_sign_certified.json") as fh:
        cert = json.load(fh)
    by_tag = {c["tag"]: c for c in cert["cases"]}

    G14 = 14.134725141734693
    G21 = 21.022039638771555
    probes = [(0.8, 0.05, G14), (1.0, 0.05, G14),
              (1.0, 0.30, G14), (1.3, 0.05, G21)]
    out = []
    for c, delta, gamma in probes:
        tag = "c=%.1f d=%.2f g=%.2f" % (c, delta, gamma)
        if tag not in by_tag:
            rig.log("skip %s (not in certified set)" % tag)
            continue
        S_pair = 2.0 * c
        g = rig.bump(c)
        xi, Fh = ghat_grid(g)
        W = (Fh * np.conj(Fh)).real
        dxi = 1.0 / (rig.NF * rig.DU)
        om = 2.0 * np.pi * xi
        P = (delta * delta + gamma * gamma - om * om) ** 2 \
            + 4.0 * delta * delta * om * om
        K = kernel_grid(xi, S_pair)
        sig = rig.sigma_vec(om)

        # P cross-check against the committed poly_P on the orbit nodes
        rho = (0.5 + delta) + 1j * gamma
        _, nodes = rig.fourpoint_annihilator(g, rho)
        s_ax = -2j * np.pi * xi
        Pnodes = np.array([rig.poly_P(s, nodes) for s in s_ax[::997]])
        Pcheck = np.max(np.abs(Pnodes - P[::997])) / np.max(np.abs(P))

        A = float(np.sum(K * W) * dxi)
        I1 = float(np.sum(K * P * W) * dxi)
        I2 = float(np.sum(K * P * P * W) * dxi)
        Aa = float(np.sum(sig * W) * dxi)
        I1a = float(np.sum(sig * P * W) * dxi)
        I2a = float(np.sum(sig * P * P * W) * dxi)

        js = by_tag[tag]
        D_e = js["cert"]["D_cert"]
        C_e = js["C"]["IC"]
        B_e = js["B01"]["IC"]
        det_e = D_e * C_e - B_e * B_e
        det_k = I2 * A - I1 * I1
        det_a = I2a * Aa - I1a * I1a
        Da_e, Ca_e, Ba_e = js["D"]["arch_sigma"], js["C"]["arch_sigma"], \
            js["B01"]["arch_sigma"]

        rig.log("case %s" % tag)
        rig.log("  kernel form vs engine: D %.3e/%.3e  C %.3e/%.3e  B01 %.3e/%.3e"
                % (I2, D_e, A, C_e, I1, B_e))
        rig.log("  arch form   vs engine: D %.3e/%.3e  C %.3e/%.3e  B01 %.3e/%.3e"
                % (I2a, Da_e, Aa, Ca_e, I1a, Ba_e))
        rig.log("  P vs poly_P rel err %.2e" % Pcheck)
        rig.log("  det: engine %.4e  kernel %.4e (rel %.2e)  arch %.4e"
                % (det_e, det_k, (det_k - det_e) / det_e, det_a))

        for name, mu in (("full K", K * W * dxi), ("arch", sig * W * dxi)):
            det_ref = det_k if name == "full K" else det_a
            det_eng = det_e if name == "full K" \
                else Da_e * Ca_e - Ba_e * Ba_e
            mp, mm, xp, xm, vp, vm = stats(mu, P)
            Am = mp - mm
            f = mm / Am
            delta_m = xp - xm
            var = (1.0 + f) * vp - f * vm - f * (1.0 + f) * delta_m ** 2
            det_id = Am * Am * var
            # moment form: P(u) = u^2 + a*u + b with u = (2 pi xi)^2, so
            # Var_nu(P) = (m4 - m2^2) + 2a(m3 - m1 m2) + a^2(m2 - m1^2),
            # moments under nu = mu/A.
            nu = mu / Am
            u2 = om * om
            m1 = float(np.sum(nu * u2))
            m2 = float(np.sum(nu * u2 * u2))
            m3 = float(np.sum(nu * u2 ** 3))
            m4 = float(np.sum(nu * u2 ** 4))
            aa = -2.0 * (gamma * gamma - delta * delta)
            mform = (m4 - m2 * m2) + 2.0 * aa * (m3 - m1 * m2) \
                + aa * aa * (m2 - m1 * m1)
            det_mf = Am * Am * mform
            crit_full = bool(f * vm + f * (1.0 + f) * delta_m ** 2
                            > (1.0 + f) * vp)
            crit_suff = bool(f * delta_m ** 2 > vp)
            rig.log("  [%s] A=%.4e f=%.5f m+=%.4e m-=%.4e D=%.4e "
                    "Var+=%.3e Var-=%.3e" % (name, Am, f, xp, xm, delta_m,
                                             vp, vm))
            rig.log("  [%s] identity vs same-grid 2x2 det: P-form rel %.2e, "
                    "moment-form rel %.2e; vs engine rel %.2e; criterion "
                    "full %s suff(f*D^2>Var+) %s (f*D^2=%.3e Var+=%.3e)"
                    % (name, (det_id - det_ref) / det_ref,
                       (det_mf - det_ref) / det_ref,
                       (det_id - det_eng) / det_eng,
                       crit_full, crit_suff, f * delta_m ** 2, vp))
            out.append({"tag": tag, "channel": name, "A": Am, "f": f,
                        "m_plus": xp, "m_minus": xm, "delta_mean": delta_m,
                        "Var_plus": vp, "Var_minus": vm,
                        "moments_u2": {"m1": m1, "m2": m2, "m3": m3,
                                       "m4": m4, "a": aa},
                        "det_identity": det_id, "det_moment_form": det_mf,
                        "det_same_grid": det_ref, "det_engine": det_eng,
                        "crit_full": crit_full, "crit_suff": crit_suff})
        out.append({"tag": tag, "kernel": {"D": I2, "C": A, "B01": I1,
                                           "det": det_k,
                                           "det_engine": det_e},
                    "arch": {"D": I2a, "C": Aa, "B01": I1a, "det": det_a,
                             "Pcheck": float(Pcheck)}})
    os.makedirs("results", exist_ok=True)
    with open("results/1919_gate_kernel_form.json", "w") as fh:
        json.dump(out, fh, indent=1, default=float)
    rig.log("wrote results/1919_gate_kernel_form.json")


if __name__ == "__main__":
    main()