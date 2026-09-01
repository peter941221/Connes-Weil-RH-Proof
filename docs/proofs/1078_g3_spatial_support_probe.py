# 1078 - g_3 spatial-support recon: does the pinned detector have a genuine compact radius?
#
# Design record + fork (stated BEFORE run): 1078_g3_spatial_support.md.
# Follows 1077 (consumer #2 PINNED numerically for zero #2, field #4 F-A).
#
# The gap: g_3 was BUILT in Mellin space as the *value* of a test at Mellin argument s,
#   g_3(s) = N' s(1-s)(s-1/2)^2 exp((-d^2 + i mu) s(1-s)).
# The Lean owner is SPATIAL: laplaceAt(phi)(s) = int e^{sx} phi(x) dx (bilateral Laplace of
# the log-coordinate function phi).  So g_3 is a CompactLogTest only if its spatial inverse
#   phi(u) = (1/2 pi i) int_{c-iT}^{c+iT} g_3(s) e^{-su} ds,  c=1/2
#           = e^{-u/2} (1/2 pi) int_{-T}^{T} g_3(1/2 + it) e^{-i u t} dt
# is COMPACTLY supported in [-log 2 / 2, log 2 / 2].  On the line s=1/2+it, s(1-s)=1/4+t^2,
# so g_3(1/2+it) = N' t^2(t^2+1/4) e^{-d^2(1/4+t^2)} e^{i mu (1/4+t^2)}: a polynomial in t
# times a Gaussian => phi is a Gaussian of width ~sqrt(2)*delta, i.e. Schwartz-decaying, not
# compact.  This probe MEASURES the tail mass outside the window and whether truncating to it
# preserves triple-vanishing + detects-rho + the field #4 sign at zero #2.
#
# Reuses the committed 1077 machinery (g_3, mu_3*, normalize_family3) via importlib; the heavy
# on-line work is done with a float64 closed form cross-checked against the mpmath g_3 at sample
# points (self-consistency gate).  Recon only: one fired config, j = 2.
#
# Run (WSL, ONE command, log on the Linux side):
#   MSYS_NO_PATHCONV=1 wsl.exe --cd /home/peter/rh sh -c \
#     '/home/peter/.local/bin/uv run --with numpy --with mpmath python -u \
#      docs/proofs/1078_g3_spatial_support_probe.py > /home/peter/1078_probe.log 2>&1; \
#      echo DONE-RC=$?'
# Env: CD_1078 (default 1.50), BETA_1078 (default 0.49)

import importlib.util
import os

import numpy as np
from mpmath import mp, mpf, pi as mpi, log as mlog

mp.dps = 30

# ---- reuse the committed 1077 machinery verbatim -----------------------------------
_here = os.path.dirname(os.path.abspath(__file__))
_spec = importlib.util.spec_from_file_location(
    "p1077", os.path.join(_here, "1077_pinned_detector_sign_probe.py"))
assert _spec is not None and _spec.loader is not None, \
    "committed 1077 probe not found next to this file"
p1077 = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(p1077)

make_g3 = p1077.make_g3            # g_3(s), mpmath closed form (the fired object verbatim)
normalize_family3 = p1077.normalize_family3   # N' so peak_t |g_3(1/2+it)| = 1
mu_3_star = p1077.mu_3_star        # phase retuning for the completion
zero_cache = p1077.zero_cache      # persisted zero cache, reused

_trapz = getattr(np, "trapezoid", None) or np.trapz   # numpy>=2 renamed trapz->trapezoid

CD = float(os.environ.get("CD_1078", "1.50"))       # fired deepest-flip config (1077)
BETA = float(os.environ.get("BETA_1078", "0.49"))
A_WINDOW = mlog(mpf(2)) / 2          # root-support half-width in log coord (= log 2 / 2)


def run():
    print("=== 1078 g_3 spatial-support recon (zero #2) ===", flush=True)

    import mpmath as _mp
    gamma_2 = float(mp.im(_mp.zetazero(2)))
    delta = CD / gamma_2
    d2 = delta * delta
    norm, _ = normalize_family3(delta)
    mu = float(mu_3_star(mpf(str(CD)) / mp.im(_mp.zetazero(2)), BETA, mp.im(_mp.zetazero(2))))

    a = float(A_WINDOW)
    print(f"cfg|cd={CD}|beta={BETA}|gamma2={gamma_2:.5f}|delta={delta:.6f}"
          f"|d2={d2:.6e}|N'={float(norm):.6e}|mu*={mu:.6f}|a=log2/2={a:.6f}",
          flush=True)

    # ---- mpmath g_3 (the fired object) for cross-check + node values --------------
    delta_mp = mpf(str(CD)) / mp.im(_mp.zetazero(2))
    norm_mp, _ = normalize_family3(delta_mp)
    mu_mp = mu_3_star(delta_mp, BETA, mp.im(_mp.zetazero(2)))
    g3 = make_g3(delta_mp, norm_mp, mu_mp)   # mpmath function of s

    def g3_line_np(t):
        """float64 closed form of g_3(1/2 + i t); even in t (all factors ~ t^2)."""
        q = 0.25 + t * t                       # s(1-s) on the line, real positive
        mag = float(norm_mp) * (t * t) * (q)   # |N' vf0 (s-1/2)^2| = N' t^2 (t^2+1/4)
        return mag * np.exp(-d2 * q) * np.exp(1j * float(mu_mp) * q)

    # ---- self-consistency: numpy closed form == mpmath g_3 on the line --------------
    ts = np.linspace(0.0, 8.0 / delta, 9)
    maxrel = 0.0
    for t in ts:
        v_np = g3_line_np(np.array([t]))[0]
        v_mp = complex(g3(mpf("0.5") + 1j * mpf(str(float(t)))))
        denom = abs(v_mp) if abs(v_mp) > 1e-12 else 1.0
        maxrel = max(maxrel, abs(v_np - v_mp) / denom)
    print(f"GATE|self-consistency|np vs mpmath g_3(1/2+it)|maxrel={maxrel:.2e}  "
          f"(<= 1e-8)", flush=True)
    assert maxrel < 1e-8, "float64 closed form diverges from the mpmath fired object"

    # ---- Bromwich inverse phi(u) = e^{-u/2}/(2 pi) int_{-T}^{T} g_3(1/2+it)e^{-iut}dt
    T = 10.0 / delta                          # e^{-d^2 t^2} decay sets the cutoff
    Nt = 8192
    tgrid = np.linspace(-T, T, Nt)
    Ft = g3_line_np(tgrid)                    # even in t
    u_max = max(6.0 * a, 4.0 / delta)         # several sigma past the window edge
    Nu = 4097
    ugrid = np.linspace(-u_max, u_max, Nu)

    print(f"grid|T={T:.3f}|Nt={Nt}|u_max={u_max:.3f}|Nu={Nu}", flush=True)
    phi = np.empty(Nu, dtype=complex)
    for iu in range(Nu):
        u = ugrid[iu]
        integrand = Ft * np.exp(-1j * u * tgrid)   # F even => imag part cancels by symmetry
        phi[iu] = np.exp(-0.5 * u) / (2.0 * mpi) * _trapz(integrand, tgrid)

    # ---- profile -------------------------------------------------------------------
    mag = np.abs(phi)
    ipeak = int(np.argmax(mag))
    print(f"profile|peak={mag[ipeak]:.6f}@u={ugrid[ipeak]:.4f}", flush=True)
    for name, uu in (("u=a", a), ("u=1.5a", 1.5 * a), ("u=3a", 3.0 * a),
                     ("u=-a", -a), ("u=6a", 6.0 * a)):
        idx = int(np.argmin(np.abs(ugrid - uu)))
        print(f"profile|{name}|u={ugrid[idx]:.4f}|abs(phi)={mag[idx]:.3e}"
              f"|rel_to_peak={mag[idx] / mag[ipeak]:.3e}", flush=True)

    # L^2 energy inside vs outside the window [-a, a].
    e = mag * mag
    total = float(_trapz(e, ugrid))
    inside_mask = np.abs(ugrid) <= a
    inside = float(_trapz(np.where(inside_mask, e, 0.0), ugrid))
    outside = total - inside
    frac_out = outside / total if total > 0 else float("nan")
    print(f"energy|total={total:.6e}|inside[-a,a]={inside:.6e}"
          f"|outside={outside:.6e}|frac_outside={100.0 * frac_out:.3f}%", flush=True)

    # effective radius holding 95% of the L^2 energy (symmetric around peak).
    order = np.argsort(ugrid - ugrid[ipeak])   # distance from the peak
    cum = np.cumsum(e[order])
    r95_idx = int(np.searchsorted(cum, 0.95 * total))
    span = max(abs(ugrid[order[r95_idx]]), abs(ugrid[order[r95_idx] - 1])) \
        if r95_idx > 0 else 0.0
    print(f"energy|r95_span={span:.4f}|a={a:.4f}|r95/a={span / a:.3f}", flush=True)

    # ---- round-trip self-check (F-C gate): M[phi](s) == g_3(s)? --------------------
    def mellin_phi(s):
        return complex(_trapz(np.exp(s * ugrid) * phi, ugrid))

    print("\n--- ROUND-TRIP:  M[phi](s) vs g_3(s) ---", flush=True)
    for name, ss in (("0", mpf(0)), ("1/2", mpf("0.5")), ("1", mpf(1)),
                     ("0.3+0.4i", mpf("0.3") + 1j * mpf("0.4")),
                     ("rho2", mpf(repr(BETA)) + 1j * mp.im(_mp.zetazero(2)))):
        mt = mellin_phi(complex(ss))
        gm = complex(g3(ss))
        if name in ("0", "1/2", "1"):
            # true value is exactly 0 at the nodes => report absolute residual directly
            print(f"roundtrip|s={name}|M[phi]={mt.real:.6e}+{mt.imag:.1e}j"
                  f"|g_3={gm.real:.6f}{gm.imag:+.6f}j"
                  f"|abs_resid={abs(mt):.3e}", flush=True)
        else:
            rel = abs(mt - gm) / max(abs(gm), 1e-12)
            print(f"roundtrip|s={name}|M[phi]={mt.real:.6f}+{mt.imag:.6f}j"
                  f"|g_3={gm.real:.6f}{gm.imag:+.6f}j|rel_err={rel:.3e}", flush=True)

    # ---- truncation + field #4 sign re-eval at zero #2 -----------------------------
    phi_win = np.where(inside_mask, phi, 0.0)   # hard truncate to [-a, a] (recon)

    def mellin(s):
        sc = complex(s)   # numpy exp cannot consume mpmath mpc; pipeline is float64
        return complex(_trapz(np.exp(sc * ugrid) * phi_win, ugrid))

    cutoff = max(3.0 * gamma_2, 5.0 / delta)
    gmax = min(6000.0, max(cutoff + 2.0, 120.0))
    gam = zero_cache(gmax)
    gam_np = np.array([float(g) for g in gam])
    ncov = int(np.searchsorted(gam_np, cutoff))

    # on-line masses with G = M[phi_win] (TRUNCATED object), same definition as
    # 1075/1077 which use rows_j = 2 |g(1/2 + i gamma_j)|^2.
    gline_abs = np.array([abs(mellin(mpf("0.5") + 1j * mpf(str(float(g)))))
                          for g in gam_np[:ncov]])
    rows = 2.0 * (gline_abs ** 2)              # |G|^2, mirrors 1075/1077 verbatim
    margin0 = float(np.sum(rows))
    Pj = float(rows[1])                        # j = 2 => index 1
    wall = margin0 - Pj

    G_rho = mellin(mpf(repr(BETA)) + 1j * mp.im(_mp.zetazero(2)))   # off-line zero rho_2, complex
    A = float(4.0 * (G_rho ** 2).real)                          # Re g^2, as in 1075/1077
    lever = float(4.0 * abs(G_rho) ** 2)                        # |g|^2
    fl = margin0 + A - Pj

    # triple-vanishing residual of the truncated object at {0,1/2,1}.
    tv = [abs(mellin(mpf(str(n)))) for n in (0, "0.5", 1)]
    peakG = float(np.max(gline_abs)) if len(gline_abs) else 0.0

    print("\n--- TRUNCATED object phi_win: field #4 sign at zero #2 ---", flush=True)
    print(f"trunc|margin0={margin0:.6f}|P2={Pj:.6f}|A={A:.6f}|wall={wall:.6f}"
          f"|lever={lever:.6f}|fl={fl:.6f}", flush=True)
    print(f"trunc|G(rho2)={complex(G_rho).real:.6f}{complex(G_rho).imag:+.6f}j"
          f"|detects={abs(complex(G_rho)):.4f} (must be != 0)", flush=True)
    for name, v in zip(("0", "1/2", "1"), tv):
        print(f"trunc|G({name})={v:.3e}|rel_to_peakG={v / peakG if peakG else float('nan'):.3e}",
              flush=True)
    wl = wall / lever if lever > 0 else float("inf")
    sinkpct = 100.0 * abs(fl) / lever if lever > 0 else float("nan")
    o1 = (lever >= np.exp(-2)) and (wall >= np.exp(-2))
    print(f"trunc|wall/lever={wl:.4f}|sink={sinkpct:.2f}% of lever|O(1)scale={'Y' if o1 else 'n'}",
          flush=True)

    # ---- verdict branch (operational cut; raw numbers always stand on their own) ---
    print("\n=== VERDICT BRANCH ===", flush=True)
    print(f"  frac_outside={100.0 * frac_out:.3f}%   (F-A wants <= ~5%)")
    print(f"  node residual max/peakG = {max(tv) / peakG if peakG else float('nan'):.3e}")
    print(f"  fl(truncated)={fl:.6f}  (<0 keeps field #4 sign)")
    branch = "F-A" if (frac_out <= 0.05 and max(tv) < 1e-2 * peakG and fl < 0) else \
             ("B" if not np.isfinite(frac_out) else "F-B")
    print(f"  => preliminary: {branch}   (hand-write the .md verdict from these rows)",
          flush=True)


if __name__ == "__main__":
    run()
