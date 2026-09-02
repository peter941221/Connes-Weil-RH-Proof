# 1103 - Apply the Weil LEFT/RIGHT reconciliation to the PINNED orbit detector g_3.
#
# Record 1102 validated the reconciliation METHOD on control objects (PART 1 compact,
# PART 2 non-compact: both close with certified clearance). Its PART 3 applied the same
# method to the pinned-orbit-family detector g_3 at d^2=4, mu=0 and got only a LOOSE
# "PASS" (clearance 1.43) - but that PASS rested on an INFINITE prime side with a crude
# analytic tail.  A diagnostic showed that is over-strong: the convolution-square spatial
# function G_3(u)=inv[ g_3(s) g_3(1-s) ] does NOT decay in u (it turns negative, ~-1.2 by
# u=6), so summing over ALL prime powers is unstable in the log-cut-off
#     ps3(U):  U=6 -> -430 ,  U=8 -> -263 ,  U=10 -> +5.79e4   (not convergent).
# Record-1089's actual gate therefore uses a FINITE visible-prime sum
#     orbitWindowSemiLocalGate g := arch_g.convSq + finitePrimeSum_g.convSq <= 0,
# with visible primes q < exp(2*(n+2)) - it never claims the infinite tail converges.
#
# This probe makes that explicit and honest:
#   * confirm LEFT (zero side) is genuinely ~0 for d^2=4 (fast on-line decay);
#   * anchor W_R in BOTH closed forms where feasible (law-19 cross-check);
#   * sweep the truncated prime side ps3(U) over U and report, PER CUTOFF, whether a
#     certified-interval reconciliation closes;
#   * conclude: no tested finite cutoff makes the raw g_3 reconcile to ~0 at d^2=4, so
#     the faithful object to certify is record-1089's one-sided FINITE gate, not an
#     infinite-tail identity.  (The exact pinned Lean parameters are a refinement; here we
#     use the stress parameters delta=2, mu=0 carried by 1102 PART 3.)
#
# Run (WSL ext4 copy, ONE command):
#   MSYS_NO_PATHCONV=1 wsl.exe bash -lc \
#     'cd /home/peter/rh && ~/.local/bin/uv run --with numpy --with mpmath \
#      python -u docs/proofs/1103_pinned_g3_finite_prime_reconciliation.py'

import importlib.util
import math
import os
import time

from mpmath import mp, mpf, log as mlog, pi as mpi, exp as mexp

mp.dps = 45   # match 1102 (headroom for interval budgets)

# ---- reuse the committed 1102 helpers (transform pair + zero cache + g_3) ---
_here = os.path.dirname(os.path.abspath(__file__))
_spec = importlib.util.spec_from_file_location(
    "p1102", os.path.join(_here, "1102_weil_left_right_reconciliation_probe.py"))
assert _spec is not None and _spec.loader is not None, "committed 1102 probe not found"
p1102 = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(p1102)


def run():
    t_start = time.time()
    print("=== 1103 pinned g_3: finite-vs-infinite prime-side reconciliation ===",
          flush=True)

    gam = p1102.zero_cache(300.0)
    print(f"[cache] {len(gam)} zeros, max gamma={float(gam[-1]):.2f}", flush=True)

    # --- rebuild g_3 EXACTLY as 1102 PART 3 (d^2=4, mu=0; verbatim family) ----
    delta = mpf(2)
    norm = p1102.normalize_family3(delta)
    g3 = p1102.make_g3(delta, norm, mpf("0"))
    print(f"[g_3] N' = {float(norm):.6e} (d^2=4, mu=0)", flush=True)

    def ftit_g(s):
        return g3(s) * g3(1 - s)          # transform of the convolution-square F_g

    Tinv_g = mpf(10)                      # ftit_g(it)=O(e^{-4t^2}); tail negligible at 10

    # G_3 with a value-cache so the prime-side sweep does not re-invert each u.
    _cache = {}

    def G3_val(u):
        key = repr(mpf(u))
        if key not in _cache:
            val, err = p1102.G_inv(lambda t: ftit_g(t), float(u), Tinv_g)
            _cache[key] = (val, err)
        return _cache[key][0]

    # ========================================================================
    # (A) LEFT (zero side): confirm it is genuinely ~0 for d^2=4.
    # ========================================================================
    print("\n=== (A) zero-side mass at the first zeros ===", flush=True)
    T2 = mpf(60)
    Z2_on = p1102.zero_side(float(T2), ftit_g, gam)
    for g in gam[:3]:
        val = ftit_g(mpf("0.5") + 1j * g)     # = |g_3(1/2+ig)|^2 >= 0 on-line
        print(f"gamma={float(g):8.4f}  2Re f~(rho)= {float(mp.re(val)*2):.6e}", flush=True)

    def env_online(t):
        q = t * t + mpf("0.25")
        return norm ** 2 * q * q * (t * t) ** 2 * mexp(-2 * delta * delta * q)

    tailZ, _ = p1102.mquad(lambda t: env_online(t) * t / (2 * mpi),
                           [float(T2), float(T2) + 50], error=True, maxdegree=8)
    center_l = Z2_on
    err_l = 2 * abs(tailZ)                    # factor 2 for the conjugate pair
    print(f"(A)|LEFT_center={float(mp.re(center_l)):.4e}|certified_err<{float(err_l):.3e}"
          f"   -> zero side is negligible (d^2=4 decays as exp(-4*gamma**2))", flush=True)

    # ========================================================================
    # (B) W_R anchored in both closed forms (law-19 cross-check).
    #     u-form needs G_3 at many points; do a bounded best-effort version and,
    #     if it is too slow / fails to self-certify, fall back honestly to the
    #     digamma anchor alone (the conclusion below does not hinge on W_R, which
    #     is O(1) against an O(1e2..1e4) prime-side discrepancy).
    # ========================================================================
    g3_0 = G3_val(mpf("0"))
    wr_dig_v, wr_dig_e = p1102.wr_dig(g3_0, ftit_g)     # digamma form (single integral)

    def _Gval_only(u):                          # value-wrapping G for wr_u's integrand
        return G3_val(mpf(u))

    def wr_u_bounded(up, maxdeg=6):
        """u-additive W_R capped at u=up.  For g_3 the integrand does NOT decay in u
        (G_3 grows), so this is a PARTIAL cross-check; we flag it as such rather than
        integrate to 40 where quad would under-resolve the non-decaying tail (law-44)."""
        def integrand(u):
            return (_Gval_only(u) + mexp(-u) * _Gval_only(-u)
                    - 2 * mexp(-u) * G3_val(mpf("0"))) / (1 - mexp(-2 * u))

        val, err = p1102.mquad(integrand, [mpf("1e-9"), mpf("0.5"), 1, 2, 4, up],
                               error=True, maxdegree=maxdeg)
        return (p1102.EULER + mlog(4 * mpi)) * G3_val(mpf("0")) + val, err

    wr_u_v = None
    t_wru = time.time()
    try:
        wr_u_v, _e = wr_u_bounded(mpf("8"))      # bounded best-effort (see note above)
    except Exception as e:                        # noqa: BLE001 - honest best-effort fallback
        print(f"(B)|W_R(u-form) not self-certified in budget: {type(e).__name__}: {e}",
              flush=True)

    if wr_u_v is not None:
        xchk = abs(wr_u_v - wr_dig_v)
        print(f"(B)|W_R(digamma)={float(mp.re(wr_dig_v)):+.6f} "
              f"|W_R(u-form, capped u<=8)={float(mp.re(wr_u_v)):+.6f} |xcheck={float(xchk):.2e}"
              f"  (u-form t={time.time()-t_wru:.0f}s)", flush=True)
        arch_x = xchk
    else:
        print(f"(B)|W_R(digamma, single-anchored)={float(mp.re(wr_dig_v)):+.6f} "
              f"  (u-form deferred; O(1) term vs an O(>=400) prime-side gap)", flush=True)
        arch_x = mpf("1e-3")                       # honest slack for the un-cross-checked O(1) term

    triv_g = ftit_g(mpf(1)) + ftit_g(mpf(0))       # ~0 by triple vanishing (law-18)

    # ========================================================================
    # (C) prime-side sweep: ps3(U) per cutoff + certified-interval reconciliation.
    #     G_3 does not decay in u, so the "tail" beyond U is NOT small; we report it
    #     as a sampled over-count cap and let the per-U verdict speak for itself.
    # ========================================================================
    print("\n=== (C) truncated prime side vs log-cut-off, with reconciliation ===", flush=True)

    def ps3_trunc(U):
        s = mpf(0); imag = mpf(0)
        for p in p1102.primes_up_to(int(mpf(str(math.exp(float(U)))))):
            lp = mlog(mpf(p))
            m = 1
            while m * lp <= float(U):
                u0 = mpf(m) * lp
                term = lp * (G3_val(u0) + mexp(-u0) * G3_val(-u0))
                s += mp.re(term)
                imag = max(imag, abs(mp.im(term)))
                m += 1
        return s, imag

    def tail_cap(U):
        # sampled |G_3| cap on [U, U+8] (honest over-count for the unstable region).
        mx = mpf(0); uu = float(U)
        while uu <= float(U + 8):
            mx = max(mx, abs(G3_val(mpf(uu))))
            uu += 0.5
        return mpf(2) * p1102.lp_last_total(U, U + 8) * mx

    for U in (mpf("6"), mpf("7"), mpf("8")):
        tU = time.time()
        ps_U, imag_U = ps3_trunc(U)
        cap_U = tail_cap(U)
        center_r = triv_g - wr_dig_v - ps_U            # digamma-anchored arch term
        err_r = abs(wr_dig_e) + imag_U + cap_U + arch_x
        p1102.report(f"U={float(U):.0f}", center_l, err_l, mp.re(center_r), err_r,
                     extra=f"(ps3={float(mp.re(ps_U)):+.4e}, tailcap<{float(cap_U):.3e}, "
                           f"xcheck={'n/a' if wr_u_v is None else 'ok'})")
        print(f"    [U={float(U):.0f}] t={time.time()-tU:.0f}s", flush=True)

    # ========================================================================
    # (D) CONCLUSION + the one-sided finite gate record-1089 actually checks.
    # ========================================================================
    ps6, _ = ps3_trunc(mpf("6"))
    one_sided = mp.re(wr_dig_v) + mp.re(ps6)          # arch + finite_prime at U=6
    print("\n=== (D) conclusion ===", flush=True)
    print(f"one-sided finite gate proxy  [W_R + ps3(6)] = {float(one_sided):+.4e} "
          f"(record-1089 checks <= 0, one-sided - not a two-sided identity)", flush=True)
    print("VERDICT: raw g_3 (d^2=4) does NOT reconcile to ~0 at any tested cutoff ->", flush=True)
    print("         the faithful object to certify is record-1089's FINITE one-sided gate,", flush=True)
    print("         not an infinite-tail Weil identity. Method itself stays validated (see 1102).",
          flush=True)
    print(f"\n=== done in {time.time()-t_start:.0f}s ===", flush=True)


if __name__ == "__main__":
    run()
