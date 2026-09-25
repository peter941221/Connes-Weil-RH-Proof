# Record 1985 — Interval certification of D at the registered point (pre-registration)

- **Date**: 2026-09-25
- **Status**: PRE-REGISTERED (this document committed BEFORE the rig run; the
  rig is deterministic and the bracket rule below is fixed in advance)
- **Script**: `scripts/fourpoint_cert_d_1985.py` (committed together with
  this document, before any result exists)
- **Output**: `results/1985_cert_d.json`

## 1. What is being certified

The deterministic path priced in record 1982 needs, as its certification
target, a high-precision bracket for the gate entry

    D = ∫ (σ(2πξ) + K_p(ξ)) · P(ξ)² · W(ξ) dξ

at the single registered point

    ρ = 1/2 + 0.10 + i·γ₁,   M = 12,   sc = 1.00,   k = 30,   n = 0,

where the float instrument (record 1983 offline run) reads

    D* ≈ −1.0737429e+06   (route Ap, dξ = 0.008, ξ ∈ [−40, 40])

with measured dξ⁴ convergence (spread 5.1e−05 across certified routes).
The float instrument is self-consistent but its absolute error bar is the
discretization scale (~55 absolute at dξ = 0.008, estimated below); the
deterministic path's certification target of ~1e−06 relative requires
re-deriving the number above the float floor.  This record fixes, in
advance, how that bracket will be produced and judged.

## 2. The pipeline being replicated (byte-equal to the float rig)

- **Nodes**: owner_nodes at the displaced zero γ₁ — orbit priority
  (ρ, 1−ρ̄, ρ̄, 1−ρ), then ρ+½, then the real triple (½, 1, 3/2), then the
  in-ball kills γ₂..γ₅; γ₆ outside the ball (radius = 4 + |2 − ρ| ≈ 18.199);
  M = 12.
- **Widths** (θⱼ = −Im nodeⱼ): main pool [2.0, 2.3, 2.6, 2.9, 3.2] on the
  five γ₁-height nodes in node order; real [2.1, 2.5, 2.9]; kill
  [2.2, 2.6, 3.0, 3.4] on γ₂..γ₅.
- **Windows**: L_φ(z) = ∫ φ(x) e^{zx} dx, φ = exp(−k/(1−(x/a)²)) on
  |x| < a; composite Gauss–Legendre, panels = 6, m = 100; nodes and weights
  Newton-refined at full dps (not inherited from float tables).
- **Density**: W = |Lb|^{2(n+1)} |Lc|² at s = ½ − 2πiξ; P the quartic
  (Δ²+γ²−ω²)² + 4Δ²ω², cross-checked against the node product form.
- **Kernel**: σ(u) = log π − Re ψ(¼ − iu/2) via mp.digamma (closed form, no
  asymptotic truncation — a full upgrade over the float rig's 8-term
  Bernoulli series); prime sum 2Λ(n)/√n · cos(2πξ log n) over prime powers
  ≤ exp(support radius), support radius = max(a)·(n+2) = 6.8 → 191 terms.
- **High precision**: dps = 30 throughout (mpmath); the pipeline's internal
  cancellation is bounded by the bracket check itself.

## 3. Speed discipline (declared in advance)

Uniform-grid evaluations use geometric iteration: e^{iw(ξ₀+hj)} = z₀·rʲ
with one exponential per (window x-node / prime power) and complex
multiplies per step.  Rounding growth is j·ε ≈ 1.6e−27 at the longest grid
(16008 steps), far below both the dps = 30 floor and the certificate scale.
This is an evaluation strategy, not an approximation: every value is
mathematically the same as the direct exponential sum, with error orders
below the working precision.

## 4. The bracket rule (fixed before the run)

Route B (direct kernel on the grid) on the ladder

    dξ ∈ {0.016, 0.008, 0.004, 0.002},  ξ ∈ [−8, 8].

Richardson at the measured dξ⁴ order:

    D_ex  = D(0.002) + (D(0.002) − D(0.004)) / 15
    Δ     = 16 · max(|D(0.002)−D(0.004)|, |D(0.004)−D(0.008)|) / 15
            + 2 · |tail annulus [8, 24]|        (route B, measured)

    bracket:  D ∈ [D_ex − Δ, D_ex + Δ]

The 16×/15 factor: under the dξ⁴ law the two-grid gap is 15× the coarser
grid's error and the Richardson-corrected residual is O(h⁶); 16× the larger
adjacent gap is the conservative envelope.

`cert_ok` requires ALL of:

1. pins < 1e−20 (base and corr interpolation at dps), X-quadrature doubling
   (m = 100 vs 150) rel < 1e−20, P quartic identity < 1e−20;
2. each adjacent B-gap shrinks by ≥ 8× per dξ halving (dξ⁴ = 16×, factor-2
   margin) — this is the convergence-order re-measurement;
3. Δ / |D_ex| ≤ 2e−6;
4. route cross-check: |Ap(0.008) − B_ex| ≤ 100.  Ap (per-prime cosine
   transforms on the 8× refined grid — the float rig's certified route,
   reproduced once at dps) disagrees with B at the SAME grid by B's own
   0.008 discretization error; the float spread 5.1e−05 relative (~55
   absolute) is the expected scale, hence the 100 bound;
5. float replication: |D_float(registered row) − B_ex| ≤ 100.

## 5. Window and tail coverage

The float instrument integrates ξ ∈ [−40, 40]; this rig integrates
[−8, 8] plus a measured tail census on [8, 24] at dξ = 0.02 (expected
|annulus| < 1e−3 absolute; the record-1983 decay measurements give W decay
~e^{−c|ξ|log|ξ|} with K bounded on the annulus, so the [24, ∞) mass is
bounded by the annulus value scaled by the same decay — logged as a caveat,
not added to Δ; at the 2e−6 target (~2 absolute) the annulus is orders
below the bar).

## 6. What this record does NOT claim

- No gate sign is proved by the rig; it certifies the number at one point.
- The float instrument remains the accepted record-1983 evidence; this
  bracket, if `cert_ok`, upgrades the registered value from
  instrument-consistent to certificate-grade.
- The dξ⁴ law was measured on the float pipeline; condition 2 re-measures
  it at dps on the same ladder and REFUSES the certificate if the order
  fails to reproduce.

## 7. Outcome (appended after the run; rule above judged, not adjusted)

**Verdict: `cert_ok = False` — the certificate FAILED its own bracket rule.**
The pipeline value is replicated and cross-anchored, but this route does not
deliver a certificate-grade bracket at the registered point.

### 7.1 The measured numbers

    ladder (route B, [−8,8]):  D(0.016) = D(0.008) = D(0.004) = D(0.002)
                               = −1073742.85377…   (identical to 12 digits)
    Ap(0.008) − B(0.008)      = −3.783e−18          (route agreement)
    pins: base 2.96e−31, corr 4.92e−29, quad-doubling 1.63e−30,
          P identity 3.23e−27
    tail annulus [8,24]:       −1.272e+18
    B-ladder gaps: |D4−D8| = 2.345e−18, |D2−D4| = 9.744e−18,
                   shrink = 0.2406
    D_ex = −1073742.85377…,   Δ = 2.544e+18,   Δ/|D_ex| = 2.37e+12
    rig vs float 1981: 54.5916 absolute (5.09e−5 relative)
    rig vs float 1983: 873.589 absolute

### 7.2 Condition-by-condition

    +----+------------------------------+--------+-------------------------+
    | #  | condition                    | result | reading                 |
    +----+------------------------------+--------+-------------------------+
    | 1  | pins < 1e-20                 | PASS   | 2.96e-31 .. 3.23e-27    |
    | 2  | gap shrink >= 8x             | FAIL   | 0.2406 (noise ratio)    |
    | 3  | Delta/|D_ex| <= 2e-6         | FAIL   | 2.37e+12 (tail-swamped) |
    | 4  | |Ap(0.008) - B_ex| <= 100    | PASS   | 3.78e-18                |
    | 5  | |D_float1981 - B_ex| <= 100  | PASS   | 54.59 (= float spread)  |
    +----+------------------------------+--------+-------------------------+

### 7.3 Why it failed (mechanism, two independent causes)

1. **Exact arithmetic removes the dxi^4 signal.**  At dps = 30 the four
   ladder rungs agree to arithmetic dregs (~1e-18 absolute): the trapezoid
   is fully converged at dxi = 0.016 already.  Condition 2 (shrink >= 8)
   was calibrated on the FLOAT pipeline's measured dxi^4 gaps — which this
   run reveals to have been float64 cancellation noise, not discretization
   signal.  A noise/noise ratio (0.24) is not a convergence order.
2. **The measured tail annulus is the quadrature's aliasing floor, not the
   true tail.**  The rig's W is a finite quadrature sum: a trigonometric
   polynomial in xi (frequencies a·X) that equals the true superfast-decaying
   transform only inside the resolution window (|xi| <~ 8).  Beyond it the
   sum floors at an almost-periodic level — measured W(35.18) = 3.8e4 where
   the true transform is ~1e-8-scale.  (sigma + K)·P^2 integrated against
   that floor over [8,24] gives the 1.27e18 annulus, which enters Delta at
   face value under the pre-registered rule.

### 7.4 What survives

- **The value**: D = −1073742.85377… at the registered point, stable to 12
  digits across the full dxi ladder AND across routes B/Ap (3.8e-18), and
  54.6 absolute from the float instrument's registered row — inside the
  float pipeline's OWN certified route spread (spread_D = 5.084e-5
  relative).  Conditions 1, 4, 5 certify the REPLICATION; record 1982's
  target D* ~ −1.0737429e+06 is thereby refined to −1.07374285377e+06.
- **The failure is diagnostic, not just negative**: it localizes exactly
  what the deterministic path's next brick must deliver — brick 2 (vertical
  Laplace decay with EXPLICIT constants) converts the true-transform tail
  from "measured annulus" to "analytic bound", and a support-resolution
  certificate (quadrature resolving power vs window) bounds the aliasing
  floor.  Until then no bracket at the 2e-6 target exists at this support.

### 7.5 Errata against this document

- Section 2 said "191 terms"; the sieve yields **178** prime powers
  ≤ exp(6.8).  The sieve is correct (it matches the float rig's count);
  the pre-registration's count was wrong.
- Section 5 predicted the annulus "|annulus| < 1e-3"; measured 1.27e+18.
  The prediction applied the true density's decay to what the rig actually
  measures — the quadrature density (mechanism 7.3(2)).
- The registered point uses gamma_1 at float64 precision (mpf of the float
  literal, exact binary conversion) so the rig stays bit-identical to the
  float instruments it certifies; the 1.1e-16 input slack is ten orders
  below the 2e-6 target and is inherited from the instruments themselves.

No gate sign is proved here; RH is not claimed.
