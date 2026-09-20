# 1735 — Three formal leaves of the 1734 page: two-IBP decay, digamma line, kernel readback

Date: 2026-09-20. Classification: FORMAL LEAVES LANDED AND AUDITED (standard
axioms only). This wave executes the formal program announced in record 1734
section 7: the oscillatory two-integration-by-parts decay face, the digamma
vertical-line growth face, and the kernel readback are now machine-checked
Lean theorems, each with a paired axiom audit. No carrier object is
constructed, no sign is touched, `0 ≤ qw` is not claimed, and RH is not
claimed. Stop word unchanged: gate certificate.

## 1. The two-IBP leaf (`Dev/C1G8R3AnnularTwoIBP.lean`)

`abs_osci_integral_le_of_C2` — for `θ, θ', θ'' : ℝ → ℂ` integrable with the
two derivative relations and `s ≠ 0`,

```text
  ‖∫ ξ, θ ξ * exp(-2πi ξ s)‖ ≤ (∫ ξ, ‖θ'' ξ‖) / (4 π² s²).
```

Mechanism: Mathlib's whole-line IBP
`integral_mul_deriv_eq_deriv_mul_of_integrable` applied twice (the
oscillatory factor has modulus one and derivative `-2πis·E`, so no boundary
terms), then `‖c·c‖ = 4π²s²` and `norm_integral_le_integral_norm`.

`annular_v_tail_lintegral_le_of_two_ibp` — composition with the committed
1734 weighted-moment leaf, giving exactly the record-1734 section-4
constant:

```text
  ∫⁻ s in Ici X, ofReal (s * ‖v s‖²) ≤ ofReal (‖θ''‖₁² / (32 π⁴ X²)).
```

Audit: `[propext, Classical.choice, Quot.sound]` for both
(`Dev/C1G8R3AnnularTwoIBPAudit.lean`; clean rounds 5-6 of
`build-logs/twoibp-round6.log` from the prior wave and the audit build
`build-logs/audit-twolibp-digamma.log`, 3542 jobs).

## 2. The digamma vertical-line leaf (`Dev/C1DigammaVerticalLine.lean`)

`abs_digamma_le_of_re_ge_quarter` — for `1/4 ≤ w.re`,

```text
  ‖digamma w‖ ≤ (‖digamma (1/2)‖ + 4 + 6/5) + (12/5) * ‖w‖.
```

This is the formal Lemma-B face of record 1734 section 2 (LINEAR growth, no
Stirling). Mechanism, all elementary:

1. `digamma w = digamma (w+1) - w⁻¹` (the recurrence never fails on the
   closed half-plane),
2. the committed reciprocal-series anchor
   `Source.C1XiCenterTwoGamma.halfAnchorGaussReciprocalSeries_eq_digamma_sub_half`
   at `w+1`,
3. per-term pricing `‖(n+1/2)⁻¹ - (n+w+1)⁻¹‖ ≤ ((n+1/2)⁻¹ - (n+3/2)⁻¹) ·
   (6/5) · ‖w + 1/2‖` (the `(6/5)` slack is `n ≥ 0`: `(5/6)(n+3/2) ≤ n+5/4`),
4. the telescoping total `2` proved directly
   (`real_scaled_halfAnchorShift_hasSum`, partial sums over `Finset.range`),
5. `‖w⁻¹‖ ≤ 4` and `‖w + 1/2‖ ≤ ‖w‖ + 1/2` close the constant.

Audit: standard axioms (`Dev/C1DigammaVerticalLineAudit.lean`; five build
rounds, final `build-logs/digamma-line-round5.log`, 3538 jobs, zero errors;
remaining style warnings fixed and re-verified in the audit build).

## 3. The kernel-readback leaf (`Dev/C1G8R3KernelReadback.lean`)

`sourceKernelReadback_ae` — for `g : CompactLogTest` and Schwartz `u`, the
`L2` representative of the Plancherel-defined root convolution is, almost
everywhere, the honest kernel-pairing integral:

```text
  (cc20GlobalLogConvolution g.involution.test (u.toLp 2)) =ᵐ[volume]
    (fun t => ∫ x, u x * conj (g.test (x - t))).
```

This is the record-1734 section-3 face: `(C u)(t) = ⟨u, k_t⟩` with
`k_t = conj (test (t - ·))`; at `t = 0` the kernel is the committed
`k_0 = conj (test (-·))`. Assembly from three committed inputs:

1. `cc20GlobalLogConvolution_toLp` (Schwartz-face bridge, landed upstream),
2. Mathlib's `SchwartzMap.coeFn_toLp` (representative lemma; NOTE the `μ`
   default fails to synthesize through the `cc20GlobalLogCrossingL2`
   abbreviation — pass `(volume : Measure ℝ)` explicitly),
3. `fullBoundaryIntegral_eq_globalConvolutionCore` (the in-house pointwise
   kernel-integral identity; this is where the `mul ℝ ℂ` vs `mul ℂ ℂ`
   bilinearity gap of Mathlib's `SchwartzMap.convolution_apply` — which is
   hardcoded `ℂ`-linear `B` — is already bridged).

Audit: `[propext, Classical.choice, Quot.sound]`
(`Dev/C1G8R3KernelReadbackAudit.lean`; four build rounds, final
`build-logs/kernel-readback-round4.log`, 3155 jobs).

## 4. Rig C: the B(N) calibration (`scripts/annular_bN_calibration_1735.py`)

Result: GOOD — all four acceptance verdicts green
(`results/annular_bN_calibration_1735_results.json`).

```text
  verdict_control_exact_zero       true   (bump control reads 1.21e-14,
                                           the quadrature floor)
  verdict_control_spectral_pipeline true  (spectral vs adaptive-quad
                                           ||theta0''||_1: diff 1.26e-7)
  verdict_control_closed_form      true   (Gaussian control vs
                                           exp(-2 pi X^2)/(4 pi):
                                           max diff 3.1e-14)
  verdict_envelopes_hold           true   (real symbol 7/7 rows and
                                           k0 5/5 rows measured <= envelope)
```

Calibrated constants (Gaussian test, unitary Fourier convention):
`‖θ''‖₁ = 124.4560` for the real Γ-ratio symbol;
`C_k = 1.6744`.

New law **F59 (envelope-slack law)**: for the fixed Gaussian test the
real-symbol tail `B_v(X)` decays SUPER-polynomially (log-log slope −7.72 on
`X ∈ [4,16]`, ratios to the `‖θ''‖₁²/(32π⁴X²)` envelope collapsing to
1.3e-4 at `X = 16`). Mechanism (hand-derived, F27): `θ = m · conj(Fh)` with
`|m| = 1` and polynomially-bounded derivatives is Schwartz whenever the
test is, so `v = F⁻¹θ` is Schwartz and the `X⁻²` envelope is the
WORST-CASE over the `W^{2,1}` class, not the decay law of any fixed
Schwartz test. The envelope is validated as an upper bound; its sharpness
would require a `θ` at the class boundary, which the annular assembly does
not need.

Erratum (rig discipline): two successive "exact-answer" references for
`‖θ₀''‖₁` were wrong before the probe settled it — first an unsplit
absolute value, then a mis-derived constant (`−2π²` for the correct `−2π`:
`θ₀'' = (4π²ξ² − 2π)e^{−πξ²}`, `‖θ₀''‖₁ = 2π · 2 · e^{−1/2}/√(2π) =
6.0814…`). The spectral pipeline was correct all along; both errors were in
the reference. Lesson: an exact-answer reference must be derived
independently of the pipeline it is meant to grade.

## 5. Remaining formal work (unchanged items, now precisely priced)

* **θ-W^{2,1} page**: Lemmas A (absolute convergence) and C (uniform `ψ' ≤
  20`) in Lean; B is landed (section 2 above).  The termwise bound needs the
  Weierstrass M-test face `Σ (n+1/4)⁻² < ∞`.
* **Translation-tail integral identities** instantiating the wing integrals
  into the 1723 consumer shape.
* **1723-consumer wiring** (blocked on the θ-page).
* The v-representative face for NON-Schwartz θ: Mathlib has no Young
  inequality (`L¹ · L² → L²`) and no convolution-MemLp lemma, and
  `Lp.fourierTransformₗᵢ` is an `extendOfIsometry` with no a.e. integral
  bridge — the density/subsequence argument is a self-contained next brick
  if the consumer ever needs pointwise `v` outside the Schwartz class.

## 6. Boundary discipline

No carrier object, no gate, no sign. `0 ≤ qw` untouched. The sign face
lives on the map-047 two-premise exit
(`healthy_spectral_nonneg_sourceRH_of_yoshida_detector`). RH not claimed.
