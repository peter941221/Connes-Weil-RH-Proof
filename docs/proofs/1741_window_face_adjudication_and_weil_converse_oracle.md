# 1741 — Window face of P2 adjudicated: the smooth triple top eigenvalue is −0.86 at the Yoshida window (four-engine verified through K = 128); the Weil converse oracle `SourceRH ⟹ window arch ≤ 0` lands on standard axioms; the 1740 arch readings were corrupted by a denominator bug

Date: 2026-09-20. Classification: ADJUDICATION LANDED + LEAN BRICK + ERRATUM
(one instrument rig `scripts/window_smooth_adjudicator_1741.py`, results
`results/1741_window_adjudicator_results.json`, log
`build-logs/1741_window_adjudicator.log`; one new Lean module
`ConnesWeilRH/Dev/C1SourceRHWeilConverse.lean` + Audit, built clean on
`[propext, Classical.choice, Quot.sound]`).  This wave executes the four-item
order from 1740: ① smooth-faithful basis adjudication of the window face of
P2, ② the Lean oracle brick for the reverse arrow, ③ the F70-with-width
threshold from the σ symbol, ④ the extension-principle scan.  No sign theorem
is proved unconditionally, `0 ≤ qw` is not claimed, and RH is not claimed.
Stop word unchanged: gate certificate.

## 0. Errata carried by this wave (all machine-verified here)

**E-A (denominator — the big one).**  `p2_ledger_rig_1740.py` evaluated every
arch path with `expm1(2y) = e^{2y} − 1` in the denominator
(`p2_ledger_rig_1740.py:143,156,333`), but the committed Lean
`archimedeanDenominator` (`Source/CCM25Concrete/SelectedWeilFormula.lean:96-104`)
is `e^y − e^{−y} = 2 sinh y`.  Since `e^{2y} − 1 = e^y (e^y − e^{−y})`,

```text
1/(e^{2y} − 1)  =  e^{−y} / (e^y − e^{−y})
```

so the 1740 integrand is the true integrand damped by `e^{−y}`.  Every 1740
arch reading is corrupted: the E2 sweep (including the headline
`lambda_triple = +0.8421` "window/rect basis FAILS"), the E3 arch/finite
sampling, the E4 band-pass positives (`+2.10/+1.39/+0.69`), and E5.
UNAFFECTED (no y-integral): the E1 σ chart (`ξ* = 6.289836`) and E3's pole
audit.  Corrected readings below; the committed Lean side was always right.

**E-B (probe class).**  1740's E5 operator `D(D+1/2)(D+1)` has Laplace roots
`s = 0, −1/2, −1` — the wrong side.  The constraint class needs vanishings at
`s = 0, +1/2, +1`; the correct operator is `P(s) = s(s−1/2)(s−1)`, i.e.
`g = h''' − 1.5 h'' + 0.5 h'`.  (1740's E5 moments reached only 9e−4.)

**E-C (constraint count).**  1740's "triple" imposed only `s ∈ {1/2, 1}`
(mass separate).  Here "triple" = all three vanishings
`∫ g e^{−sx} dx = 0` at `s ∈ {0, 1/2, 1}`.

**E-D (basis domain — found by the four-engine gate, post-run).**  The first
draft of this wave's window basis passed `2.0*x/w` as the polynomial argument
of Legendre/Chebyshev, i.e. evaluated them OUTSIDE `[−1, 1]`, where they grow
like `e^{0.96 K}`: the "basis" became edge-spike monsters (raw Gram
eigenvalues down to `−2.4e8` at K = 32; matrix/freq/yside reading
`−0.17/−0.37/−7.7` on the SAME vector at K = 64).  Fixed to `x/w`.  The span
is unchanged (affine reparametrization), so every engine-verified K ≤ 48
reading survives bit-for-bit (`lambda_triple(K=24) = −0.898813977119606`
reproduced identically); only deeper-ladder upper bounds were at risk.

## 1. The σ-symbol identity: rehabilitated and theorem-grade

With E-A fixed, the frequency-side identity closes against the y-side at
machine precision (rig V0, 7/7 exact families, worst diff `3.33e−15`):

```text
arch(F) = (log4π + γ) F(0)
          + ∫₀^∞ [e^{y/2}(F(y)+F(−y)) − 2F(0)] / (e^y − e^{−y}) dy
        = ∫ σ(2πξ) F̂(ξ) dξ,          F̂ = FT of F,
σ(ω) = log π − Re ψ(1/4 − iω/2)
```

Two hard-won fine print items: the weight is `F̂` itself, NOT `|F̂|²` (for
`F = g⋆g̃`, `F̂ = |ĝ|²` — the square is already inside); and `σ` varies on an
O(1) scale, so FFT-grid Riemann sums need zero-padding oversampling
(`Δω ≲ 0.05`), otherwise the `σ(0) = 5.372183` peak is missed (30% errors on
mass-carrying probes).  σ crosses zero at `ξ* = 6.289836` (ω* ≈ 2π), is
positive on `|ξ| < 1.001` and negative beyond, with the digamma-leaf tail
`σ(ω) ~ log(2π/|ω|) → −∞` (theorem-grade out-of-band negativity via
`Dev/C1DigammaVerticalLine.lean`).

## 2. ① The window-face adjudication (the wave's headline)

The instrument: bump × polynomial basis on `[−w, w]`, QR-orthonormalized in
sample space (rescaled to L²), the three Laplace constraint rows compressed
by null-space, and the arch quadratic form `A_ij = Re ∫ σ(2πξ) f̂_i conj(f̂_j) dξ`
built row-by-row on a 256× zero-padded FFT grid.  Acceptance gate per run:
FOUR engines must agree on the top eigenvector — the basis matrix, the
σ-side FFT integral, the y-side FFT autocorrelation, and the FFT-free
dense-quad referee.

**Verdict at the Yoshida window `w = log 2 / 2` (triple class):**

```text
  K    λ_top(triple)   four-engine spread   status
 ---   -------------   ------------------   --------
  24     −0.898814          1.1e−04          VERIFIED
  36     −0.886357          1.1e−04          VERIFIED
  48     −0.879083          1.1e−04          VERIFIED
  64     −0.872942          1.1e−04          VERIFIED
  96     −0.865924          1.1e−04          VERIFIED
 128     −0.861902          2.4e−04          VERIFIED
```

n-refinement at K = 128: `−0.861691 / −0.861902 / −0.861785` across
`n = 4096 / 8192 / 16384`.  Ladder increments decay
(`+0.0091, +0.0106, +0.0061, +0.0070, +0.0040`); the K-ladder converges to
**λ_top ≈ −0.86 < 0**.  The top of the K = 128 spectrum is well separated
(`−0.8619` vs `−1.0816` next).  Instrument ceiling: at K ≥ 160 the four
engines split again (matrix drifts to ~0, yside to a −7.7 plateau) — the
adjudication quotes K = 128 as its verified frontier.

**The window face of P2 HOLDS at the Yoshida window with margin ≈ 0.86.**
Every probe attempted on this class reads negative: the whole constrained
spectrum at every verified K, the corrected E5 D³ probes (all 8 negative,
`−1.75 … −2.63`, moments ~1e−14), three random constrained directions at
K = 24 (`−2.25 … −2.45`), and the dilation family of EXT-a (below).  The
F73 falsifier oracle — ONE smooth triple-vanishing window test with positive
arch refutes RH — remains unfired, and is now ALSO formal (§4).

Width sweep (fixed basis, K = 24, identical to 5 digits with the pre-E-D
run): the triple class stays negative through `w = 0.70` (`−0.191`) and turns
positive at `w = 1.00` (`+0.172`); the mass-only class turns positive already
at `w = 0.40` (`+0.0028`).  Bisection (rig section E6):

```text
  class    w at K=24    w at K=48    2w vs prime logs
 --------  ----------   ----------   ----------------------------------
  triple    0.845141     0.828675     log5 = 1.6094 < 2w* < 1.9459 = log7
  mass      0.398908     0.391058     log2 = 0.6931 < 2w0 < 1.0986 = log3
```

Width laws: the triple class stays arch-negative through the prime-5 window
and turns positive before prime 7 enters the autocorrelation support; the
mass-only class turns positive as soon as prime 2 enters — which is exactly
1740's F70-width-free refutation, now with the corrected denominator and a
sharp threshold.  The crossing shrinks with degree enrichment (0.8451 →
0.8287), so the honest statement is `w* ≈ 0.83 ± 0.02` for the smooth triple
class, and the Yoshida window sits DEEP inside the negative region
(`0.3466 ≪ 0.83`).

## 3. Corrected 1740 tables (what the denominator bug was hiding)

E4-redo (band-pass `g = bump · sin(2πξ₀x)` mass-zeroed, w = 3): the sign of
arch FOLLOWS the σ symbol at the carrier, point by point —

```text
  ξ₀    σ(2πξ₀)    arch/F₀ (yside)    arch/F₀ (freq)
 ----   --------   ----------------   ----------------
 0.5    +0.6976       +0.720720          +0.720718
 1.0    +0.0011       +0.005744          +0.005742
 1.5    −0.4050       −0.403058          −0.403060
 2.0    −0.6929       −0.691784          −0.691786
```

1740's "+2.10 / +1.39 / +0.69 positives" were the `e^{−y}` damping artifact,
not physics.  E5-redo (corrected D³ operator, w ∈ {0.29, log2/2}, ξ₀ ∈
{0.5, 1, 2, 3}): all eight probes negative (`−1.75 … −2.63`), Laplace moments
≤ 4.5e−14 — 1740's "smooth probes 8/8 NEGATIVE" conclusion survives the
erratum, with different values.

## 4. ② The Weil converse oracle (Lean brick)

`ConnesWeilRH/Dev/C1SourceRHWeilConverse.lean` (+ Audit) runs the two-premise
exit backwards, from committed pieces only:

```text
  SourceRH (every source zero on the critical line)
    ⟹ centeredXiCoordinate ρ purely imaginary
    ⟹ star L = −L, so star L · L = ‖L‖²  (L = laplaceAt g ·)
    ⟹ spectralTerm re = multiplicity · Complex.normSq ≥ 0   (termwise)
    ⟹ spectralWeilValue ≥ 0        (Complex.re_tsum + tsum_nonneg)
    ⟹ archimedeanTerm ≤ 0 on the window triple class
       (Gate 2 + qw_eq_neg_archimedeanTerm_of_vanishesOn_cc20Triple_
        of_rootSupport_logTwoHalf, support ⊆ [−log2/2, log2/2])
```

Main theorem:
`archimedeanTerm_nonpos_of_sourceRH_of_vanishesOn_cc20Triple_of_rootSupport_logTwoHalf`
(`Dev/C1SourceRHWeilConverse.lean:132-147`), audit
`#print axioms` = `[propext, Classical.choice, Quot.sound]`.
`SpectralSummable` is carried as the consumer's hypothesis, per the
`C1SpectralWeil` contract.  Combined with §2: the F73 falsifier oracle is now
formal BOTH ways — RH ⟹ arch ≤ 0 on the window class (this brick), and one
positive smooth triple test would refute RH (contrapositive) — while the
numerics say the class is deeply negative at the Yoshida width.

## 5. ④ Extension-principle scan (EXT-a / EXT-b)

**EXT-a (dilation).**  The Yoshida D³ probe family dilated `g_L(x) =
L^{−1/2} g(x/L)`: the quadratic form climbs toward zero but stays negative
through L = 3 (`ξ₀=1: −2.277 → −1.178; ξ₀=2: −1.861 → −0.762`).  Dilation
covariance does NOT produce a sign flip; the approach to 0⁻ is the same
"widening → 0⁺ crossing at w*" seen in the width sweep.

**EXT-b (widening price, arch + finite on the top eigenvector).**  At the
Yoshida window `finite = 0` exactly (support law: `2w = log 2` admits only
prime 2 at the boundary).  Widening:

```text
   w        λ_top(triple)   arch        finite     arch+finite
 --------   -------------   ----------  ---------  -----------
  0.3466      −0.898814     −0.898701    0.0000     −0.898701
  0.3666      −0.842533     −0.842421   −0.0005     −0.842890
  0.3966      −0.763586     −0.763476   −0.0593     −0.822791
  0.4466      −0.644320     −0.644213   −0.0757     −0.719877
  0.5466      −0.441022     −0.440922   +0.2454     −0.195531
```

Through `w + 0.20` (still short of `log 3/2 = 0.5493`, so only prime 2 is
live) the FULL P2 gate `arch + finite ≤ 0` holds on the top eigenvector; the
prime-2 term is what turns positive first (`+0.2454` at `w+0.20`).  The prime
book, not the window, is where the fight is — consistent with 1740's ledger.

## 6. New laws

* **F74 (denominator law).**  The arch y-integral weight is exactly
  `1/(e^y − e^{−y})` (committed Lean definition).  Any instrument using
  `expm1(2y)` reads the true integrand times `e^{−y}`; every sign conclusion
  drawn from it is void.  Before trusting an arch reading, check the
  denominator against `SelectedWeilFormula.lean:96-104`.
* **F75 (σ-symbol identity).**  `arch(F) = ∫ σ(2πξ) F̂(ξ) dξ` with weight
  `F̂` (not `|F̂|²`); `σ(ω) = log π − Re ψ(1/4 − iω/2)`, `σ(0) = 5.372183`,
  zero at `ξ* = 6.289836`, tail `~ log(2π/|ω|)` (digamma leaf).  Validated
  7/7 at 3.3e−15; Riemann sums need oversampling `Δω ≲ 0.05`.
* **F76 (window-face adjudication).**  On the smooth triple class at
  `w = log2/2`, `λ_top = −0.8619` (K = 128, four-engine verified, n-stable),
  ladder converging to ≈ −0.86; P2's window face holds with margin, and the
  class is a genuinely negative testing ground for the falsifier oracle.
* **F77 (instrument discipline).**  Polynomial basis arguments MUST live in
  `[-1, 1]` (E-D); acceptance = four-engine agreement (matrix / σ-side FFT /
  y-side FFT / FFT-free referee) per run; a Gram with negative eigenvalues or
  a three-way split on one vector is instrument death, not signal.  Current
  ceiling: K ≈ 128 at n = 8192.
* **F78 (width laws).**  Triple crossing `w* ≈ 0.83–0.85`
  (`log5 < 2w* < log7`), mass crossing `w₀ ≈ 0.39–0.40` (`log2 < 2w₀ <
  log3`); both shrink under degree enrichment; Yoshida sits deep inside the
  negative region.

## 7. What this wave does NOT claim

No unconditional sign theorem; `0 ≤ qw` remains the open gate; the prime
book on the full class is untouched; RH is not claimed.  The adjudication is
numerical evidence about one class at one width, with the formal converse
oracle making that evidence RH-relevant in both directions.

## 8. Next steps

1. **Push the instrument ceiling** (F77): sparse/structured basis or
   double-precision-long QR to reach K ≥ 256, closing the gap between the
   verified frontier (−0.8619) and the extrapolated limit (≈ −0.86), and
   re-bisecting w* at K = 96+.
2. **Formalize the σ-symbol identity** (F75) as a Lean lemma against the
   committed `archimedeanNumerator/Denominator` — the y-side/frequency-side
   bridge would make the numerics quotable inside the formal exit.
3. **Prime-2/3 pricing on the widening path** (EXT-b): extend the arch+finite
   ledger to `w ∈ [0.55, 0.83]` where primes 3 and 5 enter, locating where
   the full gate `arch + finite ≤ 0` first fails on the top eigenvector —
   that failure point is the honest price of the window route.
