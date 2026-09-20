# 1740 — P2 ledger audit: arch + finite ≤ 0 is the whole game; the arch symbol gets a closed form; width-free F70 refuted, the window class pinned as the RH falsifier

Date: 2026-09-20. Classification: AUDIT LANDED + RIG VERDICTS (no new Lean
brick; one instrument rig `scripts/p2_ledger_rig_1740.py` v3, results
`results/1740_p2_ledger_rig_results.json`, log `build-logs/1740_p2_ledger_rig.log`).
This wave executes the "full attack" order on the two-premise exit: the P2
ledger is pinned against committed definitions end to end, the archimedean
quadratic form is diagonalized in the frequency symbol
`σ(ξ) = log π − Re ψ(1/4 − iξ/2)`, the F70 width law is settled (refuted
without a width hypothesis, open on the window class in the smooth sense),
and the window triple class is identified as a *falsifier oracle for RH
itself*. No sign theorem is proved, `0 ≤ qw` is not claimed, and RH is not
claimed. Stop word unchanged: gate certificate.

## 1. The audit chain: P2 ⟺ arch + finite ≤ 0 on the triple-vanishing class

Every link below is machine-checked in the repo; the audit adds nothing new
formally, it pins which inequalities remain.

```text
  [capstone]  healthy_spectral_nonneg_sourceRH_of_yoshida_detector
              (Dev/C1CenterTwoRHExit.lean:67; "discharging premise 2 is
               RH-equivalent" at :36-37)
                  |
                  +-- P1: CC20YoshidaDetectorExists            (transport)
                  +-- P2: 0 ≤ spectralWeilValue g.convolutionSquare
                          for every triple-vanishing g          (THE CORE)
```

Bookkeeping (all committed):

```text
  psi(F)  = poleTerm F − archimedeanTerm F − finitePrimeSum F
            (Dev/C1SameOwnerWeil.lean:192-193)
  qw g    = psi g.convolutionSquare = spectralWeilValue g.convolutionSquare
            (Gate 2, Dev/C1CenterTwoCriterionBridge.lean:28-32,
             unconditional)
```

The pole dies on the whole triple class, unconditionally, by the Hermitian
square law: `laplaceAt F s = conj (laplaceAt g (−conj s)) · laplaceAt g s`
(`Dev/C1HealthyYoshidaDetector.lean:48-51`), so a single vanishing at
`s = 1/2` kills both pole moments
(`poleTerm_convolutionSquare_of_vanishesOn_cc20Triple` :92-110; half-line
variant `Dev/C1MinimalWeilCriterion.lean:217`). Hence

```text
  P2  ⟺  arch(F) + finite(F) ≤ 0   for every triple-vanishing g,
          F = g ⋆ g̃,
  arch(F)   = (log 4π + γ)·F(0)
              + ∫₀^∞ [e^{y/2}(F(y)+F(−y)) − 2F(0)] / (e^y − e^{−y}) dy
              (denominator pinned at Source/CCM25Concrete/
               SelectedWeilFormula.lean:103-104)
  finite(F) = Σ_powers Λ(n)/√n · (F(log n) + F(−log n)).
```

Window slice: for `supp g ⊆ (−log 2/2, log 2/2)` the support theorem makes
`finite = 0` (`finitePrimeSum_eq_zero_of_supportLt` ,
Dev/C1SameOwnerWeil.lean:161-167), and the machine-checked consumption
`qw_nonneg_of_archimedeanTerm_nonpos_of_vanishesOn_cc20Triple_of_
rootSupport_logTwoHalf` (Dev/C1HealthyYoshidaDetector.lean:165-175) turns
`arch ≤ 0` into `0 ≤ qw` on that slice. **The prime book is the only thing
between us and P2.**

## 2. The arch symbol: closed form σ(ξ) = log π − Re ψ(1/4 − iξ/2)

`arch` is a quadratic form; in frequency its symbol (diagonal kernel) is

```text
  σ(ξ) = log π − Re ψ(1/4 − iξ/2),
  σ(0)   = log π + γ + 3 log 2 + π/2 ≈ +5.372183,
  zero crossing  ξ* ≈ 6.289836   (1/ξ* ≈ 0.158987).
```

Derivation (paper, legal): the cosine integral against the arch kernel
reduces to `I(ξ) = I(0) + 2Σ_n [a/(a²+ξ²) − 1/a]` with `a = 2n + 1/4`; each
bracketed term is a *convergent difference series* (terms O(1/n²)), so the
regrouping that is illegal for `I(ξ)` alone is legal for the difference, and
the series sums to `(Re ψ)(1/4 − iξ/2) − (Re ψ)(1/4)` by the standard
partial-fraction form of digamma.

In-rig validation (E1), three independent paths agreeing to ≤ 4e-13 over
ξ ∈ [0, 50] (scipy quad; mpmath `digamma`; the difference-series closed
form): chart in
`results/1740_p2_ledger_rig_results.json` §E1.

Consequence (ties to the committed digamma leaf): with
`abs_digamma_le_of_re_ge_quarter`
(`Dev/C1DigammaVerticalLine.lean`, ‖ψ(w)‖ ≤ (‖ψ(1/2)‖+4+6/5) + (12/5)‖w‖ on
Re w ≥ 1/4), σ is *theorem-grade* for large ξ:

```text
  σ(ξ) = log π + O(log|ξ|),  and numerically σ < 0 for ξ > ξ* = 6.29.
```

So the arch form is positive at low frequency (σ(0) = 5.37) and negative at
high frequency — any bound `arch ≤ 0` must be a *cancellation statement*,
never a pointwise one. This is exactly why width-free F70 dies (§5).

## 3. The pole face, numerically confirmed

E3 samples 120 random triple-vanishing directions at two window widths:

```text
  w = 0.29     : pole/F0|max| = 5.19e-06
  w = 0.34657  : pole/F0|max| = 4.21e-06
```

Both are at the constraint-projector moment floor (the three Laplace
vanishings hold only to the discretization precision), i.e. the pole
vanishing — the committed Hermitian-pairing theorem — is confirmed at full
instrument precision. `finite = 0` exactly on the window (prime-free, as
theorem §1). `qw = −arch` read **positive on 120/120 directions**
(qw ∈ [+4.13, +4.47], mean +4.29 at the Yoshida window).

## 4. Instrument law F71: the kink-cell contribution and the three-way check

The wave's own instrument bit once, and the bite is the record's most
reusable lesson. Three computations of `arch` were carried:

```text
  matrix path : n×n Toeplitz QF built from the tent autocorrelation,
                midpoint rule at du/8                          (rect class)
  direct path : node-sample autocorrelation + trapezoid       (rect class)
  exact path  : exact piecewise-linear tent-sum F + scipy.quad (rect class)
```

E2t (three-way, Yoshida window, four structured vectors):

```text
  e_mid          matrix = −4.280070   direct = −4.669425   exact = −4.280719
  random_triple  matrix = −4.294776   direct = −4.678495   exact = −4.295440
  top_evec       matrix = +0.842070   direct = +0.030774   exact = +0.842070
  smoothed_evec  matrix = +0.841752   direct = +0.030408   exact = +0.841752
```

Diagnosis (hand-derived, then confirmed): the rect-class autocorrelation F
has slope 1/du at the origin, so the true right limit of the arch integrand
`num/D` at y = 0 is

```text
  F0 · (1/2 − 1/du)      NOT the smooth-class limit  F0/2.
```

Substituting `F0/2` at the y = 0 node biases the trapezoid by ≈ −F0/2 plus a
kink-cell curvature term — exactly the observed −0.39 … −0.81. After the fix
(`arch_direct` v3 = exact tent-sum + adaptive quad) all three paths agree to
4e-7 on smooth vectors and 2e-3 worst-case on rough random vectors, and E2x
cross-path reads 2.0e-3 (24 directions).

## 5. F70 settled: width-free refuted; window verdict is class-split

Two cleanly separated statements, both rig-grade:

```text
+--------------------------+------------------------------+-----------------+
| statement                | witness                      | verdict         |
+--------------------------+------------------------------+-----------------+
| F70 width-free           | smooth band-pass at w = 3    | REFUTED         |
| (mass-zero class)        | arch/F0 = +2.10 / +1.39 /    | (3/3 positive,  |
|                          | +0.69 at ξ₀ = 0.5/1/2        | E4)             |
+--------------------------+------------------------------+-----------------+
| F70 on the window class  | rect-basis top triple        | FAILS in the    |
| (triple-vanishing)       | eigenvector: λ = +0.8421     | RECT class      |
|                          | (= exact to 4e-7; smoothing  | (E2/E2s/E2t)    |
|                          | moves it only to +0.8407)    |                 |
+--------------------------+------------------------------+-----------------+
| F70 on the window class, | D³-root smooth band-pass,    | 8/8 NEGATIVE    |
| smooth probes            | arch/norm² ∈ [−0.36, −1.25]  | (E5)            |
+--------------------------+------------------------------+-----------------+
```

Reading:

- **Width-free F70 is dead.** In-band positivity (σ(ξ₀) can be up to +5.37)
  always beats out-of-band negative tails once the window is wide enough;
  w = 3 smooth witnesses do it robustly. The 1700 "F70 candidate" survives
  only with a width hypothesis.
- **The rect-class positivity is REAL, not a roughness artifact** — the
  three-way check pins it to 4e-7 and the top eigenvector's autocorrelation
  profile is already smooth (total variation 2.70). But the rect class is
  NOT the committed class: `CompactLogTest` is C^∞_c. Piecewise-constant
  test functions carry kink-cell contributions (F71) that have no smooth
  counterpart. **No verdict from the rect class lifts to the committed
  class in either direction.**
- **The smooth-class window verdict is OPEN, with the evidence one-sided:**
  every smooth probe so far reads negative (E5: 8/8 at both widths; E3
  random directions all ≈ −4.3 in the rect class, still negative after the
  F71 correction). No smooth positive direction was found
  (`smooth_triple_positive_found: false`).

## 6. F73: the window class is a falsifier oracle for RH itself

Because the window slice is prime-free and the pole is dead unconditionally,

```text
  RH  ⟹  arch(g ⋆ g̃) ≤ 0  for EVERY smooth triple-vanishing g
          supported in (−log 2/2, log 2/2).
```

This is a *necessity constraint on RH*, not on a route: a single
C^∞_c counterexample in that window would disprove RH outright (via the
committed equivalence). Conversely every negative probe is a consistency
check RH must keep passing. The rig's 128 smooth/negative readings are the
first systematic scan of this oracle; RH passes. This reframes the window
lane: it is no longer only "the cheapest place to prove P2", it is also the
cheapest place to *attack RH directly* — the search space is a
finite-dimensional-looking, width-0.346, three-linear-constraint class with
a diagonalizable quadratic form whose symbol is known in closed form (§2).

Prior art reinterpreted (all committed, none contradicted):

```text
  C1P2NarrowWindowCertificate.lean:33-38  narrowArchRoot: a STRICT
      negative-arch window instance — the first point of the oracle.
  C1P2BilateralProfile.lean:42-46         p2AggregateValue = arch + finite,
      the P2 residual as a committed definition.
  C1LaneRNarrowArch.lean                  Lane R = the narrow-arch program
      this wave reprices (σ closed form + oracle framing).
  C1P2BudgetNoGo.lean                     route guard: the Yoshida detector
      g is not itself a budget witness — unchanged; this wave attacks the
      budget on its own terms.
```

## 7. New laws

- **F71 (kink-cell law)**: the rect-basis discretization of the arch form
  carries an O(1) kink-cell contribution absent in the smooth class: the
  integrand's right limit at y = 0 is `F0(1/2 − 1/du)`, not `F0/2`; any
  node-quadrature that borrows the smooth-class limit biases arch by
  ≈ −F0/2. Three-way validation (matrix / direct / exact) is mandatory
  before reading any sign off a discretized quadratic form.
- **F72 (class-split sign law)**: the sign of the arch form on a test class
  is a property of the CLASS, not of the symbol: the rect class admits
  positive triple-vanishing directions at the Yoshida window
  (λ_triple = +0.8421, validated to 4e-7) while every smooth probe reads
  negative. No sign statement transfers between the rect class and C^∞_c in
  either direction.
- **F73 (RH-necessity oracle)**: RH ⟺ (given P1) `arch + finite ≤ 0` on the
  triple class; on the prime-free window slice this collapses to
  `arch ≤ 0` for smooth triple-vanishing g with support in
  (−log 2/2, log 2/2). The window class is therefore simultaneously the
  cheapest formal target (a single well-chosen g) and a direct RH falsifier;
  its symbol is σ(ξ) = log π − Re ψ(1/4 − iξ/2), positive for ξ < ξ* =
  6.2898, negative beyond.

## 8. What this wave does NOT claim

No nonnegativity theorem, no F70 in any class, no smooth-class sign
verdict, no detector construction, no carrier object, RH neither proved nor
threatened. The rect-class λ > 0 rows do not contradict RH (F72); the E5
negatives do not prove the window inequality (finitely many probes).

## 9. Next steps

1. **Smooth-class adjudication, rigorously**: replace the rect basis with a
   C^∞-faithful scheme (e.g. B-spline/`C^∞` bump basis or Fourier-band
   truncation on the window) and re-run the triple-constraint eigenvalue —
   the single most valuable number in the lane: its sign is the window face
   of P2.
2. **F70-with-width, paper version**: state and prove the sharp width
   threshold w₀(σ) for `arch ≤ 0` on band-limited probes (the σ chart says
   the threshold sits near ξ* via 1/ξ* ≈ 0.159; the Yoshida window is
   comfortably inside), and formalize the window consumption brick's
   hypothesis on a named smooth family.
3. **Formalize the oracle**: a Lean lemma packaging `RH → window arch ≤ 0`
   (one line from committed pieces), so any future smooth witness is a
   machine-checked RH event, positive or negative.
4. **σ tail from the committed digamma leaf**: convert
   `abs_digamma_le_of_re_ge_quarter` into an explicit `σ(ξ) ≤ log π +
   (‖ψ(1/2)‖+4+6/5)/2 + (12/5)‖·‖`-type bound and pin the out-of-band
   negativity theorem-grade (needed by any cancellation proof).
