# Record 1351 (DESIGN-ONLY) - the (star) <-> SourceRH Lean brick: decomposition, inventory, build order

> **1353 correction pointer (2026-09-12):** this decomposition is
> CONFIRMED by [`1353`](1353_c6_placement_audit_and_nlle_spec_repair.md)
> and gets one strengthening: B2's "window-wise counts" leg cannot be
> carried by an explicit frame-bound HYPOTHESIS alone - a count
> hypothesis is FALSE as a sufficiency (clustered on-line sets defeat
> the energy step). B2 must carry the NLLE-v2 two-limb hypothesis
> (count + spread, 1353 s5), or the windowwise reading stays out of the
> brick. The iff core B1+B4 is C6-free exactly as designed here - the
> 1353 audit touches only the advertised WINDOWWISE side, never the
> equivalence wiring.

```text
+---------------------------------------------------------------------+
| DESIGN PREREGISTRATION for a future build, NOT a funding request    |
| granted by itself. No Lean code written here; no digits; no probe.  |
| MODEL grade for effort estimates; certifies nothing; RH NOT        |
| claimed. Owner ruling needed before any build (decision policy:    |
| new module boundary).                                              |
| Produced in the 2026-09-12 parallel wave ("can finish everything   |
| in parallel").                                                      |
+---------------------------------------------------------------------+
```

## 0. P0 discharged: the exponentialWeight / laplaceAt sign convention

The 1345 s5 "first parse task" is CLOSED by direct read of the
committed source. Raw code (ConnesWeilRH/Source/
CC20YoshidaConvolution.lean:35-56):

```lean
noncomputable def exponentialWeight (f : CompactLogTest) (s : ℂ) :
    CompactLogTest := by
  let raw : ℝ → ℂ := fun x => Complex.exp (s * (x : ℂ)) * f.test x
  ...

noncomputable def laplaceAt (f : CompactLogTest) (s : ℂ) : ℂ :=
  ∫ x : ℝ, (exponentialWeight f s).test x
```

Read-out: the kernel is POSITIVE-character,

```text
  laplaceAt f s = ∫ exp(+s·x) f(x) dx        (bilateral, x = log t)
```

and the bridge theorem
`laplaceAt_compactLogTestOfWindow_eq_mellin` (:60-71) identifies it
with the repo `mellin` on the positive-variable side, i.e.

```text
  ∫ exp(s·u) g(exp u) du  =  ∫₀^∞ g(x) x^s dx/x  =  mellin g s
```

(the proof's change-block at :84-91 performs u ↦ -u and the
exp/exp_add rewriting; Fourier convention enters via
`mellin_eq_fourier, Real.fourier_eq'` at :72). CONSEQUENCE for (star):
on the line, G(iξ) = laplaceAt f (iξ) = ∫ e^{+iξx} f(x) dx - the POSITIVELY-
signed Fourier character. Every analytic "G" quoted in 1345/1346 must
be read in THIS convention; the conjugation identity
G̅(iξ) = G(-iξ) (which powers the quartet factor-4 algebra, 1345:56-64)
holds as Re G(iξ)... unchanged, but the brick must state it through
`exponentialWeight`, not through a hand-typed integral.

## 1. Committed-statement inventory (the brick's supply chain)

| # | object | location | role in brick |
|---|---|---|---|
| S1 | `exponentialWeight` / `laplaceAt` | CC20YoshidaConvolution.lean:35-56 | defines G := laplaceAt (s = I·γ / s = w) |
| S2 | `laplaceAt_compactLogTestOfWindow_eq_mellin` | :60-71 | G vs mellin dictionary (one lemma, done) |
| S3 | `convolutionSquare` | CompactLogConvolution.lean:114-124 | the bump class C_c: qw built from f * f |
| S4 | `spectralTerm` | C1SpectralWeil.lean:108-115 | zeros-side sum with multiplicities |
| S5 | on/off-line split of the spectral side | C1SpectralOnlineSplit.lean:47-67 | turns S4 into sum_on + sum_off (the quartet grouping lives here or must be added next to it) |
| S6 | gate iff legs `weilCriterion_iff_sourceRH`, `qw_nonneg_iff_nonempty_family` | C1WeilCriterionEquivalence.lean:136-141 / :118-129 | the committed anchor (d767a1d) the brick must plug into |

## 2. Target theorem (design form, names tentative)

File `C1N1SamplingContest.lean`. Two theorems, in the order provable:

```lean
-- B1 (pure algebra, no analysis):
theorem quartet_loss_eq_four_mul_Re :   -- factor-4 bookkeeping:
  -- grouping off-line zeros into {rho, rhobar, 1-rho, 1-rhobar}
  -- total term = 4 * m * (laplaceAt f w * laplaceAt f (-w))  .real

-- B4 (the advertised equivalence, conditionally on B2/B3 inputs):
theorem n1Contest_iff_qw_nonneg :
  (∀ g in vanishingClass, 0 ≤ qw g) ↔
  (∀ f, Σ_on m |G(iγ)|² ≥ 4 Σ_q m |G(w)G(-w)|)
```

Design decision D0: prove the ε-TRUNCATED version first (finite
height box, finite bump family - mirrors the pen-and-paper 1345 s2
proof), then a single limit-exchange lemma. This keeps the first
green brick inside the analytic budget of the 1343-style session
(3 axioms precedent, 0 sorryAx) and defers the tall poles (B2/B3)
into named hypothesis slots they can later be discharged into.

## 3. Decomposition and dependency truth-table

| leg | content | status / blocker |
|---|---|---|
| B1 | quartet algebra + factor 4 (the F5-corrected form, |G(w)G(-w)| not Re[G²]) | GREEN-LIT standalone; pure rewriting on S1+S5 |
| B3 | window localization: Nyquist/tail estimate for the band-limited bumps (sinc² ~ 0 adjacent-node claim, 1346:74-75) | ESTIMATION leg; Paley-Wiener-ish; medium-heavy; feeds the f<1/3 per-window reading, NOT the iff |
| B2 | per-zero balance: turning Σ ≥ Σ into window-wise counts | INJECTS C6 (frame bound on the bump family) - the missing bone C7's *sibling*; brick must carry it as an explicit named hypothesis until C6 is proved or class-restricted |
| B4 | (star) ↔ gate wiring: S4/S5 split of spectralTerm against S6's committed iff | MECHANICAL once B1 done; the iff legs reuse d767a1d verbatim |
| C6 | frame bound: Σ|⟨f_n, h⟩|² ≤ A‖h‖² on our specific bump family | UNPROVED anywhere in repo (1346: "C6 second bone"); build option = prove for the Rp=R/(1+1.6/m) family via uncertainty-principle bookkeeping, or downgrade B2 to hypothesis |

Honest map:

```text
   B1 ----\
           +---> B4 -----> n1Contest_iff_qw_nonneg  (iff, gate-level)
   S6 ----/                       ^
   B2 (needs C6) ----------> only the WINDOWWISE f<1/3 reading (B3+B2)
```

i.e. the EQUIVALENCE brick (B1+B4) does NOT need C6 at all - C6 is
needed only for the geometric RE-INTERPRETATION (1346's f<1/3 in a
window), which H1/H2 in 1350 carry as their own open legs.

## 4. Effort and risk (MODEL estimates)

| task | estimate | precedent |
|---|---|---|
| B1 | 1 focused session (few hundred lines) | 1343 brick: single-file equivalence, 3 axioms |
| B4 | 1-2 sessions | reuses committed iff legs |
| B3 | multi-session estimation campaign | = G8-tower-scale difficulty, smaller |
| C6 | open problem at repo scale | second-bone status (1346) |

Build order: B1 -> B4 -> (owner review of green core) -> decide
B3/C6 separately from the brick. Risk if built naively as ONE
theorem: B2/C6 contaminates the iff with a hypothesis it does not
need (section 3 map); the two-theorem split in s2 prevents that.

## 5. Non-claims and next steps

- This design asserts no theorem; D0/estimates are MODEL-grade.
- N1 lane remains PENDING-and-UNFUNDED (1346 s6, 1347 s4); a funded
  build would be a NEW task with its own PREREG (law 42: no code
  before statement is locked in the build prereg).

1. Owner ruling: fund B1+B4 green-core build, or park design.
2. If funded: `1351b` build prereg (statement text locked, axiom
   budget stated, no digits concept).
3. B3/C6 remain thermometer-lane science, not brick engineering.
