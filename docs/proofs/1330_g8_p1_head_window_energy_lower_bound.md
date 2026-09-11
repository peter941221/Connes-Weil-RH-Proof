# Record 1330 — G8 P1 head-window energy lower bound (hcolumn criterion)

Date: 2026-09-11.
Status: FORMAL Lean brick (route-A decision tool).  It transports the
full-carrier column-energy premise `hcolumn` (records 1324-1328) into a
summability statement for the *head-window crossing energy* of the actual
Sonin carrier, and registers the audit finding on record 1329's Stage-0
infinite-rank assumption.  It proves no vanishing statement, no `qw` sign, no
`SourceRH`, and no RH claim.  RH is not claimed.

Consumer: the remaining P1 analytic obligation — the single named series
`hcolumn p : Summable fun i => ‖newFrameAntiresonantColumn ... (newSuffixFrame† (u_i))‖²`
(`C1G8P1RadialCrossingEnergyTransport.lean:85-88`).  This brick is the cheap
decisive test of that premise's plausibility *for the real carrier* (not its
vanishing-condition twins), replacing the closed 1329 probe as the
information source about `ran P_S`.

## 1. Three committed facts (verbatim, with owners)

Fact F1 — the new suffix frame is radial (`CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantRadialSplit.lean:88-93`):

```lean
theorem radialSupportProjection_comp_newSuffixFrame
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    radialSupportProjection lambda ∘L newSuffixFrame lambda S =
      newSuffixFrame lambda S
```

Fact F2 — the radial support subspace is the half-line vanishing condition
(`CCM24LogRadialSupport.lean:31-32, 67-69`):

```lean
def ccm24LogRadialLowerRegion (lambda) : Set ℝ := Set.Iio (Real.log lambda)

theorem mem_ccm24LogRadialSupportClosedSubspace_iff (lambda) (u) :
    u ∈ ccm24LogRadialSupportClosedSubspace lambda ↔
      ∀ᵐ t ∂volume, t < Real.log lambda → u t = 0
```

Fact F3 — the translation convention (`GlobalLogCrossing.lean:140-149`) and
the column's antiresonant core (`CCM24FiniteSCompletedJuliaAmbientDefectFactorization.lean:162-177`,
`CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantRadialBlockRecurrence.lean:73-77`):

```lean
theorem cc20GlobalLogTranslation_coeFn (b) (u) :
    (cc20GlobalLogTranslation b u : ℝ → ℂ) =ᵐ[volume] fun t => u (t + b)

def primeEulerAntiresonantCore (p) :=
  ContinuousLinearMap.id ℂ finiteSCarrier +
    (cc20GlobalLogTranslation (Real.log p)).toContinuousLinearMap   -- I + U_(log p)

theorem newFrameAntiresonantColumn_eq_scale_smul_core (lambda) (p) (S) :
    newFrameAntiresonantColumn lambda p S =
      (primeEulerAmbientLossScale p : ℂ) •
        (primeEulerAntiresonantCore p ∘L newSuffixFrame lambda S)
```

## 2. Stage-0 reduction: the head-window criterion (paper)

Write `a := Real.log lambda`, `τ := Real.log p > 0`, and define the
**head-window scale** `headWindowScale lambda p := ⟨lambda * p, _⟩`, so
`Real.log (headWindowScale lambda p) = a + τ` (`Real.log_mul`).  The head
window is the first shift-length of the half-line: `[a, a + τ)`.

Commutation (new Lean fact, indicator proof): for `U := (cc20GlobalLogTranslation τ).toCLM`
and `radialComplement mu := id - radialSupportProjection mu`,

```text
radialComplement lambda ∘L U  =  U ∘L radialComplement (headWindowScale lambda p)
```

pointwise-a.e. both sides equal `(Iio a).indicator (fun t => f (t + τ))` — the
lower window of the base scale is exactly the `τ`-preimage of the lower window
of the head scale.

Pointwise control (new Lean fact): for every `v` fixed by
`radialSupportProjection lambda` (in particular `v = newSuffixFrame S (newSuffixFrame S† u)`
by Fact F1):

```text
‖radialComplement (headWindowScale lambda p) v‖
  = ‖U v‖-of-lower-part ...  [isometry ‖U x‖ = ‖x‖, commute, radialComplement lambda v = 0]
  = ‖radialComplement lambda (v + U v)‖
  = ‖radialComplement lambda (primeEulerAntiresonantCore p v)‖
  ≤ ‖primeEulerAntiresonantCore p v‖          [‖radialComplement λ‖ ≤ 1].
```

Transport (new Lean fact): with `column` and `hcolumn` exactly as in the
1324 premise,

```text
hcolumn  ⟹  Summable fun i =>
  ‖radialComplement (headWindowScale unitSoninScale p)
    (newSuffixFrame unitSoninScale S (newSuffixFrame S† (sourceBasis i)))‖²
```

(constant stripping `(‖lossScale p‖⁻¹)²` uses
`primeEulerAmbientLossScale_pos`; the loss scale `‖(c:ℂ)⁻¹‖·‖(c:ℂ)‖ = 1` closes
it by `field_simp`).

Meaning: the head-window term is the carrier mass that the `log p`-shift
carries BELOW the Sonin cutoff.  Antiperiodicity `U_τ e ≈ -e` can never touch
it: the shifted head is disjoint from the half-line, so its defect is
exactly `2·‖head‖²`, and the criterion is the sharp form of "the identity
part must be cancelled by the shift part" from 1329 §1 — now for the REAL
carrier, not a twin.

## 3. Registered decision dichotomy (not proved here)

`hcolumn` holds only if the head-window crossing operator
`H_{λ,p} := radialComplement (headWindowScale λ p) ∘L P_S` (P_S the carrier
projection) is Hilbert-Schmidt along carrier bases.  Exactly one of:

```text
(i)  H_{λ,p} is not compact — e.g. the carrier contains an infinite
     orthonormal family supported in the head window; then ¬ hcolumn and
     the radial leg 1324-1328 is vacuous.
(ii) ran(newSuffixFrame λ S) ⊆ Ici(log λ + log p) a.e., i.e. the carrier
     has zero head-window mass for this p; then the criterion is silent.
```

Which case holds is a structural question about
`sourceSoninCarrier = radial ⊓ HT⁻¹(radial)`
(`CCM24HardyTitchmarsh.lean:376-381`) — the dimension/nontriviality question
below.  Any formal falsification or a carrier-structure theorem is a NEW
preregistration; this record authorizes none.

## 4. Audit finding against record 1329 §1 (registered defect)

Record 1329 §1 states: "The identity part alone contributes `2·rank(P_S)` and
`rank(P_S) = ∞`".  The repository contains NO theorem that
`sourceSoninCarrier λ` (equivalently `ran (newSuffixFrame λ S)`, a Sonin
space defined by TWO support conditions) is infinite-dimensional, nonzero, or
even non-degenerate:

```text
grep -rn "infiniteDimensional|FiniteDimensional" ConnesWeilRH/ | grep -iE "sonin|carrier"  ->  empty
```

The 1329 verdict itself is safe (its statistics never needed the rank), but
its Stage-0 *reduction narrative* used an unproved premise.  This record's
§2 replaces the narrative with a proved implication whose consequence is a
named, checkable operator.  Future Stage-0 reductions must either cite a
carrier non-degeneracy theorem or stay silent on rank.

## 5. Lean owners and verification

Dev leaf: `ConnesWeilRH/Dev/C1G8P1HeadWindowEnergyLowerBound.lean`, paired
audit `C1G8P1HeadWindowEnergyLowerBoundAudit.lean`.  Audited declarations:

```text
headWindowScale, log_headWindowScale,
radialComplement_coeFn_indicator,
radialComplement_translation_commute,
norm_radialComplement_headWindow_le_norm_antiresonantCore,
summable_headWindowCrossing_normSq_of_antiresonantColumnEnergy
```

Acceptance: focused build + audit log `1542_g8_p1_head_window_batch.log`,
footer success, zero `error:`, zero `sorryAx`, `[propext, Classical.choice,
Quot.sound]` only.

RH is not claimed.
