/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Dev.C1WeilCriterionEquivalence
import ConnesWeilRH.Dev.C1HealthyTestSpace
import ConnesWeilRH.Dev.C1HealthyYoshidaDetector

/-!
# C1MinimalWeilCriterion - the wall's minimal normal form (record 1416)

The committed gate is stated with a three-point Mellin vanishing hypothesis:

```text
  forall g : CompactLogTest,
    CC20VanishesOn healthyCC20TestSpace cc20TripleFiniteVanishingSet g ->
      0 <= qw g
```

with `cc20TripleFiniteVanishingSet = {zero, half, one}`
(`CC20RHExit.lean:21`).  Record 1416 asked whether that node set is a
genuine degree of freedom - in particular whether a scale-covariant
producer could move it, which is the only way the O2 radius gap
(`docs/map/004` section 8) could be crossed by dilation.  Two readings
answer both questions at once.

**The vanishing hypothesis is vestigial in the equivalence.**  The
reverse leg `qw_nonneg_of_sourceRH` (`C1WeilCriterionEquivalence.lean:103`)
takes no vanishing argument at all - it splits `qw` into on-line and
off-line spectral mass, kills the off-line part under `SourceRH`, and
keeps the on-line part nonnegative.  The committed `iff` already
discards the hypothesis (`fun hRH g _hg => ...`,
`C1WeilCriterionEquivalence.lean:140`), and the file header says so in
prose (`:20-24`, "The vanishing hypothesis is not even consumed").  What
was never stated is the consequence: the gate family is monotone in the
node set, so every sub-triple `F` gives an `SourceRH`-equivalent gate,
and the extreme `F = 0` is the side-condition-free normal form

```text
  (forall g : CompactLogTest, 0 <= qw g) <-> SourceRH
```

Smaller `F` means a STRONGER gate (more tests in scope), so this is a
sharpening, not a shortcut: nothing here makes the wall easier.

**`half` is the structural node; `zero` and `one` are not read by the
certificate chain.**  The only place the certificate route consumes
vanishing is the pole kill, and it reads `half` alone
(`poleTerm_convolutionSquare_of_vanishesOn_cc20Triple`,
`C1HealthyYoshidaDetector.lean:102-110`, whose body invokes only
`CriticalVanishingPoint.half`).  Part 4 restates the whole reduction
`qw = -archimedean - finitePrime`, and the root-support specialization
`qw = -archimedean`, from the singleton `{half}` hypothesis - so the
endpoint sign interface keeps its exact shape with one node instead of
three.  Since the pole pair `(+-1/2)` belongs to `xi` and not to the
test, no transformation of `g` can relocate it: the scale-covariant
producer route is dead, and the dilation rigidity
`laplaceAt (D_lambda g) s = (1/lambda) * laplaceAt g (s/lambda)`
leaves `lambda = 1` as the only symmetry of any node set containing
`half`.

SCOPE: pure reassembly of landed blocks.  No sign theorem, no
positivity statement, no inequality about zeta.  RH NOT claimed; the
gate stays OPEN in every form below.
-/

namespace ConnesWeilRH
namespace Source
namespace C1MinimalWeilCriterion

open CC20YoshidaConvolution
open CC20YoshidaConvolution.CompactLogTest
open CCM25Concrete.CompactLogConvolution
open CCM25Concrete.CompactLogConvolution.CompactLogTest
open C1SameOwnerWeil
open C1HealthyYoshidaDetector
open C1WeilCriterionEquivalence

noncomputable section

/-! ### Part 1: the vanishing predicate is monotone in the node set -/

/-- Vanishing on a larger node set implies vanishing on every subset of it.
This is the whole content of the gate family's monotonicity; it is a
restriction of a universal quantifier and carries no analysis. -/
theorem vanishesOn_of_subset
    {C : CC20TestSpace} {F F' : Finset CriticalVanishingPoint} {g : C.Test}
    (hsub : F ⊆ F') (h : CC20VanishesOn C F' g) : CC20VanishesOn C F g :=
  fun p hp => h p (hsub hp)

/-- The empty node set imposes nothing: every test vanishes on it. -/
theorem vanishesOn_empty (C : CC20TestSpace) (g : C.Test) :
    CC20VanishesOn C ∅ g := by
  intro p hp
  simp at hp

/-- On the healthy compact-log carrier, vanishing on the singleton `{half}`
is exactly vanishing of the bilateral Laplace transform at `1/2`. -/
theorem vanishesOn_singleton_half_iff (g : CompactLogTest) :
    CC20VanishesOn C1.healthyCC20TestSpace {CriticalVanishingPoint.half} g ↔
      CompactLogTest.laplaceAt g (1 / 2 : ℂ) = 0 := by
  constructor
  · intro h
    simpa [C1.healthyMellinReadoff, criticalVanishingPointValue] using
      h CriticalVanishingPoint.half (by simp)
  · intro h p hp
    have hp' : p = CriticalVanishingPoint.half := Finset.mem_singleton.mp hp
    subst hp'
    simpa [C1.healthyMellinReadoff, criticalVanishingPointValue] using h

/-- The committed triple hypothesis already contains the structural node:
this is the transcription of `laneRTripleVanishing_laplaceAt_half`
(`C1XiCenterTwoGammaConstrainedPrefix.lean:229`) into the minimal form. -/
theorem vanishesOn_half_of_vanishesOn_triple (g : CompactLogTest)
    (h : CC20VanishesOn C1.healthyCC20TestSpace
      cc20TripleFiniteVanishingSet g) :
    CompactLogTest.laplaceAt g (1 / 2 : ℂ) = 0 := by
  simpa [C1.healthyMellinReadoff, criticalVanishingPointValue] using
    h CriticalVanishingPoint.half (by simp [cc20TripleFiniteVanishingSet])

/-! ### Part 2: the gate family, monotone in the node set -/

/-- The surviving gate, parameterized by its Mellin vanishing node set.
`F = cc20TripleFiniteVanishingSet` recovers the committed statement of
record 1341. -/
def weilGate (F : Finset CriticalVanishingPoint) : Prop :=
  ∀ g : CompactLogTest,
    CC20VanishesOn C1.healthyCC20TestSpace F g → 0 ≤ C1SameOwnerWeil.qw g

/-- A gate on a SMALLER node set is STRONGER: it quantifies over more tests.
So `F ⊆ F'` transports `weilGate F` to `weilGate F'`, losing strength. -/
theorem weilGate_of_subset {F F' : Finset CriticalVanishingPoint}
    (hsub : F ⊆ F') (h : weilGate F) : weilGate F' :=
  fun g hg => h g (vanishesOn_of_subset hsub hg)

/-- The committed normal form, restated in the parameterized family. -/
theorem weilGate_triple_iff_sourceRH :
    weilGate cc20TripleFiniteVanishingSet ↔
      RHDefinitionBridge.standard.SourceRH :=
  C1WeilCriterionEquivalence.weilCriterion_iff_sourceRH

/-- **Every sub-triple node set gives an `SourceRH`-equivalent gate.**
The forward leg weakens the gate up to the committed triple and applies
the landed equivalence; the reverse leg is `qw_nonneg_of_sourceRH`,
which never reads the vanishing hypothesis. -/
theorem weilGate_iff_sourceRH_of_subset_triple
    {F : Finset CriticalVanishingPoint}
    (hF : F ⊆ cc20TripleFiniteVanishingSet) :
    weilGate F ↔ RHDefinitionBridge.standard.SourceRH := by
  constructor
  · intro h
    exact C1WeilCriterionEquivalence.weilCriterion_iff_sourceRH.mp
      (weilGate_of_subset hF h)
  · intro hRH g _hg
    exact C1WeilCriterionEquivalence.qw_nonneg_of_sourceRH g hRH

/-! ### Part 3: the two extreme instantiations -/

/-- **The side-condition-free normal form of the wall.**  Proving
nonnegativity of `qw` on EVERY compactly supported log test - with no
Mellin vanishing hypothesis whatsoever - is equivalent to `SourceRH`.
The vanishing node set is therefore not a degree of freedom of the
equivalence: it can be deleted, and deleting it makes the obligation
stronger. -/
theorem weilGate_unconditional_iff_sourceRH :
    (∀ g : CompactLogTest, 0 ≤ C1SameOwnerWeil.qw g) ↔
      RHDefinitionBridge.standard.SourceRH := by
  have hempty :
      (∀ g : CompactLogTest, 0 ≤ C1SameOwnerWeil.qw g) ↔ weilGate ∅ := by
    constructor
    · intro h g _hg
      exact h g
    · intro h g
      exact h g (vanishesOn_empty _ _)
  exact hempty.trans
    (weilGate_iff_sourceRH_of_subset_triple (Finset.empty_subset _))

/-- **The pole-minimal normal form.**  One Mellin node - the right image
of the `xi` pole pair - already suffices to make the gate equivalent to
`SourceRH`.  This is the weakest hypothesis under which the certificate
route of Part 4 still runs. -/
theorem weilGate_halfOnly_iff_sourceRH :
    (∀ g : CompactLogTest,
      CompactLogTest.laplaceAt g (1 / 2 : ℂ) = 0 →
        0 ≤ C1SameOwnerWeil.qw g) ↔
      RHDefinitionBridge.standard.SourceRH := by
  have hsub :
      ({CriticalVanishingPoint.half} : Finset CriticalVanishingPoint) ⊆
        cc20TripleFiniteVanishingSet := by
    rw [Finset.singleton_subset_iff]
    simp [cc20TripleFiniteVanishingSet]
  have hkey :
      (∀ g : CompactLogTest,
        CompactLogTest.laplaceAt g (1 / 2 : ℂ) = 0 →
          0 ≤ C1SameOwnerWeil.qw g) ↔
        weilGate {CriticalVanishingPoint.half} := by
    constructor
    · intro h g hg
      exact h g ((vanishesOn_singleton_half_iff g).mp hg)
    · intro h g hg
      exact h g ((vanishesOn_singleton_half_iff g).mpr hg)
  exact hkey.trans (weilGate_iff_sourceRH_of_subset_triple hsub)

/-! ### Part 4: the certificate chain reads `half` and nothing else

The reductions below are the exact counterparts of
`C1HealthyYoshidaDetector.lean:102-175`, with the triple hypothesis
replaced by the singleton `{half}`.  Their existence is the minimality
witness: `zero` and `one` are never read, so no certificate argument in
this route can depend on them. -/

/-- Vanishing at the single structural node kills the pole term of the
Hermitian square, because the Hermitian pairing needs only one of the two
pole factors. -/
theorem poleTerm_convolutionSquare_of_vanishesOn_halfOnly (g : CompactLogTest)
    (h : CC20VanishesOn C1.healthyCC20TestSpace
      {CriticalVanishingPoint.half} g) :
    C1SameOwnerWeil.poleTerm g.convolutionSquare = 0 :=
  poleTerm_convolutionSquare_of_laplaceAt_half_eq_zero g
    ((vanishesOn_singleton_half_iff g).mp h)

/-- On `{half}`-vanishing tests the whole same-owner Weil functional is the
negative archimedean-plus-finite-prime remainder. -/
theorem qw_eq_neg_archimedeanTerm_sub_finitePrimeSum_of_vanishesOn_halfOnly
    (g : CompactLogTest)
    (h : CC20VanishesOn C1.healthyCC20TestSpace
      {CriticalVanishingPoint.half} g) :
    C1SameOwnerWeil.qw g =
      -(C1SameOwnerWeil.archimedeanTerm g.convolutionSquare) -
        C1SameOwnerWeil.finitePrimeSum g.convolutionSquare := by
  rw [C1SameOwnerWeil.qw_eq_psi_square, C1SameOwnerWeil.psi_eq_components,
    poleTerm_convolutionSquare_of_vanishesOn_halfOnly g h]
  ring

/-- Root support in the full Yoshida window `[-log 2 / 2, log 2 / 2]` places
the Hermitian square in the open prime-free window `(-log 2, log 2)`; with
only the structural node, `qw` is then exactly the negative archimedean
term. -/
theorem qw_eq_neg_archimedeanTerm_of_vanishesOn_halfOnly_of_rootSupport_logTwoHalf
    (g : CompactLogTest)
    (hvanishes : CC20VanishesOn C1.healthyCC20TestSpace
      {CriticalVanishingPoint.half} g)
    (hsupport : Function.support g.test ⊆
      Set.Icc (-(Real.log 2 / 2)) (Real.log 2 / 2)) :
    C1SameOwnerWeil.qw g =
      -C1SameOwnerWeil.archimedeanTerm g.convolutionSquare := by
  have hwindow :=
    CompactLogTest.convolutionSquare_support_subset_two_mul_Ioo g hsupport
  have htwo : (2 : ℝ) * (Real.log 2 / 2) = Real.log 2 := by ring
  rw [htwo] at hwindow
  rw [qw_eq_neg_archimedeanTerm_sub_finitePrimeSum_of_vanishesOn_halfOnly
      g hvanishes,
    C1SameOwnerWeil.finitePrimeSum_eq_zero_of_support_subset_open_log_two
      g.convolutionSquare hwindow]
  ring

/-- The endpoint sign interface in its minimal form: once the archimedean
term is known nonpositive on the centered root-support class, the
same-owner Weil value is nonnegative there - from ONE Mellin node. The
analytic nonpositivity itself remains the open obligation. -/
theorem qw_nonneg_of_archimedeanTerm_nonpos_of_vanishesOn_halfOnly_of_rootSupport_logTwoHalf
    (g : CompactLogTest)
    (hvanishes : CC20VanishesOn C1.healthyCC20TestSpace
      {CriticalVanishingPoint.half} g)
    (hsupport : Function.support g.test ⊆
      Set.Icc (-(Real.log 2 / 2)) (Real.log 2 / 2))
    (harch : C1SameOwnerWeil.archimedeanTerm g.convolutionSquare ≤ 0) :
    0 ≤ C1SameOwnerWeil.qw g := by
  rw [qw_eq_neg_archimedeanTerm_of_vanishesOn_halfOnly_of_rootSupport_logTwoHalf
    g hvanishes hsupport]
  linarith

end

end C1MinimalWeilCriterion
end Source
end ConnesWeilRH
