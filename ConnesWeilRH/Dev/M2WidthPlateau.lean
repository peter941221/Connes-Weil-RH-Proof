import ConnesWeilRH.Dev.Wall14PlateauExplicitComplex
import ConnesWeilRH.Dev.C1WeilExplicit

/-!
# M2WidthPlateau - width-scaled legacy M.2 carrier

Width-parameterized counterpart of the explicit flat-top compact bump
bumpPlateauTest. The old M-2/990 sign-boundary numerics used the wrong pole,
prime coordinates, and a prime-2 truncation. They do not determine the sign of
the complete Weil value.
This file makes the same geometric carriers expressible as CompactLogTest
objects with an arbitrary support half-width w > 0, via
wideBump w x = bumpEx (x / w), folding the base
bump support [-1,1] to [-w,w].  Lifts to a complex test wideTest (proving
test 0 = 1 and HasCompactSupport) and reads C1WeilExplicit.healthyQw on two
plain plateau carriers.

SCOPE (docs/990 + 989):
* makes the width-scaled legacy carriers and their complete healthyQw values
  expressible / stateable;
* NO bound (healthyQw <= 0), NO sign assertion, NO finite-vanishing.
* The smooth {0, 1/2, 1}-vanishing residual used by corrected numerics is a
  different object and is not part of this module.
All proofs axiom-clean ([propext, Classical.choice, Quot.sound], 0 sorry).
RH NOT claimed.
-/
namespace ConnesWeilRH
namespace Source
namespace Dev
namespace M2Width
open Wall14Plateau
open ConnesWeilRH.Source.CCM25Concrete.CompactLogConvolution

noncomputable def wideBump (w x : Real) : Real := bumpEx (x / w)

lemma wideBump_plateau (w : Real) (wpos : 0 < w) (x : Real)
    (hx : x ^ 2 ≤ bplateau ^ 2 * w ^ 2) : wideBump w x = 1 := by
  unfold wideBump
  apply bump_eq_one_of_sq_le (x / w)
  unfold bSq
  have hw2 : 0 < w ^ 2 := pow_pos wpos 2
  rw [div_pow, div_le_iff₀ hw2]
  simpa [pow_two, bplateau] using hx

lemma wideBump_outer (w : Real) (wpos : 0 < w) (x : Real)
    (h : w ^ 2 ≤ x ^ 2) : wideBump w x = 0 := by
  unfold wideBump
  apply bumpEx_eq_zero_of_one_le_sq (x / w)
  have hw2 : 0 < w ^ 2 := pow_pos wpos 2
  rw [div_pow, one_le_div hw2]
  exact h

lemma wideBump_abs_lt (w : Real) (wpos : 0 < w) (x : Real)
    (hnz : wideBump w x ≠ 0) : |x| < w := by
  have hy : bumpEx (x / w) ≠ 0 := by
    intro h0
    apply hnz
    simpa [wideBump] using h0
  have hsq : (x / w) ^ 2 < 1 := bumpEx_ne_zero_of_sq_lt_one (x / w) hy
  have habs : |x / w| < 1 := (sq_lt_one_iff_abs_lt_one (x / w)).mp hsq
  rw [abs_div] at habs
  rw [abs_of_pos wpos] at habs
  exact (div_lt_one wpos).mp habs

lemma wideBump_mem_Icc (w : Real) (wpos : 0 < w) (x : Real)
    (hnz : wideBump w x ≠ 0) : x ∈ Set.Icc (-w) w := by
  have hk : |x| < w := wideBump_abs_lt w wpos x hnz
  rcases (abs_lt.mp hk) with ⟨hl, hu⟩
  exact ⟨le_of_lt hl, le_of_lt hu⟩

theorem wideBump_contDiff (w : Real) :
    ContDiff Real (⊤ : ℕ∞) (fun x : Real => wideBump w x) := by
  unfold wideBump
  have hz : ContDiff Real (⊤ : ℕ∞) (fun x : Real => x / w) := by
    fun_prop
  exact bumpEx_contDiff.comp hz

noncomputable def wideFun (w x : Real) : Complex := Complex.ofRealCLM (wideBump w x)

theorem wideFun_contDiff (w : Real) :
    ContDiff Real (⊤ : ℕ∞) (wideFun w : ℝ → Complex) := by
  simpa [wideFun] using Complex.ofRealCLM.contDiff.comp (wideBump_contDiff w)

theorem wideFun_compact (w : Real) (wpos : 0 < w) : HasCompactSupport (wideFun w) := by
  unfold HasCompactSupport
  apply IsCompact.of_isClosed_subset (isCompact_Icc (a := (-w)) (b := w))
  · exact isClosed_closure
  · have hsub : Function.support (wideFun w) ⊆ Set.Icc (-w) w := by
      intro x hx
      have hb : wideBump w x ≠ 0 := by
        intro h0
        apply hx
        simp [wideFun, h0]
      exact wideBump_mem_Icc w wpos x hb
    simpa [isClosed_Icc.closure_eq] using closure_mono hsub

noncomputable def wideSchema (w : Real) (wpos : 0 < w) :=
  (wideFun_compact w wpos).toSchwartzMap (wideFun_contDiff w)

noncomputable def wideTest (w : Real) (wpos : 0 < w) : CompactLogTest where
  test := wideSchema w wpos
  compactSupport := wideFun_compact w wpos

theorem wideTest_apply (w : Real) (wpos : 0 < w) (x : Real) :
    (wideTest w wpos).test x = (wideBump w x : Complex) := by
  change wideFun w x = (wideBump w x : Complex)
  rfl

theorem wideTest_zero (w : Real) (wpos : 0 < w) :
    (wideTest w wpos).test 0 = (1 : Complex) := by
  rw [wideTest_apply]
  have hb : wideBump w 0 = 1 := by
    apply wideBump_plateau w wpos 0
    have hp : (0 : Real) ≤ bplateau ^ 2 * w ^ 2 := by
      positivity
    simpa [pow_two] using hp
  simp [hb]

/-- The wider legacy M2 carrier, with support half-width `3/2`. -/
noncomputable def wideW : Real := 3 / 2

lemma wideW_pos : 0 < wideW := by
  unfold wideW
  norm_num

noncomputable def wideC : CompactLogTest := wideTest wideW wideW_pos

theorem wideC_zero : wideC.test 0 = (1 : Complex) :=
  wideTest_zero wideW wideW_pos

theorem wideC_hasCompactSupport : HasCompactSupport wideC.test :=
  wideC.compactSupport

/-- Complete healthy-psi value on the wider carrier square (expression only;
no sign asserted). -/
noncomputable def widePsi : Real :=
  ConnesWeilRH.Source.C1WeilExplicit.healthyQw wideC




/-- The narrower legacy M2 carrier, with support half-width `6/5`. -/
noncomputable def narrowW : Real := 6 / 5

lemma narrowW_pos : 0 < narrowW := by
  unfold narrowW
  norm_num

noncomputable def narrowC : CompactLogTest := wideTest narrowW narrowW_pos

theorem narrowC_zero : narrowC.test 0 = (1 : Complex) :=
  wideTest_zero narrowW narrowW_pos

theorem narrowC_hasCompactSupport : HasCompactSupport narrowC.test :=
  narrowC.compactSupport

/-- Complete healthy-psi value on the narrower carrier square (expression only;
no sign asserted). -/
noncomputable def narrowPsi : Real :=
  ConnesWeilRH.Source.C1WeilExplicit.healthyQw narrowC





/-- Exact decomposition into pole, archimedean, and every visible prime-power
term of the same convolution square. -/
theorem healthyQw_decomposition (c : CompactLogTest) :
    ConnesWeilRH.Source.C1WeilExplicit.healthyQw c =
      ConnesWeilRH.Source.C1SameOwnerWeil.poleTerm c.convolutionSquare -
        ConnesWeilRH.Source.C1SameOwnerWeil.archimedeanTerm c.convolutionSquare -
          ConnesWeilRH.Source.C1SameOwnerWeil.finitePrimeSum c.convolutionSquare := by
  rfl

/-- Specialized to the wider plain plateau carrier. -/
theorem widePsi_decomposition : widePsi =
      ConnesWeilRH.Source.C1SameOwnerWeil.poleTerm wideC.convolutionSquare -
        ConnesWeilRH.Source.C1SameOwnerWeil.archimedeanTerm wideC.convolutionSquare -
          ConnesWeilRH.Source.C1SameOwnerWeil.finitePrimeSum wideC.convolutionSquare := by
  unfold widePsi
  exact healthyQw_decomposition wideC

/-- Specialized to the narrower plain plateau carrier. -/
theorem narrowPsi_decomposition : narrowPsi =
      ConnesWeilRH.Source.C1SameOwnerWeil.poleTerm narrowC.convolutionSquare -
        ConnesWeilRH.Source.C1SameOwnerWeil.archimedeanTerm narrowC.convolutionSquare -
          ConnesWeilRH.Source.C1SameOwnerWeil.finitePrimeSum narrowC.convolutionSquare := by
  unfold narrowPsi
  exact healthyQw_decomposition narrowC





/-- The source Weil value is the negative CC20 local sum on the same square. -/
theorem healthyQw_eq_neg_weilLocalSum (c : CompactLogTest) :
    ConnesWeilRH.Source.C1WeilExplicit.healthyQw c =
      -ConnesWeilRH.Source.C1.healthyCC20TestSpace.weilLocalSum
          (ConnesWeilRH.Source.C1.healthyCC20TestSpace.starConvolution c) := by
  rw [ConnesWeilRH.Source.C1.healthyWeilSquareReadoff]
  simp [ConnesWeilRH.Source.C1WeilExplicit.healthyQw_eq_sameOwner]

end M2Width
end Dev
end Source
end ConnesWeilRH
