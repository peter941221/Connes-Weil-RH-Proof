import ConnesWeilRH.Dev.Wall14PlateauExplicitComplex
import ConnesWeilRH.Dev.C1WeilExplicit

/-!
# M2WidthPlateau -- width-scaled plateau carrier (M.2/990 negative-psi family)

Width-parameterized counterpart of the explicit flat-top compact bump
bumpPlateauTest, so the M-2/990 sign-boundary numerics (docs/proofs/990: the healthy
psi crosses from + to - at window width 2.8175; the negative-psi family =
window width > 2.82) become expressible as a CompactLogTest with an arbitrary
support half-width w > 0, via wideBump w x = bumpEx (x / w), folding the base
bump support [-1,1] to [-w,w].  Lifts to a complex test wideTest (proving
test 0 = 1 and HasCompactSupport) and reads C1WeilExplicit.healthyQw on a
concrete negative-psi-family carrier wideC (support [-3/2, 3/2], width 3).

HONEST SCOPE (mirrors M2HealthyPsiPort; docs/990 + 989):
* makes the width-scaled (negative-psi-family) carrier and its healthyQw value
  expressible / stateable.
* NO bound (healthyQw <= 0), NO sign assertion, NO finite-vanishing.
* The {0, 1/2, 1}-vanish ortho-residual construction stays an open step, not
  part of this module.
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

/-- concrete negative-psi-family carrier: support half-width (3/2), so M2 window width 3 > 2.82. -/
noncomputable def wideW : Real := 3 / 2

lemma wideW_pos : 0 < wideW := by
  unfold wideW
  norm_num

noncomputable def wideC : CompactLogTest := wideTest wideW wideW_pos

theorem wideC_zero : wideC.test 0 = (1 : Complex) :=
  wideTest_zero wideW wideW_pos

theorem wideC_hasCompactSupport : HasCompactSupport wideC.test :=
  wideC.compactSupport

/-- healthy-psi value on the width-scaled carrier convolution square (expression only,
   the numeric pole - archimedean - finite-prime-{2} of docs/990; NO sign asserted). -/
noncomputable def widePsi : Real :=
  ConnesWeilRH.Source.C1WeilExplicit.healthyQw wideC




/-- narrow positive-psi-family carrier: support half-width (6/5), so M2 window width 12/5 = 2.4 (the positive-psi side of docs/990, boundary 2.82). -/
noncomputable def narrowW : Real := 6 / 5

lemma narrowW_pos : 0 < narrowW := by
  unfold narrowW
  norm_num

noncomputable def narrowC : CompactLogTest := wideTest narrowW narrowW_pos

theorem narrowC_zero : narrowC.test 0 = (1 : Complex) :=
  wideTest_zero narrowW narrowW_pos

theorem narrowC_hasCompactSupport : HasCompactSupport narrowC.test :=
  narrowC.compactSupport

/-- healthy-psi value on the narrow (positive-psi-family) carrier convolution square
   (expression only; NO sign asserted). -/
noncomputable def narrowPsi : Real :=
  ConnesWeilRH.Source.C1WeilExplicit.healthyQw narrowC





/-- Exact decomposition of the healthy-psi value into the genuine healthy-carrier
   components: pole - archimedean(compact term) - finite-prime-{2}.  This is the
   arithmetic handle a future real-analysis closure attaches to; it does NOT assert
   a sign or compute the (analytic, integral-valued) terms to a decimal. -/
theorem healthyQw_decomposition (c : CompactLogTest) :
    ConnesWeilRH.Source.C1WeilExplicit.healthyQw c =
      (Dev.WellFormHealthyRepoint.healthyEval.poleFunctional (c.convolutionSquare.test) -
        ConnesWeilRH.Source.CCM25Concrete.CompactLogArchimedeanLift.compactLogArchimedeanTerm
          c.convolutionSquare) -
        Dev.WellFormHealthyRepoint.healthyEval.sourceFinitePrimeTerm 2 (c.convolutionSquare.test) := by
  unfold ConnesWeilRH.Source.C1WeilExplicit.healthyQw
  unfold ConnesWeilRH.Source.C1WeilExplicit.healthyPsi
  rw [ConnesWeilRH.Source.CCM25Concrete.CompactArchTotal.totalArchimedean_eq_compact
      (c.convolutionSquare)]

/-- Specialized to the wide (negative-psi-family) carrier. -/
theorem widePsi_decomposition : widePsi =
      (Dev.WellFormHealthyRepoint.healthyEval.poleFunctional (wideC.convolutionSquare.test) -
        ConnesWeilRH.Source.CCM25Concrete.CompactLogArchimedeanLift.compactLogArchimedeanTerm
          wideC.convolutionSquare) -
        Dev.WellFormHealthyRepoint.healthyEval.sourceFinitePrimeTerm 2 (wideC.convolutionSquare.test) := by
  unfold widePsi
  exact healthyQw_decomposition wideC

/-- Specialized to the narrow (positive-psi-family) carrier. -/
theorem narrowPsi_decomposition : narrowPsi =
      (Dev.WellFormHealthyRepoint.healthyEval.poleFunctional (narrowC.convolutionSquare.test) -
        ConnesWeilRH.Source.CCM25Concrete.CompactLogArchimedeanLift.compactLogArchimedeanTerm
          narrowC.convolutionSquare) -
        Dev.WellFormHealthyRepoint.healthyEval.sourceFinitePrimeTerm 2 (narrowC.convolutionSquare.test) := by
  unfold narrowPsi
  exact healthyQw_decomposition narrowC





/-- THE BRIDGE (task-3 item 1): the healthy-psi value factors back through the wired
   healthyCC20TestSpace archimedean slot plus the pole and finite-prime corrections.
   The wired `weilLocalSum` slot holds only `-totalArchimedean` (archimedean component of
   Eq.3.7); the full healthy-psi carries the genuine pole and finite-prime-{2} terms
   (healthyEval).  Concretely:
       healthyQw c = weilLocalSum c + pole(conv.test) - prime2(conv.test),
   which is the exact algebraic seam across the powers/prime/arch split.  Axiom-clean
   (unfold healthyQw/healthyPsi, rw healthyWeilReadoff, ring).  NO sign asserted. -/
theorem healthyQw_eq_weil (c : CompactLogTest) :
    ConnesWeilRH.Source.C1WeilExplicit.healthyQw c =
      ConnesWeilRH.Source.C1.healthyCC20TestSpace.weilLocalSum c +
        Dev.WellFormHealthyRepoint.healthyEval.poleFunctional (c.convolutionSquare.test) -
        Dev.WellFormHealthyRepoint.healthyEval.sourceFinitePrimeTerm 2 (c.convolutionSquare.test) := by
  unfold ConnesWeilRH.Source.C1WeilExplicit.healthyQw
  unfold ConnesWeilRH.Source.C1WeilExplicit.healthyPsi
  rw [ConnesWeilRH.Source.C1.healthyWeilReadoff c]
  ring

end M2Width
end Dev
end Source
end ConnesWeilRH
