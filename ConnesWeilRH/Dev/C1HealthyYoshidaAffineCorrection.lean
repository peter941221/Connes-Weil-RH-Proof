import ConnesWeilRH.Dev.C1HealthyYoshidaCorrectionFamily
import ConnesWeilRH.Source.CC20YoshidaConstruction
import ConnesWeilRH.Dev.C1VariationalFiniteDimensionalSelector

/-!
# C1HealthyYoshidaAffineCorrection - linear source-family layer

The existing windowed Mellin vectors span the finite node-value space.  This
leaf packages that fact as a surjective linear map, chooses a linear right
inverse, and transports the resulting coefficient family to `CompactLogTest`.
It proves no profile sign and no RH statement.
-/

namespace ConnesWeilRH
namespace Source
namespace C1HealthyYoshidaAffineCorrection

open CC20YoshidaConvolution
open CC20YoshidaConvolution.CompactLogTest
open CCM25Concrete.CompactLogConvolution
open CCM25Concrete.SelectedYoshidaBridge
open CC20YoshidaNearZeros
open CC20YoshidaInterpolationNode
open CC20YoshidaInterpolationNode.CC20YoshidaExpandedMomentNode
open C1VariationalFiniteDimensionalSelector

noncomputable section

def WindowedPositiveIntervalCompactTest.IsUnitBounded
    (p : WindowedPositiveIntervalCompactTest a b) : Prop :=
  ∀ x : Real,
    ‖normalizedCC20ConcreteTestAlgebra.legacy.encode p.1.test x‖ ≤ 1

abbrev UnitBoundedWindowedPositiveIntervalCompactTest (a b : Real) :=
  {p : WindowedPositiveIntervalCompactTest a b //
    WindowedPositiveIntervalCompactTest.IsUnitBounded p}

noncomputable def unitBoundedWindowedFiniteMellinVector
    (nodes : Finset Complex) (a b : Real)
    (p : UnitBoundedWindowedPositiveIntervalCompactTest a b) :
    FiniteMellinNode nodes → Complex :=
  windowedFiniteMellinVector nodes a b p.1

theorem unitBoundedWindowedFiniteMellinVector_span_top
    (nodes : Finset Complex) (a b : Real)
    (ha : 0 < a) (ha_one : a < 1) (hone_b : 1 < b) :
    Submodule.span Complex
        (Set.range (unitBoundedWindowedFiniteMellinVector nodes a b)) = ⊤ := by
  classical
  have hsep :
      ∀ L : (FiniteMellinNode nodes → Complex) →ₗ[Complex] Complex,
        L ≠ 0 →
          ∃ p : UnitBoundedWindowedPositiveIntervalCompactTest a b,
            L (unitBoundedWindowedFiniteMellinVector nodes a b p) ≠ 0 := by
    intro L hL
    let coeff := finiteLinearFunctionalCoordinates L
    have hcoeff : coeff ≠ 0 :=
      finiteLinearFunctionalCoordinates_ne_zero hL
    rcases exists_windowed_test_with_finite_kernel_integral_ne_zero
        nodes ha ha_one hone_b coeff hcoeff with
      ⟨p, hsupp, hnonneg, hupper, him, hintegral⟩
    let windowed : WindowedPositiveIntervalCompactTest a b := ⟨p, hsupp⟩
    have hbound : WindowedPositiveIntervalCompactTest.IsUnitBounded windowed := by
      intro x
      have hx :
          normalizedCC20ConcreteTestAlgebra.legacy.encode p.test x =
            ((normalizedCC20ConcreteTestAlgebra.legacy.encode p.test x).re : Complex) := by
        apply Complex.ext
        · simp
        · simp [him x]
      rw [hx, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (hnonneg x)]
      exact hupper x
    let bounded : UnitBoundedWindowedPositiveIntervalCompactTest a b :=
      ⟨windowed, hbound⟩
    refine ⟨bounded, ?_⟩
    rw [finiteLinearFunctional_apply_eq_sum_coordinates]
    change
      (∑ z : FiniteMellinNode nodes,
        finiteMellinVector nodes p z * coeff z) ≠ 0
    rw [finite_mellin_sum_eq_kernel_integral]
    exact hintegral
  by_contra htop
  let P : Submodule Complex (FiniteMellinNode nodes → Complex) :=
    Submodule.span Complex
      (Set.range (unitBoundedWindowedFiniteMellinVector nodes a b))
  have hproper : P < ⊤ := (show P ≠ ⊤ from htop).lt_top
  rcases Submodule.exists_le_ker_of_lt_top P hproper with
    ⟨L, hL_ne, hP_le_ker⟩
  rcases hsep L hL_ne with ⟨p, hp⟩
  have hp_mem : unitBoundedWindowedFiniteMellinVector nodes a b p ∈ P :=
    Submodule.subset_span (Set.mem_range_self p)
  exact hp (hP_le_ker hp_mem)

theorem exists_unitBounded_target_vector_sparse_coefficients
    (nodes : Finset Complex) (a b : Real)
    (ha : 0 < a) (ha_one : a < 1) (hone_b : 1 < b)
    (y : FiniteMellinNode nodes → Complex) :
    ∃ d : (FiniteMellinNode nodes → Complex) →₀ Complex,
      d.support.card ≤ nodes.card ∧
      (↑d.support : Set (FiniteMellinNode nodes → Complex)) ⊆
        Set.range (unitBoundedWindowedFiniteMellinVector nodes a b) ∧
      d.sum (fun v r => r • v) = y := by
  have hspan := unitBoundedWindowedFiniteMellinVector_span_top
    nodes a b ha ha_one hone_b
  have hy_mem : y ∈ Submodule.span Complex
      (Set.range (unitBoundedWindowedFiniteMellinVector nodes a b)) := by
    rw [hspan]
    exact Submodule.mem_top
  rcases Submodule.mem_span_set_iff_exists_finsupp_le_finrank.mp hy_mem with
    ⟨d, hcard, hsupport, hsum⟩
  refine ⟨d, ?_, hsupport, hsum⟩
  rw [hspan] at hcard
  simpa using hcard

theorem exists_unitBounded_source_sparse_coefficients
    (nodes : Finset Complex) (a b : Real)
    (ha : 0 < a) (ha_one : a < 1) (hone_b : 1 < b)
    (y : FiniteMellinNode nodes → Complex) :
    ∃ c : WindowedPositiveIntervalCompactTest a b →₀ Complex,
      c.support.card ≤ nodes.card ∧
      (∀ z : FiniteMellinNode nodes,
        c.sum (fun p coefficient =>
          coefficient * windowedFiniteMellinVector nodes a b p z) = y z) ∧
      ∀ p ∈ c.support,
        ∃ q : UnitBoundedWindowedPositiveIntervalCompactTest a b,
          q.1.1 = p ∧ WindowedPositiveIntervalCompactTest.IsUnitBounded q.1 := by
  classical
  obtain ⟨d, hdcard, hdsource, hdsum⟩ :=
    exists_unitBounded_target_vector_sparse_coefficients
      nodes a b ha ha_one hone_b y
  let α := d.support
  let p : α → UnitBoundedWindowedPositiveIntervalCompactTest a b := fun v =>
    Classical.choose (hdsource v.property)
  have hp : ∀ v : α,
      unitBoundedWindowedFiniteMellinVector nodes a b (p v) =
        (v : FiniteMellinNode nodes → Complex) := by
    intro v
    exact Classical.choose_spec (hdsource v.property)
  have hp_inj : Function.Injective p := by
    intro v w hpvw
    apply Subtype.ext
    calc
      (v : FiniteMellinNode nodes → Complex) =
          unitBoundedWindowedFiniteMellinVector nodes a b (p v) := (hp v).symm
      _ = unitBoundedWindowedFiniteMellinVector nodes a b (p w) := by rw [hpvw]
      _ = (w : FiniteMellinNode nodes → Complex) := hp w
  let e : α ↪ UnitBoundedWindowedPositiveIntervalCompactTest a b :=
    ⟨p, hp_inj⟩
  have hf_bij : Set.BijOn (fun v : α => (v : FiniteMellinNode nodes → Complex))
      ((fun v : α => (v : FiniteMellinNode nodes → Complex)) ⁻¹'
        (↑d.support : Set (FiniteMellinNode nodes → Complex)))
      (↑d.support : Set (FiniteMellinNode nodes → Complex)) := by
    refine ⟨?_, ?_, ?_⟩
    · intro v hv
      exact v.property
    · intro v hv w hw hvw
      exact Subtype.ext hvw
    · intro v hv
      exact ⟨⟨v, hv⟩, hv, rfl⟩
  let l : α →₀ Complex :=
    Finsupp.comapDomain (fun v : α => (v : FiniteMellinNode nodes → Complex)) d
      hf_bij.injOn
  let cb : UnitBoundedWindowedPositiveIntervalCompactTest a b →₀ Complex :=
    Finsupp.embDomain e l
  let s : UnitBoundedWindowedPositiveIntervalCompactTest a b ↪
      WindowedPositiveIntervalCompactTest a b := Function.Embedding.subtype _
  let c : WindowedPositiveIntervalCompactTest a b →₀ Complex :=
    cb.mapDomain s
  have hlcard : l.support.card = d.support.card := by
    change (d.support.preimage (fun v : α => (v : FiniteMellinNode nodes → Complex))
      hf_bij.injOn).card = d.support.card
    rw [Finset.card_preimage _ _ hf_bij.injOn]
    have hfilter : {x ∈ d.support | x ∈ Set.range
        (fun v : α => (v : FiniteMellinNode nodes → Complex))} = d.support := by
      ext x
      simp only [Finset.mem_filter]
      constructor
      · intro hx
        exact hx.1
      · intro hx
        exact ⟨hx, ⟨⟨x, hx⟩, rfl⟩⟩
    rw [hfilter]
  have hcbcard : cb.support.card = l.support.card := by
    dsimp [cb]
    simpa using (Finset.card_map (s := l.support) e)
  have hccard : c.support.card = cb.support.card := by
    dsimp [c]
    rw [Finsupp.mapDomain_support_of_injective s.injective]
    exact Finset.card_image_of_injective cb.support s.injective
  refine ⟨c, ?_, ?_, ?_⟩
  · rw [hccard, hcbcard, hlcard]
    exact hdcard
  · intro z
    dsimp [c]
    rw [Finsupp.sum_mapDomain_index_inj s.injective]
    dsimp [cb]
    rw [Finsupp.embDomain_eq_mapDomain,
      Finsupp.sum_mapDomain_index_inj e.injective]
    have htransport :=
      Finsupp.sum_comapDomain
        (fun v : α => (v : FiniteMellinNode nodes → Complex)) d
        (fun v coefficient => coefficient • v) hf_bij
    have htransport_z := congrArg (fun q => q z) htransport
    have hsource_to_target :
        l.sum (fun v coefficient =>
          coefficient * windowedFiniteMellinVector nodes a b (e v).1 z) =
          l.sum (fun v coefficient => (coefficient • (v : FiniteMellinNode nodes → Complex)) z) := by
      refine Finsupp.sum_congr ?_
      intro v coefficient
      change l v * windowedFiniteMellinVector nodes a b (p v).1 z =
        (l v • (v : FiniteMellinNode nodes → Complex)) z
      rw [show windowedFiniteMellinVector nodes a b (p v).1 =
          unitBoundedWindowedFiniteMellinVector nodes a b (p v) from rfl, hp]
      simp [smul_eq_mul]
    have htransport_z' :
        l.sum (fun v coefficient => (coefficient • (v : FiniteMellinNode nodes → Complex)) z) =
          d.sum (fun v coefficient => (coefficient • v) z) := by
      simpa [l, α, Finsupp.sum, smul_eq_mul, Function.comp_def] using htransport_z
    calc
      l.sum (fun v coefficient =>
          coefficient * windowedFiniteMellinVector nodes a b (e v).1 z) =
          l.sum (fun v coefficient => (coefficient • (v : FiniteMellinNode nodes → Complex)) z) :=
        hsource_to_target
      _ = d.sum (fun v coefficient => (coefficient • v) z) := htransport_z'
      _ = y z := by
        simpa only [Finsupp.sum_apply'] using congrArg (fun q => q z) hdsum
  · intro q hq
    have hmem : q ∈ cb.support.map s := by
      simpa [c, Finsupp.mapDomain_support_of_injective s.injective] using hq
    rcases Finset.mem_map.mp hmem with ⟨r, hr, rfl⟩
    exact ⟨r, rfl, r.2⟩

/-- The finite-node evaluation map on finitely supported windowed test
combinations. -/
noncomputable def windowedMellinEvaluationMap
    (nodes : Finset Complex) (a b : Real)
    (ha : 0 < a) (ha_one : a < 1) (hone_b : 1 < b) :
    (WindowedPositiveIntervalCompactTest a b →₀ Complex) →ₗ[Complex]
      (FiniteMellinNode nodes → Complex) :=
  Finsupp.lsum Complex (fun p =>
    LinearMap.toSpanSingleton Complex (FiniteMellinNode nodes → Complex)
      (windowedFiniteMellinVector nodes a b p))

@[simp] theorem windowedMellinEvaluationMap_apply
    (nodes : Finset Complex) (a b : Real)
    (ha : 0 < a) (ha_one : a < 1) (hone_b : 1 < b)
    (c : WindowedPositiveIntervalCompactTest a b →₀ Complex)
    (z : FiniteMellinNode nodes) :
    windowedMellinEvaluationMap nodes a b ha ha_one hone_b c z =
      c.sum (fun p coefficient =>
        coefficient * windowedFiniteMellinVector nodes a b p z) := by
  simp only [windowedMellinEvaluationMap, Finsupp.lsum_apply,
    Finsupp.sum, LinearMap.toSpanSingleton, LinearMap.coe_smulRight,
    LinearMap.id_coe, id_eq, Finset.sum_apply, smul_eq_mul, Pi.smul_apply]

theorem exists_unitBounded_source_sparse_coefficients_evaluation
    (nodes : Finset Complex) (a b : Real)
    (ha : 0 < a) (ha_one : a < 1) (hone_b : 1 < b)
    (y : FiniteMellinNode nodes → Complex) :
    ∃ c : WindowedPositiveIntervalCompactTest a b →₀ Complex,
      c.support.card ≤ nodes.card ∧
      windowedMellinEvaluationMap nodes a b ha ha_one hone_b c = y ∧
      ∀ p ∈ c.support,
        ∃ q : UnitBoundedWindowedPositiveIntervalCompactTest a b,
          q.1.1 = p ∧ WindowedPositiveIntervalCompactTest.IsUnitBounded q.1 := by
  obtain ⟨c, hcard, hcoords, hbounded⟩ :=
    exists_unitBounded_source_sparse_coefficients nodes a b ha ha_one hone_b y
  refine ⟨c, hcard, ?_, hbounded⟩
  funext z
  rw [windowedMellinEvaluationMap_apply]
  exact hcoords z

noncomputable def sparseUnitBoundedWindowedMellinCorrection
    (nodes : Finset Complex) (a b : Real)
    (ha : 0 < a) (ha_one : a < 1) (hone_b : 1 < b)
    (y : FiniteMellinNode nodes → Complex) :
    WindowedPositiveIntervalCompactTest a b →₀ Complex :=
  Classical.choose
    (exists_unitBounded_source_sparse_coefficients_evaluation
      nodes a b ha ha_one hone_b y)

theorem sparseUnitBoundedWindowedMellinCorrection_support_card
    (nodes : Finset Complex) (a b : Real)
    (ha : 0 < a) (ha_one : a < 1) (hone_b : 1 < b)
    (y : FiniteMellinNode nodes → Complex) :
    (sparseUnitBoundedWindowedMellinCorrection nodes a b ha ha_one hone_b y).support.card ≤
      nodes.card := by
  exact (Classical.choose_spec
    (exists_unitBounded_source_sparse_coefficients_evaluation
      nodes a b ha ha_one hone_b y)).1

theorem sparseUnitBoundedWindowedMellinCorrection_evaluation
    (nodes : Finset Complex) (a b : Real)
    (ha : 0 < a) (ha_one : a < 1) (hone_b : 1 < b)
    (y : FiniteMellinNode nodes → Complex) :
    windowedMellinEvaluationMap nodes a b ha ha_one hone_b
        (sparseUnitBoundedWindowedMellinCorrection nodes a b ha ha_one hone_b y) = y := by
  exact (Classical.choose_spec
    (exists_unitBounded_source_sparse_coefficients_evaluation
      nodes a b ha ha_one hone_b y)).2.1

theorem sparseUnitBoundedWindowedMellinCorrection_source_bound
    (nodes : Finset Complex) (a b : Real)
    (ha : 0 < a) (ha_one : a < 1) (hone_b : 1 < b)
    (y : FiniteMellinNode nodes → Complex) :
    ∀ p ∈ (sparseUnitBoundedWindowedMellinCorrection nodes a b ha ha_one hone_b y).support,
      ∃ q : UnitBoundedWindowedPositiveIntervalCompactTest a b,
        q.1.1 = p ∧ WindowedPositiveIntervalCompactTest.IsUnitBounded q.1 := by
  exact (Classical.choose_spec
    (exists_unitBounded_source_sparse_coefficients_evaluation
      nodes a b ha ha_one hone_b y)).2.2

theorem windowedMellinEvaluationMap_surjective
    (nodes : Finset Complex) (a b : Real)
    (ha : 0 < a) (ha_one : a < 1) (hone_b : 1 < b) :
    Function.Surjective
      (windowedMellinEvaluationMap nodes a b ha ha_one hone_b) := by
  intro y
  have hspan := windowedFiniteMellinVector_span_top nodes ha ha_one hone_b
  have hy_mem : y ∈ Submodule.span Complex
      (Set.range (windowedFiniteMellinVector nodes a b)) := by
    rw [hspan]
    exact Submodule.mem_top
  rcases Finsupp.mem_span_range_iff_exists_finsupp.mp hy_mem with
    ⟨c, hc⟩
  refine ⟨c, ?_⟩
  funext z
  rw [windowedMellinEvaluationMap_apply]
  have hpoint := congr_fun hc z
  simpa [Finsupp.sum, Pi.smul_apply, smul_eq_mul] using hpoint

/-! The finite-dimensional reduction is stated first on target vectors.  The
support subset records that every selected vector still comes from a genuine
windowed test; a later adapter may choose one source preimage per vector. -/
theorem exists_windowedMellin_target_vector_sparse_coefficients
    (nodes : Finset Complex) (a b : Real)
    (ha : 0 < a) (ha_one : a < 1) (hone_b : 1 < b)
    (y : FiniteMellinNode nodes → Complex) :
    ∃ d : (FiniteMellinNode nodes → Complex) →₀ Complex,
      d.support.card ≤ nodes.card ∧
      (↑d.support : Set (FiniteMellinNode nodes → Complex)) ⊆
        Set.range (windowedFiniteMellinVector nodes a b) ∧
      d.sum (fun v r => r • v) = y := by
  have hspan := windowedFiniteMellinVector_span_top nodes ha ha_one hone_b
  have hy_mem : y ∈ Submodule.span Complex
      (Set.range (windowedFiniteMellinVector nodes a b)) := by
    rw [hspan]
    exact Submodule.mem_top
  rcases Submodule.mem_span_set_iff_exists_finsupp_le_finrank.mp hy_mem with
    ⟨d, hcard, hsupport, hsum⟩
  refine ⟨d, ?_, hsupport, hsum⟩
  rw [hspan] at hcard
  simpa using hcard

/-! Transport the target-vector certificate back to source-test indices.  One
source preimage is chosen for each selected target vector; injectivity follows
because the selected target vectors are distinct. -/
theorem exists_windowedMellin_source_sparse_coefficients
    (nodes : Finset Complex) (a b : Real)
    (ha : 0 < a) (ha_one : a < 1) (hone_b : 1 < b)
    (y : FiniteMellinNode nodes → Complex) :
    ∃ c : WindowedPositiveIntervalCompactTest a b →₀ Complex,
      c.support.card ≤ nodes.card ∧
      windowedMellinEvaluationMap nodes a b ha ha_one hone_b c = y := by
  classical
  obtain ⟨d, hdcard, hdsource, hdsum⟩ :=
    exists_windowedMellin_target_vector_sparse_coefficients
      nodes a b ha ha_one hone_b y
  let α := d.support
  let p : α → WindowedPositiveIntervalCompactTest a b := fun v =>
    Classical.choose (hdsource v.property)
  have hp : ∀ v : α,
      windowedFiniteMellinVector nodes a b (p v) = (v : FiniteMellinNode nodes → Complex) := by
    intro v
    exact Classical.choose_spec (hdsource v.property)
  have hp_inj : Function.Injective p := by
    intro v w hpvw
    apply Subtype.ext
    calc
      (v : FiniteMellinNode nodes → Complex) =
          windowedFiniteMellinVector nodes a b (p v) := (hp v).symm
      _ = windowedFiniteMellinVector nodes a b (p w) := by rw [hpvw]
      _ = (w : FiniteMellinNode nodes → Complex) := hp w
  let e : α ↪ WindowedPositiveIntervalCompactTest a b :=
    ⟨p, hp_inj⟩
  have hf_bij : Set.BijOn (fun v : α => (v : FiniteMellinNode nodes → Complex))
      ((fun v : α => (v : FiniteMellinNode nodes → Complex)) ⁻¹'
        (↑d.support : Set (FiniteMellinNode nodes → Complex)))
      (↑d.support : Set (FiniteMellinNode nodes → Complex)) := by
    refine ⟨?_, ?_, ?_⟩
    · intro v hv
      exact v.property
    · intro v hv w hw hvw
      exact Subtype.ext hvw
    · intro v hv
      exact ⟨⟨v, hv⟩, hv, rfl⟩
  let l : α →₀ Complex :=
    Finsupp.comapDomain (fun v : α => (v : FiniteMellinNode nodes → Complex)) d
      hf_bij.injOn
  let c : WindowedPositiveIntervalCompactTest a b →₀ Complex :=
    Finsupp.embDomain e l
  have hlcard : l.support.card = d.support.card := by
    change (d.support.preimage (fun v : α => (v : FiniteMellinNode nodes → Complex))
      hf_bij.injOn).card =
      d.support.card
    rw [Finset.card_preimage _ _ hf_bij.injOn]
    have hfilter : {x ∈ d.support | x ∈ Set.range
        (fun v : α => (v : FiniteMellinNode nodes → Complex))} = d.support := by
      ext x
      simp only [Finset.mem_filter]
      constructor
      · intro hx
        exact hx.1
      · intro hx
        exact ⟨hx, ⟨⟨x, hx⟩, rfl⟩⟩
    rw [hfilter]
  have hccard : c.support.card = l.support.card := by
    dsimp [c]
    simpa using (Finset.card_map e l.support)
  refine ⟨c, ?_, ?_⟩
  · rw [hccard, hlcard]
    exact hdcard
  · funext z
    rw [windowedMellinEvaluationMap_apply]
    dsimp [c]
    rw [Finsupp.embDomain_eq_mapDomain,
      Finsupp.sum_mapDomain_index_inj e.injective]
    have htransport :=
      Finsupp.sum_comapDomain
        (fun v : α => (v : FiniteMellinNode nodes → Complex)) d
        (fun v coefficient => coefficient • v) hf_bij
    have htransport_z := congrArg (fun q => q z) htransport
    have hsource_to_target :
        l.sum (fun v coefficient =>
          coefficient * windowedFiniteMellinVector nodes a b (e v) z) =
          l.sum (fun v coefficient => (coefficient • (v : FiniteMellinNode nodes → Complex)) z) := by
      refine Finsupp.sum_congr ?_
      intro v coefficient
      change l v * windowedFiniteMellinVector nodes a b (p v) z =
        (l v • (v : FiniteMellinNode nodes → Complex)) z
      rw [hp]
      simp [smul_eq_mul]
    have htransport_z' :
        l.sum (fun v coefficient => (coefficient • (v : FiniteMellinNode nodes → Complex)) z) =
          d.sum (fun v coefficient => (coefficient • v) z) := by
      simpa [l, α, Finsupp.sum, smul_eq_mul, Function.comp_def] using htransport_z
    calc
      l.sum (fun v coefficient =>
          coefficient * windowedFiniteMellinVector nodes a b (e v) z) =
          l.sum (fun v coefficient => (coefficient • (v : FiniteMellinNode nodes → Complex)) z) :=
        hsource_to_target
      _ = d.sum (fun v coefficient => (coefficient • v) z) := htransport_z'
      _ = y z := by
        simpa only [Finsupp.sum_apply'] using congrArg (fun q => q z) hdsum

/-! A named sparse source owner for later seminorm-budget consumers.  This
selector is deliberately separate from the affine right inverse: it exposes
the support bound needed by the quantitative route without changing the
existing affine producer API. -/
noncomputable def sparseWindowedMellinCorrection
    (nodes : Finset Complex) (a b : Real)
    (ha : 0 < a) (ha_one : a < 1) (hone_b : 1 < b)
    (y : FiniteMellinNode nodes → Complex) :
    WindowedPositiveIntervalCompactTest a b →₀ Complex :=
  Classical.choose
    (exists_windowedMellin_source_sparse_coefficients
      nodes a b ha ha_one hone_b y)

theorem sparseWindowedMellinCorrection_support_card
    (nodes : Finset Complex) (a b : Real)
    (ha : 0 < a) (ha_one : a < 1) (hone_b : 1 < b)
    (y : FiniteMellinNode nodes → Complex) :
    (sparseWindowedMellinCorrection nodes a b ha ha_one hone_b y).support.card ≤
      nodes.card := by
  exact (Classical.choose_spec
    (exists_windowedMellin_source_sparse_coefficients
      nodes a b ha ha_one hone_b y)).1

theorem sparseWindowedMellinCorrection_evaluation
    (nodes : Finset Complex) (a b : Real)
    (ha : 0 < a) (ha_one : a < 1) (hone_b : 1 < b)
    (y : FiniteMellinNode nodes → Complex) :
    windowedMellinEvaluationMap nodes a b ha ha_one hone_b
        (sparseWindowedMellinCorrection nodes a b ha ha_one hone_b y) = y := by
  exact (Classical.choose_spec
    (exists_windowedMellin_source_sparse_coefficients
      nodes a b ha ha_one hone_b y)).2

theorem exists_min_norm_on_sparse_source_support
    (nodes : Finset Complex) (a b : Real)
    (ha : 0 < a) (ha_one : a < 1) (hone_b : 1 < b)
    (y : FiniteMellinNode nodes → Complex)
    (c : WindowedPositiveIntervalCompactTest a b →₀ Complex)
    (hc : windowedMellinEvaluationMap nodes a b ha ha_one hone_b c = y) :
    ∃ d : EuclideanSpace Complex c.support,
      (∑ v : c.support,
        d v • windowedFiniteMellinVector nodes a b v.1) = y ∧
      ∀ e : EuclideanSpace Complex c.support,
        (∑ v : c.support,
          e v • windowedFiniteMellinVector nodes a b v.1) = y →
          ‖d‖ ≤ ‖e‖ := by
  let c₀ : EuclideanSpace Complex c.support :=
    WithLp.toLp 2 (fun v => c v.1)
  have hc₀ :
      (∑ v : c.support,
        c₀ v • windowedFiniteMellinVector nodes a b v.1) = y := by
    funext z
    have hz := congrArg (fun q => q z) hc
    change windowedMellinEvaluationMap nodes a b ha ha_one hone_b c z = y z at hz
    rw [windowedMellinEvaluationMap_apply] at hz
    have hz' :=
      (Finset.sum_attach c.support
        (fun x => c x * windowedFiniteMellinVector nodes a b x z)).trans hz
    simpa [c₀, Finsupp.sum, smul_eq_mul] using hz'
  exact exists_min_norm_euclidean_coefficient
    (fun v : c.support => windowedFiniteMellinVector nodes a b v.1) y
    ⟨c₀, hc₀⟩

/-- A linear right inverse of the finite-node evaluation map.  Its existence
uses only surjectivity and the projectivity of finite function spaces over the
field `Complex`; it does not use any sign conclusion. -/
noncomputable def windowedMellinRightInverse
    (nodes : Finset Complex) (a b : Real)
    (ha : 0 < a) (ha_one : a < 1) (hone_b : 1 < b) :
    (FiniteMellinNode nodes → Complex) →ₗ[Complex]
    (WindowedPositiveIntervalCompactTest a b →₀ Complex) :=
  Classical.choose
    (LinearMap.exists_rightInverse_of_surjective
      (windowedMellinEvaluationMap nodes a b ha ha_one hone_b)
      (LinearMap.range_eq_top.mpr
        (windowedMellinEvaluationMap_surjective nodes a b ha ha_one hone_b)))

theorem windowedMellinEvaluationMap_comp_rightInverse
    (nodes : Finset Complex) (a b : Real)
    (ha : 0 < a) (ha_one : a < 1) (hone_b : 1 < b) :
    (windowedMellinEvaluationMap nodes a b ha ha_one hone_b).comp
        (windowedMellinRightInverse nodes a b ha ha_one hone_b) =
      LinearMap.id := by
  exact Classical.choose_spec
    (LinearMap.exists_rightInverse_of_surjective
      (windowedMellinEvaluationMap nodes a b ha ha_one hone_b)
      (LinearMap.range_eq_top.mpr
        (windowedMellinEvaluationMap_surjective nodes a b ha ha_one hone_b)))

/-- The affine-family correction obtained from the linear right inverse,
written in log coordinates. -/
noncomputable def affineResidualCorrection
    (nodes : Finset Complex) {lower upper : Real}
    (hlower : lower < 0) (hupper : 0 < upper)
    (y : FiniteMellinNode nodes → Complex) : CompactLogTest :=
  let a : Real := Real.exp lower
  let b : Real := Real.exp upper
  let ha : 0 < a := Real.exp_pos lower
  let hb : 0 < b := Real.exp_pos upper
  let ha_one : a < 1 := Real.exp_lt_one_iff.mpr hlower
  let hone_b : 1 < b := Real.one_lt_exp_iff.mpr hupper
  let coeffs := windowedMellinRightInverse nodes a b ha ha_one hone_b y
  let source := windowedPositiveIntervalCompactTestCombination coeffs
  compactLogTestOfWindow source ha hb
    (windowedPositiveIntervalCompactTestCombination_support_subset coeffs)

theorem affineResidualCorrection_support_subset
    (nodes : Finset Complex) {lower upper : Real}
    (hlower : lower < 0) (hupper : 0 < upper)
    (y : FiniteMellinNode nodes → Complex) :
    Function.support (affineResidualCorrection nodes hlower hupper y).test ⊆
      Set.Ioo lower upper := by
  dsimp [affineResidualCorrection]
  simpa using
    (compactLogTestOfWindow_support_subset
      (windowedPositiveIntervalCompactTestCombination
        (windowedMellinRightInverse nodes (Real.exp lower) (Real.exp upper)
          (Real.exp_pos lower) (Real.exp_lt_one_iff.mpr hlower)
          (Real.one_lt_exp_iff.mpr hupper) y))
      (Real.exp_pos lower) (Real.exp_pos upper)
      (windowedPositiveIntervalCompactTestCombination_support_subset _))

theorem affineResidualCorrection_laplaceAt
    (nodes : Finset Complex) {lower upper : Real}
    (hlower : lower < 0) (hupper : 0 < upper)
    (y : FiniteMellinNode nodes → Complex)
    (z : FiniteMellinNode nodes) :
    laplaceAt (affineResidualCorrection nodes hlower hupper y) z.1 = y z := by
  dsimp [affineResidualCorrection]
  rw [laplaceAt_compactLogTestOfWindow_eq_mellin]
  have hbridge := windowedFiniteMellinVector_combination
    nodes
    (windowedMellinRightInverse nodes (Real.exp lower) (Real.exp upper)
      (Real.exp_pos lower) (Real.exp_lt_one_iff.mpr hlower)
      (Real.one_lt_exp_iff.mpr hupper) y)
    z
  have hright := congrArg (fun f => f z)
    (LinearMap.congr_fun
      (windowedMellinEvaluationMap_comp_rightInverse nodes
        (Real.exp lower) (Real.exp upper) (Real.exp_pos lower)
        (Real.exp_lt_one_iff.mpr hlower)
         (Real.one_lt_exp_iff.mpr hupper)) y)
  have hright' :
      (windowedMellinRightInverse nodes (Real.exp lower) (Real.exp upper)
        (Real.exp_pos lower) (Real.exp_lt_one_iff.mpr hlower)
        (Real.one_lt_exp_iff.mpr hupper) y).sum (fun p coefficient =>
          coefficient * windowedFiniteMellinVector nodes (Real.exp lower)
            (Real.exp upper) p z) = y z := by
    simpa [LinearMap.comp_apply, windowedMellinEvaluationMap_apply] using hright
  calc
    _ = normalizedCC20TestSpace.mellinAt
        (windowedPositiveIntervalCompactTestCombination
          (windowedMellinRightInverse nodes (Real.exp lower) (Real.exp upper)
            (Real.exp_pos lower) (Real.exp_lt_one_iff.mpr hlower)
            (Real.one_lt_exp_iff.mpr hupper) y)) z.1 := by
          simp only [normalizedCC20TestSpace_mellinAt_eq,
            normalizedCC20ConcreteEvaluationData_mellinAt_eq_mellin]
    _ = _ := hbridge
    _ = _ := hright'

end
end C1HealthyYoshidaAffineCorrection
end Source
end ConnesWeilRH
