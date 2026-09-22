/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Dev.C1WindowTaperAssembly
import ConnesWeilRH.Dev.C1QuantitativeConsumer
import ConnesWeilRH.Dev.C1HealthyYoshidaMinimalInterpolation
import ConnesWeilRH.Dev.C1HealthyDetectorPinning

/-!
# C1RouteAlphaOwner - R1: the route-alpha owner, funded L2 budget

(N2beta component 5, discharge)

Record 1389 section 7 re-scoped the component-5 discharge onto the route-alpha
register: the four-node family `healthyDetectorNodeSet rho = {0, 1/2, 1, rho}`
whose vanishings sit on the owner itself, the ROOT pinning window
`Icc (-(log 2 / 2)) (log 2 / 2)`, and the IFF
`healthyDetectorData_iff_selectedDetectorArchimedeanGate` that collapses the
whole healthy-data package to one scalar sign.

This leaf builds the owner that items (a)-(d) of that section require — ONE
assembled `CompactLogTest` carrying simultaneously:

- the minimal healthy data: `HealthyMinimalLaplaceRealizes rho g` with the
  normalization `laplaceAt g rho = -1` (the two record-1385 taper owners are
  realized through the record-1389 value split: the xi-side factor `u` carries
  the all-ones pattern and the taper factor `f` carries the concentrated
  `(0, 0, 0, -1)` pattern, so the multiplicative value law of record 1386
  reproduces `healthyDetectorNodeTarget rho` exactly);
- the pinning support: `support g.test` inside `Icc (-(log 2 / 2)) (log 2 / 2)`,
  discharged by the single numeric side condition `Ru + Rf ≤ log 2 / 2` on the
  record-1386 summed window (1389 section 4);
- the funded budget: `compactLogL2sq g ≤ (2 * Ru) · ((1 + ε') · K_loc_u) ·
  ((1 + ε) · K_loc_f)` — the record-1379 Lemma-E quantities at the two value
  patterns on the two symmetric windows — which is the explicit `hfit`
  discharge the record-1387 consumer demanded (1388 section 0's R1 commitment,
  now on the correct 4-node register).

Deliverables, in dependency order:

- `windowGramInverse_cost_re_nonneg`: the inverse-solve cost
  `y* G⁻¹ y` is nonnegative — at the solved vector the record-1383 quadratic
  identity is a window integral of a squared modulus (this is the side fact
  that lets the record-1386 budget be multiplied through `(1 + ε) · K_loc`);
- `exists_routeAlphaOwner`: the owner — realization, normalization, pinning
  support, and closed-form budget, all on ONE `CompactLogTest`;
- `exists_routeAlphaOwner_margin_pos`: the same owner through the record-1387
  consumer — FIT and (J1) compose with the healthy-data realization on one
  owner, yielding `0 < δ / 2 - C_min · compactLogL2sq g`;
- `healthyDetectorData_of_routeAlphaOwner`: the 009 §5 item 4 wiring — the
  record-1375 promotion template consumed under the ROOT pinning lemma,
  conditional on the archimedean gate `0 < archimedeanTerm g.convolutionSquare`
  that records 1080/1081 carry as the open sign, which this leaf does NOT
  claim.

Lane discipline: FORMAL only. No archimedean-gate proof, no decay rate, no
numeric digit, no `C_min` or `δ` value, no `HealthyYoshidaDetectorData` field
is produced unconditionally, no N3/N4 input, no RH-adjacent conclusion. The
gate `harch` and the budget premises `hfit`/`hJ1` remain hypotheses; their
discharge is governed by the record-1390 prereg.

Design record: docs/map/009_n2beta_core_bone_completion_contract.md item 5;
recon record docs/proofs/1389_component5_recon_route_alpha_collapse.md.
-/

namespace ConnesWeilRH
namespace Source
namespace C1RouteAlphaOwner

open MeasureTheory
open scoped Topology
open scoped ContDiff
open CCM25Concrete.CompactLogConvolution
open CC20YoshidaConvolution.CompactLogTest
open C1CompactLogL2Export
open C1WindowMellinGram
open C1WindowMellinIndependence
open C1WindowTaperLift
open C1WindowTaperCore
open C1WindowTaperAssembly
open C1QuantitativeConsumer
open CC20YoshidaNearZeros
open CC20YoshidaConvolution
open C1HealthyYoshidaDetector
open C1HealthyYoshidaMinimalInterpolation
open C1HealthyDetectorPinning

/-! ### The route-alpha register instantiation -/

/-- The route-alpha index type: the four nodes of the register's own minimal
family, as the subtype the correction interfaces already speak.  Node
distinctness is NOT needed for this type — the Finset deduplicates — but the
interpolation wrapper needs an injective enumeration, which the subtype value
map provides unconditionally. -/
abbrev routeAlphaIndex (rho : ℂ) : Type :=
  FiniteMellinNode (healthyDetectorNodeSet rho)

/-- The node map: the subtype value, i.e. the node itself. -/
def routeAlphaNodes (rho : ℂ) : routeAlphaIndex rho → ℂ := Subtype.val

/-- The xi-side value pattern of the record-1389 split: all-ones on the four
nodes, so the assembled owner's values are exactly the taper factor's. -/
noncomputable def routeAlphaBaseValue (rho : ℂ) : routeAlphaIndex rho → ℂ :=
  fun _ => 1

/-- The minimal healthy target is pointwise either zero or minus one, hence its
sup norm is at most one. -/
theorem healthyDetectorNodeTarget_norm_le_one (rho : ℂ) :
    ‖healthyDetectorNodeTarget rho‖ ≤ 1 := by
  refine (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr ?_
  intro z
  by_cases h : z.1 = rho
  · simp [healthyDetectorNodeTarget, h]
  · simp [healthyDetectorNodeTarget, h]

/-- The route-alpha subtype has at most the four displayed nodes. -/
theorem routeAlphaIndex_card_le_four (rho : ℂ) :
    Fintype.card (routeAlphaIndex rho) ≤ 4 := by
  simpa [routeAlphaIndex, healthyDetectorNodeSet] using
    (Finset.card_le_four (a := (0 : ℂ)) (b := (1 / 2 : ℂ))
      (c := (1 : ℂ)) (d := rho))

/-- The route-alpha target contributes at most four to the conservative
cardinality-times-sup-norm budget. -/
theorem routeAlpha_target_card_norm_le_four (rho : ℂ) :
    (Fintype.card (routeAlphaIndex rho) : ℝ) *
        ‖healthyDetectorNodeTarget rho‖ ≤ 4 := by
  have hcard : (Fintype.card (routeAlphaIndex rho) : ℝ) ≤ 4 := by
    exact_mod_cast routeAlphaIndex_card_le_four rho
  have hnorm := healthyDetectorNodeTarget_norm_le_one rho
  have hcard0 : 0 ≤ (Fintype.card (routeAlphaIndex rho) : ℝ) :=
    Nat.cast_nonneg _
  nlinarith [hcard0]

/-- The real-part envelope on the route-alpha register is controlled by the
real strip of the selected zero, with no dependence on its imaginary height. -/
theorem routeAlphaRealPartBound_le_four_exp
    (rho : ℂ) (a b : ℝ) (hrho0 : 0 ≤ rho.re) (hrho1 : rho.re ≤ 1) :
    windowTaperRealPartBound a b (routeAlphaNodes rho) ≤
      4 * Real.exp (max |a| |b|) := by
  have hnode : ∀ z : routeAlphaIndex rho,
      |(routeAlphaNodes rho z).re| ≤ 1 := by
    intro z
    have hz : z.1 = 0 ∨ z.1 = (1 / 2 : ℂ) ∨ z.1 = 1 ∨ z.1 = rho := by
      simpa [routeAlphaIndex, healthyDetectorNodeSet] using z.2
    change |z.1.re| ≤ 1
    rcases hz with h | h | h | h
    · rw [h]
      simp
    · rw [h]
      norm_num
    · rw [h]
      norm_num
    · rw [h, abs_of_nonneg hrho0]
      exact hrho1
  unfold windowTaperRealPartBound
  calc
    ∑ i : routeAlphaIndex rho,
        Real.exp (|(routeAlphaNodes rho i).re| * max |a| |b|)
        ≤ ∑ i : routeAlphaIndex rho, Real.exp (1 * max |a| |b|) := by
          apply Finset.sum_le_sum
          intro i hi
          exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right
            (hnode i) (by positivity))
    _ = (Fintype.card (routeAlphaIndex rho) : ℝ) *
        Real.exp (max |a| |b|) := by
          simp [Finset.sum_const, Finset.card_univ]
    _ ≤ 4 * Real.exp (max |a| |b|) := by
          exact mul_le_mul_of_nonneg_right
            (by exact_mod_cast routeAlphaIndex_card_le_four rho)
            (Real.exp_pos _).le

/-- The same envelope bound with the strip hypotheses supplied by the actual
source-zero owner. -/
theorem routeAlphaRealPartBound_le_four_exp_of_sourceNontrivialZero
    (rho : ℂ)
    (hrho : RHDefinitionBridge.standard.sourceNontrivialZero rho)
    (a b : ℝ) :
    windowTaperRealPartBound a b (routeAlphaNodes rho) ≤
      4 * Real.exp (max |a| |b|) := by
  exact routeAlphaRealPartBound_le_four_exp rho a b
    (sourceNontrivialZero_zero_lt_re hrho).le
    (sourceNontrivialZero_re_lt_one hrho).le

/-- The current real-part strict-budget shape cannot fit a route-alpha owner
on an interval of length at most one: the zero-node Gram upper ceiling forces
`alpha <= b - a`, while the target and nonempty index already force the budget
to demand `alpha > 2`. -/
theorem routeAlpha_realPart_gap_budget_impossible_of_interval_length_le_one
    (rho : ℂ) {a b : ℝ} (hab : a < b) (hwidth : b - a ≤ 1)
    (τ : ℝ → ℝ) (hτc : Continuous τ) (hτ1 : ∀ x, τ x ≤ 1)
    (α : ℝ)
    (hgap : ∀ v : routeAlphaIndex rho → ℂ, α * ‖v‖ ^ 2 ≤
      (dotProduct (star v)
        (Matrix.mulVec
          (windowTaperGramMatrix a b (fun x => (τ x : ℂ))
            (routeAlphaNodes rho)) v)).re)
    (hbudget : 2 * ((Fintype.card (routeAlphaIndex rho) : ℝ) *
        ‖healthyDetectorNodeTarget rho‖ *
          windowTaperRealPartBound a b (routeAlphaNodes rho)) < α) :
    False := by
  let i₀ : routeAlphaIndex rho :=
    ⟨(0 : ℂ), by simp [healthyDetectorNodeSet]⟩
  letI : Nonempty (routeAlphaIndex rho) := ⟨i₀⟩
  have hgapUpper : α ≤ b - a :=
    windowTaperGram_gap_le_interval_length_of_zero_node hab τ hτc hτ1
      (routeAlphaNodes rho) i₀ (by simp [routeAlphaNodes, i₀]) α hgap
  have hcard : (1 : ℝ) ≤ Fintype.card (routeAlphaIndex rho) := by
    have hpos : 0 < Fintype.card (routeAlphaIndex rho) :=
      Fintype.card_pos_iff.mpr inferInstance
    exact_mod_cast hpos
  let irho : routeAlphaIndex rho :=
    ⟨rho, by simp [healthyDetectorNodeSet]⟩
  have htarget : (1 : ℝ) ≤ ‖healthyDetectorNodeTarget rho‖ := by
    have hpoint : ‖healthyDetectorNodeTarget rho irho‖ = 1 := by
      simp [healthyDetectorNodeTarget, irho]
    have hpoint_le :=
      norm_le_pi_norm (f := healthyDetectorNodeTarget rho) irho
    rw [hpoint] at hpoint_le
    exact hpoint_le
  have hbound : (1 : ℝ) ≤ windowTaperRealPartBound a b
      (routeAlphaNodes rho) := by
    unfold windowTaperRealPartBound
    have hterm : (1 : ℝ) ≤
        Real.exp (|(routeAlphaNodes rho i₀).re| * max |a| |b|) := by
      apply Real.one_le_exp
      positivity
    exact hterm.trans (Finset.single_le_sum (s := (Finset.univ :
      Finset (routeAlphaIndex rho))) (f := fun i =>
        Real.exp (|(routeAlphaNodes rho i).re| * max |a| |b|))
      (fun i _ => (Real.exp_pos _).le) (Finset.mem_univ i₀))
  have hcardNorm : (1 : ℝ) ≤
      (Fintype.card (routeAlphaIndex rho) : ℝ) *
        ‖healthyDetectorNodeTarget rho‖ := by
    simpa using (mul_le_mul hcard htarget (by norm_num) (by positivity))
  have hprod : (1 : ℝ) ≤
      (Fintype.card (routeAlphaIndex rho) : ℝ) *
        ‖healthyDetectorNodeTarget rho‖ *
          windowTaperRealPartBound a b (routeAlphaNodes rho) := by
    simpa using (mul_le_mul hcardNorm hbound (by positivity) (by positivity))
  have htwo : (2 : ℝ) ≤ 2 * ((Fintype.card (routeAlphaIndex rho) : ℝ) *
      ‖healthyDetectorNodeTarget rho‖ *
        windowTaperRealPartBound a b (routeAlphaNodes rho)) := by
    nlinarith
  have hgt : (2 : ℝ) < α := lt_of_le_of_lt htwo hbudget
  linarith

instance routeAlphaIndex_nonempty (rho : ℂ) :
    Nonempty (routeAlphaIndex rho) :=
  ⟨⟨(0 : ℂ), by simp [healthyDetectorNodeSet]⟩⟩

/-! ### The nonnegativity side fact -/

/-- The inverse-solve cost is nonnegative.  At the solved vector `coeff = G⁻¹ y`
the record-1383 quadratic identity reads `(star coeff) ⬝ᵥ y` as the window
integral of a squared modulus, and taking real parts (via `congrArg`) already
presents the right-hand side as the real window integral, which is
nonnegative.  The solve `G (G⁻¹ y) = y` is record 1384's pinned
`Matrix.mulVec_mulVec` computation.  This is the side fact that lets the
record-1386 factorized budget be multiplied through `(1 + ε) · K_loc` in the
R1 chain. -/
theorem windowGramInverse_cost_re_nonneg {ι : Type*} [Fintype ι]
    [DecidableEq ι] {a b : ℝ}
    (hab : a < b) (nodes : ι → ℂ) (hne : Function.Injective nodes) (y : ι → ℂ) :
    0 ≤ (dotProduct (star (Matrix.mulVec
        ↑(windowExpGramMatrix_isUnit_of_injective hab nodes hne).unit⁻¹
        y)) y).re := by
  classical
  let G := windowExpGramMatrix a b nodes
  let hG := windowExpGramMatrix_isUnit_of_injective hab nodes hne
  have hsolve : Matrix.mulVec G (Matrix.mulVec (↑hG.unit⁻¹ : Matrix ι ι ℂ) y) =
      y := by
    calc Matrix.mulVec G (Matrix.mulVec (↑hG.unit⁻¹ : Matrix ι ι ℂ) y)
        = Matrix.mulVec (G * (↑hG.unit⁻¹ : Matrix ι ι ℂ)) y :=
            -- 1384's pin: explicit matrix arguments; the stated direction is
            -- `M.mulVec (N.mulVec v) = (M * N).mulVec v` (no `.symm`).
            Matrix.mulVec_mulVec y G (↑hG.unit⁻¹ : Matrix ι ι ℂ)
      _ = Matrix.mulVec (1 : Matrix ι ι ℂ) y := by rw [hG.mul_val_inv]
      _ = y := Matrix.one_mulVec y
  have hqz : (∫ x : ℝ in a..b, ‖∑ i : ι,
        Matrix.mulVec (↑hG.unit⁻¹ : Matrix ι ι ℂ) y i
        * Complex.exp (star (nodes i) * (x : ℂ))‖ ^ 2 ∂volume : ℂ)
      = dotProduct (star (Matrix.mulVec (↑hG.unit⁻¹ : Matrix ι ι ℂ) y)) y := by
    have := windowExpGram_quadratic_eq_integral a b nodes
      (Matrix.mulVec (↑hG.unit⁻¹ : Matrix ι ι ℂ) y)
    rw [hsolve] at this
    exact this
  -- 1385's working idiom: orient the quadratic identity integral = dot, rewrite
  -- the dot away, then collapse the squared-modulus integral's real part with
  -- `integral_norm_sq_re` (matching `↑(‖W x‖ ^ 2)` up to `ofReal_pow` defeq).
  rw [← hqz, integral_norm_sq_re]
  refine intervalIntegral.integral_nonneg hab.le ?_
  intro x _
  exact sq_nonneg _

/-! ### The R1 owner -/

/-- R1 (record 1389 section 7, items a-d): ONE compact-log owner on the
route-alpha register.  Under the numeric pinning side condition
`Ru + Rf ≤ log 2 / 2`, the record-1385/1386 assembly of the all-ones xi-side
taper owner with the concentrated `(0, 0, 0, -1)` taper owner realizes the
minimal healthy data (`HealthyMinimalLaplaceRealizes` with the normalization
`laplaceAt g rho = -1`), sits in the pinning window, and pays at most the
closed-form factorized budget `(2 * Ru) · ((1 + ε') · K_loc_u) · ((1 + ε) ·
K_loc_f)`.  The budget right-hand side is spelled exactly in the record-1387
`hfit` template shape so the consumer chains by plain `le_trans` (1387's
byte-identical mirroring law). -/
theorem exists_routeAlphaOwner
    (rho : ℂ)
    (hrho : RHDefinitionBridge.standard.sourceNontrivialZero rho)
    (hoff : rho.re ≠ 1 / 2)
    {Rf Ru : ℝ} (hRf : 0 < Rf) (hRu : 0 < Ru)
    (hsum : Ru + Rf ≤ Real.log 2 / 2)
    {ε ε' : ℝ} (hε : 0 < ε) (hε' : 0 < ε') :
    ∃ g : CompactLogTest,
      HealthyMinimalLaplaceRealizes rho g ∧
        laplaceAt g rho = -1 ∧
        Function.support g.test ⊆
          Set.Icc (-(Real.log 2 / 2)) (Real.log 2 / 2) ∧
        compactLogL2sq g ≤ (2 * Ru)
          * ((1 + ε') * (dotProduct (star (Matrix.mulVec
              ↑(windowExpGramMatrix_isUnit_of_injective (neg_lt_self hRu)
                (routeAlphaNodes rho) Subtype.coe_injective).unit⁻¹
              (routeAlphaBaseValue rho))) (routeAlphaBaseValue rho)).re)
          * ((1 + ε) * (dotProduct (star (Matrix.mulVec
              ↑(windowExpGramMatrix_isUnit_of_injective (neg_lt_self hRf)
                (routeAlphaNodes rho) Subtype.coe_injective).unit⁻¹
              (healthyDetectorNodeTarget rho)))
              (healthyDetectorNodeTarget rho)).re) := by
  -- (a) the two record-1385 taper owners, one per value pattern.
  obtain ⟨u, husupp, huval, hucost⟩ :=
    exists_windowTaperCorrection_cost_le_one_plus_eps (neg_lt_self hRu)
      (routeAlphaNodes rho) Subtype.coe_injective (routeAlphaBaseValue rho) hε'
  obtain ⟨g, hgsupp, hgval, hgcost⟩ :=
    exists_assembledOwner_cost_le (neg_lt_self hRf) (neg_lt_self hRu)
      (routeAlphaNodes rho) Subtype.coe_injective
      (healthyDetectorNodeTarget rho) u husupp hε
  -- (b) the multiplicative value law reproduces the register's target.
  have hvalues : ∀ z : FiniteMellinNode (healthyDetectorNodeSet rho),
      laplaceAt g z.1 = healthyDetectorNodeTarget rho z := by
    intro z
    have h1 := hgval z
    have h2 := huval z
    simp only [routeAlphaNodes, routeAlphaBaseValue] at h1 h2 ⊢
    rw [h2, one_mul] at h1
    exact h1
  have hreal : HealthyMinimalLaplaceRealizes rho g :=
    healthyMinimalLaplaceRealizes_of_node_values hrho hoff hvalues
  have hrhoval : laplaceAt g rho = -1 := by
    have h := hvalues (⟨rho, by simp [healthyDetectorNodeSet]⟩ :
      FiniteMellinNode (healthyDetectorNodeSet rho))
    simpa [healthyDetectorNodeTarget] using h
  -- (c) the summed window lands inside the pinning window under `hsum`.
  rw [show ((-Ru) + (-Rf) : ℝ) = -(Ru + Rf) by ring] at hgsupp
  have hsumL : -(Real.log 2 / 2) ≤ -(Ru + Rf) := by linarith
  have hsupp : Function.support g.test ⊆
      Set.Icc (-(Real.log 2 / 2)) (Real.log 2 / 2) := by
    refine Set.Subset.trans hgsupp ?_
    refine Set.Subset.trans Set.Ioo_subset_Icc_self ?_
    exact Set.Icc_subset_Icc hsumL hsum
  -- (d) the closed-form budget: multiply the two funded cost bounds.
  have h2Ru : (Ru : ℝ) - -Ru = 2 * Ru := by ring
  rw [h2Ru] at hgcost
  have hW0 : (0 : ℝ) ≤ 2 * Ru := by linarith
  have hEf : 0 ≤ (1 + ε) * (dotProduct (star (Matrix.mulVec
        ↑(windowExpGramMatrix_isUnit_of_injective (neg_lt_self hRf)
          (routeAlphaNodes rho) Subtype.coe_injective).unit⁻¹
        (healthyDetectorNodeTarget rho)))
        (healthyDetectorNodeTarget rho)).re :=
    mul_nonneg (by linarith : (0 : ℝ) ≤ 1 + ε)
      (windowGramInverse_cost_re_nonneg (neg_lt_self hRf)
        (routeAlphaNodes rho) Subtype.coe_injective
        (healthyDetectorNodeTarget rho))
  have hstep1 : (2 * Ru) * compactLogL2sq u ≤
      (2 * Ru) * ((1 + ε') * (dotProduct (star (Matrix.mulVec
          ↑(windowExpGramMatrix_isUnit_of_injective (neg_lt_self hRu)
            (routeAlphaNodes rho) Subtype.coe_injective).unit⁻¹
          (routeAlphaBaseValue rho))) (routeAlphaBaseValue rho)).re) :=
    mul_le_mul_of_nonneg_left hucost hW0
  have hstep2 : (2 * Ru) * compactLogL2sq u * ((1 + ε) * (dotProduct (star
          (Matrix.mulVec
            ↑(windowExpGramMatrix_isUnit_of_injective (neg_lt_self hRf)
              (routeAlphaNodes rho) Subtype.coe_injective).unit⁻¹
            (healthyDetectorNodeTarget rho)))
            (healthyDetectorNodeTarget rho)).re) ≤
      (2 * Ru) * ((1 + ε') * (dotProduct (star (Matrix.mulVec
          ↑(windowExpGramMatrix_isUnit_of_injective (neg_lt_self hRu)
            (routeAlphaNodes rho) Subtype.coe_injective).unit⁻¹
          (routeAlphaBaseValue rho))) (routeAlphaBaseValue rho)).re)
        * ((1 + ε) * (dotProduct (star (Matrix.mulVec
            ↑(windowExpGramMatrix_isUnit_of_injective (neg_lt_self hRf)
              (routeAlphaNodes rho) Subtype.coe_injective).unit⁻¹
            (healthyDetectorNodeTarget rho)))
            (healthyDetectorNodeTarget rho)).re) :=
    mul_le_mul_of_nonneg_right hstep1 hEf
  exact ⟨g, hreal, hrhoval, hsupp, le_trans hgcost hstep2⟩

/-- 009 §5 items 2-3 composed on one owner: the record-1387 margin consumer
`margin_pos_of_owner_cost_fits` applied to the R1 owner's funded budget — if
the closed-form ceiling fits (`hfit`, now an assumption about real numbers to
be confirmed by the record-1390 rig) and obeys (J1), the SAME owner that
carries the minimal healthy data and the pinning support also carries the
strictly positive local-mass margin `0 < δ / 2 - C_min · compactLogL2sq g`.
-/
theorem exists_routeAlphaOwner_margin_pos
    (rho : ℂ)
    (hrho : RHDefinitionBridge.standard.sourceNontrivialZero rho)
    (hoff : rho.re ≠ 1 / 2)
    {Rf Ru : ℝ} (hRf : 0 < Rf) (hRu : 0 < Ru)
    (hsum : Ru + Rf ≤ Real.log 2 / 2)
    {ε ε' : ℝ} (hε : 0 < ε) (hε' : 0 < ε')
    {δ Cmin ceiling : ℝ} (hC : 0 < Cmin)
    (hfit : (2 * Ru)
        * ((1 + ε') * (dotProduct (star (Matrix.mulVec
            ↑(windowExpGramMatrix_isUnit_of_injective (neg_lt_self hRu)
              (routeAlphaNodes rho) Subtype.coe_injective).unit⁻¹
            (routeAlphaBaseValue rho))) (routeAlphaBaseValue rho)).re)
        * ((1 + ε) * (dotProduct (star (Matrix.mulVec
            ↑(windowExpGramMatrix_isUnit_of_injective (neg_lt_self hRf)
              (routeAlphaNodes rho) Subtype.coe_injective).unit⁻¹
            (healthyDetectorNodeTarget rho)))
            (healthyDetectorNodeTarget rho)).re) ≤ ceiling)
    (hJ1 : ceiling < δ / (2 * Cmin)) :
    ∃ g : CompactLogTest,
      HealthyMinimalLaplaceRealizes rho g ∧
        laplaceAt g rho = -1 ∧
        Function.support g.test ⊆
          Set.Icc (-(Real.log 2 / 2)) (Real.log 2 / 2) ∧
        0 < δ / 2 - Cmin * compactLogL2sq g := by
  obtain ⟨g, hreal, hrhoval, hsupp, hcost⟩ :=
    exists_routeAlphaOwner rho hrho hoff hRf hRu hsum hε hε'
  exact ⟨g, hreal, hrhoval, hsupp,
    margin_pos_of_owner_cost_fits hC g (le_trans hcost hfit) hJ1⟩

/-! ### The gate-conditional healthy-data wiring (009 §5 item 4) -/

/-- The wiring, conditional on the gate: the record-1375 promotion template
consumed through the ROOT pinning lemma
`convolutionSquare_support_logTwo_of_rootSupport_logTwoHalf`.  The hypothesis
`harch` is the open sign that records 1080/1081 carry
(`selectedDetectorArchimedeanGate`); this leaf does NOT claim it, and by the
record-1389 IFF nothing else about the owner is missing — the support,
vanishings, detection, and smoothness sides are all already discharged by
`exists_routeAlphaOwner` plus `healthyCC20CompactSupportSmooth`. -/
theorem healthyDetectorData_of_routeAlphaOwner
    {rho : ℂ} {g : CompactLogTest}
    (hreal : HealthyMinimalLaplaceRealizes rho g)
    (hsupp : Function.support g.test ⊆
      Set.Icc (-(Real.log 2 / 2)) (Real.log 2 / 2))
    (harch : 0 < C1SameOwnerWeil.archimedeanTerm g.convolutionSquare) :
    HealthyYoshidaDetectorData rho g :=
  healthyDetectorData_of_HealthyMinimalLaplaceRealizes_of_archimedeanTerm_pos
    hreal
    (convolutionSquare_support_logTwo_of_rootSupport_logTwoHalf g hsupp)
    harch

end C1RouteAlphaOwner
end Source
end ConnesWeilRH
