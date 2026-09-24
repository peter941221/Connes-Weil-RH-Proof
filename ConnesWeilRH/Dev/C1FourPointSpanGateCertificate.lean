/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Dev.C1ArchimedeanIntegrabilityGeneric
import ConnesWeilRH.Dev.C1C3CarrierTransport
import ConnesWeilRH.Dev.C1FourPointSpectralPrefixTransport

/-!
# 103 Cut 2: the four-point span gate reduces to one diagonal sign

Map `103` books Cut 2 as a quadratic-form estimate on the annihilator-detector
span `v(lam) = u - lam * g`, where `u` is the committed four-point annihilator
and `g` the selected detector:

  `ICgate (v(lam).square) = D - lam * (B01 + B10) + lam^2 * C`

with `D = ICgate (u.square)`, `C = ICgate (g.square) > 0`, and the two cross
terms `B01 = ICgate (u.involution.convolution g)`, `B10` the reversed pair.
This module proves that identity on the committed owners
(`annihilator_span_gate_eq_parabola`, a specialization of the legalless
`gate_qform_span_free`) and then removes the cross terms from the acceptance
condition:

* `exists_nonzero_lambda_quadratic_nonpos_iff` is the complete trichotomy: a
  nonzero coefficient with nonpositive span gate exists exactly when the
  diagonal `D` is negative, or `D = 0` with a nonvanishing cross sum, or `D > 0`
  with the discriminant `B^2 - 4 C D` nonnegative (the map's determinant
  certificate; the `B != 0` side condition is needed only in the `D = 0` case).

* `exists_pos_lambda_quadratic_nonpos`: the strictly negative diagonal `D < 0`
  alone already produces a strictly positive coefficient, with no nonvanishing
  or sign condition on either cross term. The witness is the closed-form plus
  root `gatePlusRoot`; positivity is `B + sqrt (B^2 - 4 C D) > 0`, which holds
  because the square root strictly dominates `|B|`.

* `exists_pos_lambda_orbitWindowSemiLocalGate_of_annihilator_gate_neg` is the
  wire on a healthy detector: the only remaining Cut-2 obligation is the single
  strict sign `ICgate ((fullFunctionalEquationOrbitAnnihilator g rho).square) < 0`,
  and the conclusion is stated on the same `annihilatorDetectorSpanVector` owner
  that `C1FourPointSpectralPrefixTransport` bounds on the spectral side, so one
  coefficient `lam > 0` carries both signs
  (`exists_pos_lambda_gate_and_prefix_of_annihilator_gate_neg`).

* The vertex branch, selected by the record-1918 sign probe: for a positive
  cross sum and a strictly negative gate determinant
  `D * C - (B / 2) ^ 2 < 0` (equivalently a strictly positive discriminant),
  the vertex coefficient `B / (2 * C)` is strictly positive and the span gate
  is *strictly* negative there (`gate_quadratic_at_vertex`,
  `exists_pos_lambda_quadratic_neg_of_det_neg`), with the same owner wires
  (`exists_pos_lambda_orbitWindowSemiLocalGate_of_annihilator_det_neg`,
  `exists_pos_lambda_gate_and_prefix_of_annihilator_det_neg`).

No gate sign, no joint high-shell margin, and no RH statement is proved here.
RH NOT claimed.
-/

namespace ConnesWeilRH
namespace Source
namespace C1FourPointSpanGateCertificate

open Matrix
open CC20YoshidaConvolution
open CC20YoshidaConvolution.CompactLogTest
open CC20YoshidaNearZeros
open CCM25Concrete.CompactLogConvolution
open CCM25Concrete.UnscaledYoshidaSelectedOwner
open ConnesWeilRH.Dev.C1C3CarrierTransport
open C1ArchimedeanIntegrabilityGeneric
open C1GateMatrixRepresentation
open C1HealthyYoshidaDetector
open C1LocalConfigurationDomination
open C1OrbitWindowSemiLocalGate
open C1SpectralWeil
open C1SameOwnerWeil
open C1TwoPointSpectralDecomposition
open C1FourPointSpectralPrefixTransport
open scoped BigOperators

noncomputable section

/-! ## The span quadratic on the committed owners -/

/-- The gate of the annihilator-detector span is the explicit quadratic
polynomial in the span coefficient whose coefficients are the three gate
values of the owner pair. -/
theorem annihilator_span_gate_eq_parabola
    (u g : CompactLogTest) (lam : Real) {B : Real}
    (hw : ∀ i, Function.support ((![u, g] : Fin 2 → CompactLogTest) i).test ⊆
      Set.Ioo (-B) B) :
    ICgate ((annihilatorDetectorSpanVector u g lam).convolutionSquare) =
      ICgate u.convolutionSquare -
        lam * (ICgate (u.involution.convolution g) +
          ICgate (g.involution.convolution u)) +
        lam ^ 2 * ICgate g.convolutionSquare := by
  have h := gate_qform_span_free (![u, g] : Fin 2 → CompactLogTest)
    (![1, -lam] : Fin 2 → Real) hw
  rw [show spanObj (![u, g] : Fin 2 → CompactLogTest)
      (![1, -lam] : Fin 2 → Real) =
      annihilatorDetectorSpanVector u g lam from rfl] at h
  rw [h, ← pair_gate_sum_eq_qform]
  rw [Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    pairTest, Fin.isValue]
  have hsq : ∀ f : CompactLogTest,
      f.involution.convolution f = f.convolutionSquare := fun _ => rfl
  rw [← hsq u, ← hsq g]
  ring

/-! ## Symmetric polarization of the same-owner parabola -/

/-- The two symmetric evaluations of the same-owner span recover the sum of
the directed cross gates.  This is the exact polarization identity for the
unrestricted annihilator-detector pair; no cross-term symmetry is assumed. -/
theorem annihilator_span_gate_polarization
    (u g : CompactLogTest) (B : Real)
    (hw : ∀ i, Function.support ((![u, g] : Fin 2 → CompactLogTest) i).test ⊆
      Set.Ioo (-B) B) :
    2 * (ICgate (u.involution.convolution g) +
      ICgate (g.involution.convolution u)) =
      ICgate ((annihilatorDetectorSpanVector u g (-1)).convolutionSquare) -
        ICgate ((annihilatorDetectorSpanVector u g 1).convolutionSquare) := by
  have hneg := annihilator_span_gate_eq_parabola u g (-1) hw
  have hpos := annihilator_span_gate_eq_parabola u g 1 hw
  rw [hneg, hpos]
  ring

/-- The vertex determinant can equivalently be read from the two symmetric
same-owner gate evaluations.  This is useful when the archimedean and finite
prime channels are estimated after the span has been formed. -/
theorem annihilator_span_gate_det_eq_symmetric_gap
    (u g : CompactLogTest) (B : Real)
    (hw : ∀ i, Function.support ((![u, g] : Fin 2 → CompactLogTest) i).test ⊆
      Set.Ioo (-B) B) :
    ICgate u.convolutionSquare * ICgate g.convolutionSquare -
        ((ICgate (u.involution.convolution g) +
          ICgate (g.involution.convolution u)) / 2) ^ 2 =
    ICgate u.convolutionSquare * ICgate g.convolutionSquare -
        ((ICgate ((annihilatorDetectorSpanVector u g (-1)).convolutionSquare) -
          ICgate ((annihilatorDetectorSpanVector u g 1).convolutionSquare)) / 4) ^ 2 := by
  rw [← annihilator_span_gate_polarization u g B hw]
  ring


/-! ## The scalar reduction -/

/-- The larger root of the span quadratic in the sign convention
`D - lam * B + lam ^ 2 * C`. -/
noncomputable def gatePlusRoot (D B C : Real) : Real :=
  (B + Real.sqrt (B ^ 2 - 4 * C * D)) / (2 * C)

/-- The plus root annihilates the span quadratic whenever the discriminant is
nonnegative. -/
theorem gate_quadratic_at_gatePlusRoot {D B C : Real} (hC : 0 < C)
    (hdisc : 0 ≤ B ^ 2 - 4 * C * D) :
    D - gatePlusRoot D B C * B + gatePlusRoot D B C ^ 2 * C = 0 := by
  have h2C : (2 : Real) * C ≠ 0 := by positivity
  have hroot : 2 * C * gatePlusRoot D B C - B =
      Real.sqrt (B ^ 2 - 4 * C * D) := by
    unfold gatePlusRoot
    field_simp
    ring
  have hcomplete : (4 : Real) * C *
      (D - gatePlusRoot D B C * B + gatePlusRoot D B C ^ 2 * C) =
      (2 * C * gatePlusRoot D B C - B) ^ 2 + (4 * C * D - B ^ 2) := by
    ring
  have hzero : (4 : Real) * C *
      (D - gatePlusRoot D B C * B + gatePlusRoot D B C ^ 2 * C) = 0 := by
    rw [hcomplete, hroot, Real.sq_sqrt hdisc]
    ring
  exact (mul_eq_zero.mp hzero).resolve_left (by positivity)

/-- A strictly negative diagonal makes the plus root strictly positive: the
square root strictly dominates `|B|`. -/
theorem gatePlusRoot_pos_of_neg {D B C : Real} (hC : 0 < C) (hD : D < 0) :
    0 < gatePlusRoot D B C := by
  have hdisc : 0 < B ^ 2 - 4 * C * D := by
    nlinarith [sq_nonneg B, mul_pos hC (neg_pos.mpr hD)]
  have hnum : 0 < B + Real.sqrt (B ^ 2 - 4 * C * D) := by
    rcases lt_or_ge 0 B with hB | hB
    · have hr : 0 < Real.sqrt (B ^ 2 - 4 * C * D) := Real.sqrt_pos.mpr hdisc
      linarith
    · have hlt : -B < Real.sqrt (B ^ 2 - 4 * C * D) := by
        refine Real.lt_sqrt_of_sq_lt ?_
        nlinarith [mul_pos hC (neg_pos.mpr hD)]
      linarith
  unfold gatePlusRoot
  exact div_pos hnum (by positivity)

/-- A strictly negative diagonal alone supplies a strictly positive span
coefficient with nonpositive span gate. No cross-term side condition enters. -/
theorem exists_pos_lambda_quadratic_nonpos {D B C : Real} (hC : 0 < C)
    (hD : D < 0) :
    ∃ lam : Real, 0 < lam ∧ D - lam * B + lam ^ 2 * C ≤ 0 := by
  have hdisc : 0 ≤ B ^ 2 - 4 * C * D := by
    nlinarith [sq_nonneg B, mul_pos hC (neg_pos.mpr hD)]
  exact ⟨gatePlusRoot D B C, gatePlusRoot_pos_of_neg hC hD,
    (gate_quadratic_at_gatePlusRoot hC hdisc).le⟩

/-- The complete trichotomy for the span quadratic: a nonzero coefficient with
nonpositive value exists exactly in one of the three named cases. This is the
exact algebraic content of the map's determinant certificate, sharpened: the
nonvanishing cross-sum condition is needed only when `D = 0`. -/
theorem exists_nonzero_lambda_quadratic_nonpos_iff {D B C : Real} (hC : 0 < C) :
    (∃ lam : Real, lam ≠ 0 ∧ D - lam * B + lam ^ 2 * C ≤ 0) ↔
      (D < 0 ∨ (D = 0 ∧ B ≠ 0) ∨ (0 < D ∧ 0 ≤ B ^ 2 - 4 * C * D)) := by
  constructor
  · rintro ⟨lam, hne, hQ⟩
    rcases lt_trichotomy D 0 with hlt | heq | hgt
    · exact Or.inl hlt
    · by_cases hB : B = 0
      · exfalso
        rw [heq, hB] at hQ
        simp only [mul_zero, sub_zero, zero_add] at hQ
        have hpos : 0 < lam ^ 2 * C := mul_pos (sq_pos_of_ne_zero hne) hC
        linarith
      · exact Or.inr (Or.inl ⟨heq, hB⟩)
    · by_cases hdisc : 0 ≤ B ^ 2 - 4 * C * D
      · exact Or.inr (Or.inr ⟨hgt, hdisc⟩)
      · exfalso
        have hcomp : (4 : Real) * C * (D - lam * B + lam ^ 2 * C) =
            (2 * C * lam - B) ^ 2 + (4 * C * D - B ^ 2) := by
          ring
        have hneg : 0 < 4 * C * D - B ^ 2 := by linarith [not_le.mp hdisc]
        have hpos : 0 < (4 : Real) * C *
            (D - lam * B + lam ^ 2 * C) := by
          rw [hcomp]
          nlinarith [sq_nonneg (2 * C * lam - B)]
        have hnonpos : (4 : Real) * C * (D - lam * B + lam ^ 2 * C) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (by positivity) hQ
        linarith
  · rintro (hlt | ⟨heq, hB⟩ | ⟨hgt, hdisc⟩)
    · obtain ⟨lam, hpos, hQ⟩ := exists_pos_lambda_quadratic_nonpos hC hlt
      exact ⟨lam, ne_of_gt hpos, hQ⟩
    · refine ⟨B / C, div_ne_zero hB (ne_of_gt hC), ?_⟩
      have hzero : D - B / C * B + (B / C) ^ 2 * C = 0 := by
        rw [heq]
        field_simp
        ring
      rw [hzero]
    · refine ⟨gatePlusRoot D B C, ?_, (gate_quadratic_at_gatePlusRoot hC hdisc).le⟩
      intro hzero
      have hsum : B + Real.sqrt (B ^ 2 - 4 * C * D) = 0 := by
        have := hzero
        unfold gatePlusRoot at this
        field_simp at this
        linarith
      have hsqrt : Real.sqrt (B ^ 2 - 4 * C * D) = -B := by linarith
      have hsq := Real.sq_sqrt hdisc
      rw [hsqrt] at hsq
      nlinarith [mul_pos hC hgt]

/-! ## The vertex branch -/

/-- The parabola value at the vertex coefficient `B / (2 * C)` in the exact
rational form `-(B ^ 2 - 4 * C * D) / (4 * C)`. -/
theorem gate_quadratic_at_vertex {D B C : Real} (hC : 0 < C) :
    D - (B / (2 * C)) * B + (B / (2 * C)) ^ 2 * C =
      -(B ^ 2 - 4 * C * D) / (4 * C) := by
  have h2C : (2 : Real) * C ≠ 0 := by positivity
  field_simp
  ring

/-- The strict vertex witness: a positive cross sum, a positive pivot, and a
strictly negative gate determinant `D * C - (B / 2) ^ 2 < 0` (equivalently a
strictly positive discriminant) supply a strictly positive span coefficient
whose span gate is strictly negative. This is the branch selected by the
record-1918 sign probe on the committed detector class. -/
theorem exists_pos_lambda_quadratic_neg_of_det_neg {D B C : Real} (hC : 0 < C)
    (hB : 0 < B) (hdet : D * C - (B / 2) ^ 2 < 0) :
    ∃ lam : Real, 0 < lam ∧ D - lam * B + lam ^ 2 * C < 0 := by
  refine ⟨B / (2 * C), div_pos hB (by positivity), ?_⟩
  have hdisc : 0 < B ^ 2 - 4 * C * D := by
    nlinarith [hdet]
  rw [gate_quadratic_at_vertex hC]
  exact div_neg_of_neg_of_pos (by linarith) (by positivity)

/-! ## The wire on the healthy detector owner -/

/-- 103 Cut 2 wire: on a healthy detector, a strictly negative gate on the
four-point annihilator supplies a strictly positive span coefficient whose
span gate is nonpositive. The only game sign is the diagonal. -/
theorem exists_pos_lambda_orbitWindowSemiLocalGate_of_annihilator_gate_neg
    {rho : Complex} {g : CompactLogTest}
    (hdata : HealthyYoshidaDetectorData rho g)
    {B : Real} (hsupport : Function.support g.test ⊆ Set.Ioo (-B) B)
    (hdiag : ICgate
      ((fullFunctionalEquationOrbitAnnihilator g rho).convolutionSquare) < 0) :
    ∃ lam : Real, 0 < lam ∧
      orbitWindowSemiLocalGate
        (annihilatorDetectorSpanVector
          (fullFunctionalEquationOrbitAnnihilator g rho) g lam) := by
  set u : CompactLogTest := fullFunctionalEquationOrbitAnnihilator g rho with hu
  have hC : 0 < ICgate g.convolutionSquare := by
    have h := pinned_orbit_positive_pivot hdata (0 : Real)
    rwa [carrierModulate_neg_inv (0 : Real) g] at h
  have hsupp_g : Function.support g.test ⊆ Set.Icc (-B) B :=
    hsupport.trans Set.Ioo_subset_Icc_self
  have hsupp_u : Function.support u.test ⊆ Set.Icc (-B) B := by
    rw [hu]
    exact fullFunctionalEquationOrbitAnnihilator_support_subset_Icc g rho hsupp_g
  have hw : ∀ i, Function.support ((![u, g] : Fin 2 → CompactLogTest) i).test ⊆
      Set.Ioo (-(B + 1)) (B + 1) := by
    intro i
    fin_cases i
    · intro x hx
      have hx' := hsupp_u hx
      exact ⟨by linarith [hx'.1], by linarith [hx'.2]⟩
    · intro x hx
      have hx' := hsupp_g hx
      exact ⟨by linarith [hx'.1], by linarith [hx'.2]⟩
  obtain ⟨lam, hpos, hQ⟩ := exists_pos_lambda_quadratic_nonpos
    (D := ICgate u.convolutionSquare)
    (B := ICgate (u.involution.convolution g) + ICgate (g.involution.convolution u))
    (C := ICgate g.convolutionSquare) hC (by rw [hu]; exact hdiag)
  refine ⟨lam, hpos, ?_⟩
  rw [orbitWindowSemiLocalGate_iff, annihilator_span_gate_eq_parabola u g lam hw]
  exact hQ

/-- 103 Cut 2 wire, vertex branch: on a healthy detector, a positive cross sum
with a strictly negative gate determinant on the four-point annihilator
supplies a strictly positive span coefficient whose span gate is strictly
negative. Under the committed cross-term symmetry the determinant hypothesis
reads `ICgate(u.square) * ICgate(g.square) - ICgate(u*⋆g) ^ 2 < 0`. -/
theorem exists_pos_lambda_orbitWindowSemiLocalGate_of_annihilator_det_neg
    {rho : Complex} {g : CompactLogTest}
    (hdata : HealthyYoshidaDetectorData rho g)
    {B : Real} (hsupport : Function.support g.test ⊆ Set.Ioo (-B) B)
    (hcross : 0 < ICgate
        ((fullFunctionalEquationOrbitAnnihilator g rho).involution.convolution g) +
      ICgate (g.involution.convolution
        (fullFunctionalEquationOrbitAnnihilator g rho)))
    (hdet : ICgate
        ((fullFunctionalEquationOrbitAnnihilator g rho).convolutionSquare) *
        ICgate g.convolutionSquare -
        ((ICgate ((fullFunctionalEquationOrbitAnnihilator g rho).involution.convolution g) +
          ICgate (g.involution.convolution
            (fullFunctionalEquationOrbitAnnihilator g rho))) / 2) ^ 2 < 0) :
    ∃ lam : Real, 0 < lam ∧
      orbitWindowSemiLocalGate
        (annihilatorDetectorSpanVector
          (fullFunctionalEquationOrbitAnnihilator g rho) g lam) := by
  set u : CompactLogTest := fullFunctionalEquationOrbitAnnihilator g rho with hu
  have hC : 0 < ICgate g.convolutionSquare := by
    have h := pinned_orbit_positive_pivot hdata (0 : Real)
    rwa [carrierModulate_neg_inv (0 : Real) g] at h
  have hsupp_g : Function.support g.test ⊆ Set.Icc (-B) B :=
    hsupport.trans Set.Ioo_subset_Icc_self
  have hsupp_u : Function.support u.test ⊆ Set.Icc (-B) B := by
    rw [hu]
    exact fullFunctionalEquationOrbitAnnihilator_support_subset_Icc g rho hsupp_g
  have hw : ∀ i, Function.support ((![u, g] : Fin 2 → CompactLogTest) i).test ⊆
      Set.Ioo (-(B + 1)) (B + 1) := by
    intro i
    fin_cases i
    · intro x hx
      have hx' := hsupp_u hx
      exact ⟨by linarith [hx'.1], by linarith [hx'.2]⟩
    · intro x hx
      have hx' := hsupp_g hx
      exact ⟨by linarith [hx'.1], by linarith [hx'.2]⟩
  obtain ⟨lam, hpos, hQ⟩ := exists_pos_lambda_quadratic_neg_of_det_neg
    (D := ICgate u.convolutionSquare)
    (B := ICgate (u.involution.convolution g) + ICgate (g.involution.convolution u))
    (C := ICgate g.convolutionSquare) hC (by rw [hu]; exact hcross)
      (by rw [hu]; exact hdet)
  refine ⟨lam, hpos, ?_⟩
  rw [orbitWindowSemiLocalGate_iff, annihilator_span_gate_eq_parabola u g lam hw]
  exact hQ.le

/-! ## Same-coefficient coordination with the spectral prefix -/

/-- One strictly positive coefficient carries both Cut-2 signs on the same
`annihilatorDetectorSpanVector` owner: the nonpositive span gate and the
nonpositive spectral prefix bound. The joint high-shell margin (the remaining
Cut-1 acceptance) is not proved here. -/
theorem exists_pos_lambda_gate_and_prefix_of_annihilator_gate_neg
    (g : CompactLogTest) (rho : sourceNontrivialZeroSet)
    (S : Finset sourceNontrivialZeroSet) (hrho : rho ∈ S)
    (hoff : rho.1.re ≠ 1 / 2)
    (hdata : HealthyYoshidaDetectorData rho.1 g)
    {B : Real} (hsupport : Function.support g.test ⊆ Set.Ioo (-B) B)
    (htarget :
      ∀ w : FiniteMellinNode (sourceFunctionalEquationOrbit rho.1),
        laplaceAt g (w.1 - 1 / 2) = negativeSourceOrbitValue rho.1 w)
    (hzero : ∀ z : sourceNontrivialZeroSet, z ∈ S →
      z.1 ∉ sourceFunctionalEquationOrbit rho.1 →
        laplaceAt g.convolutionSquare (z.1 - 1 / 2) = 0)
    (hdiag : ICgate
      ((fullFunctionalEquationOrbitAnnihilator g rho.1).convolutionSquare) < 0) :
    ∃ lam : Real, 0 < lam ∧
      orbitWindowSemiLocalGate
        (annihilatorDetectorSpanVector
          (fullFunctionalEquationOrbitAnnihilator g rho.1) g lam) ∧
      (∑ z ∈ S,
        spectralTerm
          (annihilatorDetectorSpanVector
            (fullFunctionalEquationOrbitAnnihilator g rho.1) g lam).convolutionSquare
          z).re ≤
        -(xiMultiplicity rho : Real) * lam ^ 2 := by
  obtain ⟨lam, hpos, hgate⟩ :=
    exists_pos_lambda_orbitWindowSemiLocalGate_of_annihilator_gate_neg
      hdata hsupport hdiag
  exact ⟨lam, hpos, hgate,
    finiteSpectralPrefix_re_le_neg_xiMultiplicity_mul_sq_of_fullOrbit_transport
      g rho lam S hrho hoff htarget hzero⟩

/-- One strictly positive coefficient carries both Cut-2 signs on the same
`annihilatorDetectorSpanVector` owner in the vertex branch: the strictly
negative span gate at the vertex and the nonpositive spectral prefix bound.
The joint high-shell margin (the remaining Cut-1 acceptance) is not proved
here. -/
theorem exists_pos_lambda_gate_and_prefix_of_annihilator_det_neg
    (g : CompactLogTest) (rho : sourceNontrivialZeroSet)
    (S : Finset sourceNontrivialZeroSet) (hrho : rho ∈ S)
    (hoff : rho.1.re ≠ 1 / 2)
    (hdata : HealthyYoshidaDetectorData rho.1 g)
    {B : Real} (hsupport : Function.support g.test ⊆ Set.Ioo (-B) B)
    (htarget :
      ∀ w : FiniteMellinNode (sourceFunctionalEquationOrbit rho.1),
        laplaceAt g (w.1 - 1 / 2) = negativeSourceOrbitValue rho.1 w)
    (hzero : ∀ z : sourceNontrivialZeroSet, z ∈ S →
      z.1 ∉ sourceFunctionalEquationOrbit rho.1 →
        laplaceAt g.convolutionSquare (z.1 - 1 / 2) = 0)
    (hcross : 0 < ICgate
        ((fullFunctionalEquationOrbitAnnihilator g rho.1).involution.convolution g) +
      ICgate (g.involution.convolution
        (fullFunctionalEquationOrbitAnnihilator g rho.1)))
    (hdet : ICgate
        ((fullFunctionalEquationOrbitAnnihilator g rho.1).convolutionSquare) *
        ICgate g.convolutionSquare -
        ((ICgate ((fullFunctionalEquationOrbitAnnihilator g rho.1).involution.convolution g) +
          ICgate (g.involution.convolution
            (fullFunctionalEquationOrbitAnnihilator g rho.1))) / 2) ^ 2 < 0) :
    ∃ lam : Real, 0 < lam ∧
      orbitWindowSemiLocalGate
        (annihilatorDetectorSpanVector
          (fullFunctionalEquationOrbitAnnihilator g rho.1) g lam) ∧
      (∑ z ∈ S,
        spectralTerm
          (annihilatorDetectorSpanVector
            (fullFunctionalEquationOrbitAnnihilator g rho.1) g lam).convolutionSquare
          z).re ≤
        -(xiMultiplicity rho : Real) * lam ^ 2 := by
  obtain ⟨lam, hpos, hgate⟩ :=
    exists_pos_lambda_orbitWindowSemiLocalGate_of_annihilator_det_neg
      hdata hsupport hcross hdet
  exact ⟨lam, hpos, hgate,
    finiteSpectralPrefix_re_le_neg_xiMultiplicity_mul_sq_of_fullOrbit_transport
      g rho lam S hrho hoff htarget hzero⟩

end

end C1FourPointSpanGateCertificate
end Source
end ConnesWeilRH
