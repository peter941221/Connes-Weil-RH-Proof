/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Dev.C1FourPointSpanGateCertificate

/-!
# 103 Cut 2, audit brick: the diagonal sign is the only obligation

Record-1981 audit of the record-1917 wire. In
`exists_pos_lambda_quadratic_nonpos` the hypothesis `0 < C` exists only to
certify the closed-form witness `gatePlusRoot` (whose denominator is `2 * C`);
it is a packaging artifact, not mathematics. This module supplies the
hypothesis-free witness and rewires the committed consumer without the
healthy-detector data:

* `exists_pos_lambda_quadratic_nonpos_of_diag_neg`: `D < 0` alone (any signs
  of `B` and `C`) yields a strictly positive coefficient with a nonpositive
  span quadratic. The witness is the explicit small coefficient
  `diagNegWitness D B C = min 1 (|D| / (2 * (|B| + |C| + 1)))`; the estimate
  is `D - lam*B + lam^2*C <= D + (|B| + |C|)*lam < D + |D|/2 = D/2 < 0`.

* `exists_pos_lambda_gate_and_prefix_of_annihilator_gate_neg'` is the
  committed consumer wire of record 1917
  (`exists_pos_lambda_gate_and_prefix_of_annihilator_gate_neg`) with the
  `HealthyYoshidaDetectorData` hypothesis REMOVED: no healthy pivot enters,
  only the support bound needed to state the span parabola identity, the
  interpolation hypotheses `htarget`/`hzero` consumed by the spectral prefix
  transport, and the single strict sign `hdiag`. One strictly positive
  coefficient carries the nonpositive span gate and the prefix margin
  `-xiMultiplicity(rho) * lam^2`, exactly as before.
-/

namespace ConnesWeilRH
namespace Source
namespace C1FourPointSpanGateDiagOnly

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
open ConnesWeilRH.Source.C1FourPointSpanGateCertificate
open scoped BigOperators

/-- Explicit small strictly positive coefficient at which the span quadratic
is dominated by its diagonal alone. -/
noncomputable def diagNegWitness (D B C : Real) : Real :=
  min 1 (|D| / (2 * (|B| + |C| + 1)))

/-- The witness is strictly positive whenever the diagonal is strictly
negative (indeed whenever `D != 0`). -/
theorem diagNegWitness_pos {D B C : Real} (hD : D < 0) :
    0 < diagNegWitness D B C := by
  refine lt_min (by norm_num) ?_
  exact div_pos (abs_pos.mpr hD.ne) (by positivity)

/-- **Audit brick.** A strictly negative diagonal alone supplies a strictly
positive span coefficient with a nonpositive span quadratic. No hypothesis on
`B` or `C` enters: the `0 < C` hypothesis of
`exists_pos_lambda_quadratic_nonpos` certifies only the closed-form plus-root
witness, not the existence statement. -/
theorem exists_pos_lambda_quadratic_nonpos_of_diag_neg {D B C : Real}
    (hD : D < 0) :
    ∃ lam : Real, 0 < lam ∧ D - lam * B + lam ^ 2 * C ≤ 0 := by
  refine ⟨diagNegWitness D B C, diagNegWitness_pos hD, ?_⟩
  have hnlam : 0 ≤ diagNegWitness D B C :=
    le_of_lt (diagNegWitness_pos hD)
  have hle1 : diagNegWitness D B C ≤ 1 := min_le_left _ _
  have hle2 : diagNegWitness D B C ≤ |D| / (2 * (|B| + |C| + 1)) :=
    min_le_right _ _
  have hB : diagNegWitness D B C * B ≤ diagNegWitness D B C * |B| :=
    mul_le_mul_of_nonneg_left (le_abs_self B) hnlam
  have hC : diagNegWitness D B C ^ 2 * C ≤ diagNegWitness D B C * |C| := by
    have h2 : diagNegWitness D B C ^ 2 ≤ diagNegWitness D B C := by
      nlinarith [hle1, hnlam]
    calc diagNegWitness D B C ^ 2 * C
        ≤ diagNegWitness D B C ^ 2 * |C| :=
          mul_le_mul_of_nonneg_left (le_abs_self C) (sq_nonneg _)
      _ ≤ diagNegWitness D B C * |C| :=
          mul_le_mul_of_nonneg_right h2 (by positivity)
  have hkey : diagNegWitness D B C * |B| + diagNegWitness D B C * |C|
      < -D / 2 := by
    have hsplit : diagNegWitness D B C * |B| + diagNegWitness D B C * |C|
        = (|B| + |C|) * diagNegWitness D B C := by ring
    have h1 : (|B| + |C|) * diagNegWitness D B C
        ≤ (|B| + |C|) * (|D| / (2 * (|B| + |C| + 1))) :=
      mul_le_mul_of_nonneg_left hle2 (by positivity)
    have h2 : (|B| + |C|) * (|D| / (2 * (|B| + |C| + 1))) < |D| / 2 := by
      have ht : 0 < |D| := abs_pos.mpr hD.ne
      field_simp
      linarith
    rw [hsplit]
    linarith [h1, h2, abs_of_neg hD]
  -- assemble: the quadratic is at most D + (|B| + |C|) * lam < D/2 < 0
  have htri : -(diagNegWitness D B C * B) ≤ diagNegWitness D B C * |B| := by
    have h1 : -B ≤ |B| := by linarith [neg_abs_le B]
    calc -(diagNegWitness D B C * B)
        = diagNegWitness D B C * (-B) := by ring
      _ ≤ diagNegWitness D B C * |B| :=
          mul_le_mul_of_nonneg_left h1 hnlam
  have hfinal : D + diagNegWitness D B C * |B| + diagNegWitness D B C ^ 2 * C
      < 0 := by
    linarith [hkey, hC, abs_of_neg hD]
  have hzero : D - diagNegWitness D B C * B
      + diagNegWitness D B C ^ 2 * C
      ≤ D + diagNegWitness D B C * |B| + diagNegWitness D B C ^ 2 * C := by
    linarith [htri]
  linarith

/-- **Rewired consumer.** The record-1917 wire
`exists_pos_lambda_gate_and_prefix_of_annihilator_gate_neg` with the
`HealthyYoshidaDetectorData` hypothesis REMOVED (it entered only to produce
`0 < ICgate g.square`, which the audit brick no longer needs). The surviving
hypotheses are exactly the ones the conclusions consume: the support bound
needed to state the span parabola identity, the orbit interpolation
`htarget` and kill vanishing `hzero` consumed by the spectral prefix
transport, and the single strict diagonal sign. One strictly positive
coefficient carries the nonpositive span gate and the prefix margin
`-xiMultiplicity(rho) * lam^2`. -/
theorem exists_pos_lambda_gate_and_prefix_of_annihilator_gate_neg'
    (g : CompactLogTest) (rho : sourceNontrivialZeroSet)
    (S : Finset sourceNontrivialZeroSet) (hrho : rho ∈ S)
    (hoff : rho.1.re ≠ 1 / 2)
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
  set u : CompactLogTest := fullFunctionalEquationOrbitAnnihilator g rho.1 with hu
  have hsupp_g : Function.support g.test ⊆ Set.Icc (-B) B :=
    hsupport.trans Set.Ioo_subset_Icc_self
  have hsupp_u : Function.support u.test ⊆ Set.Icc (-B) B := by
    rw [hu]
    exact fullFunctionalEquationOrbitAnnihilator_support_subset_Icc g rho.1
      hsupp_g
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
  obtain ⟨lam, hpos, hQ⟩ :=
    exists_pos_lambda_quadratic_nonpos_of_diag_neg
      (D := ICgate u.convolutionSquare)
      (B := ICgate (u.involution.convolution g) +
        ICgate (g.involution.convolution u))
      (C := ICgate g.convolutionSquare)
      (by rw [hu]; exact hdiag)
  refine ⟨lam, hpos, ?_,
    finiteSpectralPrefix_re_le_neg_xiMultiplicity_mul_sq_of_fullOrbit_transport
      g rho lam S hrho hoff htarget hzero⟩
  rw [orbitWindowSemiLocalGate_iff, annihilator_span_gate_eq_parabola u g lam hw]
  exact hQ

end C1FourPointSpanGateDiagOnly
end Source
end ConnesWeilRH
