import ConnesWeilRH.Dev.C1CC20EndpointCoefficient
import ConnesWeilRH.Dev.C1CC20ArchimedeanReadback
import ConnesWeilRH.Source.CC20Concrete.PositiveTrace
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# CC20 endpoint certificate data and the rank-one transfer step

This leaf joins three already separate layers:

* the explicit rational enclosure for the CC20 operator constant `gamma`;
* the coefficient `c = 4 * gamma / log 2`;
* a positive Hilbert-Schmidt trace and the endpoint bound consumed by the
  same-owner certificate.

The endpoint bound remains an explicit analytic field.  The final section
also constructs a zero-trace certificate on the already-proved narrow support
class.  That is a regression witness for the certificate interface, not the
nontrivial CC20 trace theorem.
-/

namespace ConnesWeilRH
namespace Source
namespace C1CC20EndpointCertificateData

open CCM25Concrete.CompactLogConvolution
open CC20Concrete
open C1CC20ArchimedeanReadback
open C1CC20EndpointCoefficient

/-! ## 1. Explicit CC20 spectral data -/

/-- Caller-supplied numerical data for the CC20 Lemma `second` constant.

The inequalities are intentionally fields: this structure does not claim to
prove the operator/spectral computation which supplies them.
-/
structure CC20GammaSpectralData where
  gamma : ℝ
  gamma_lower : (294 : ℝ) / 100 < gamma
  gamma_upper : gamma < (2944 : ℝ) / 1000

noncomputable def CC20GammaSpectralData.coefficient
    (data : CC20GammaSpectralData) : ℝ :=
  4 * data.gamma / Real.log 2

theorem CC20GammaSpectralData.coefficient_eq
    (data : CC20GammaSpectralData) :
    data.coefficient = 4 * data.gamma / Real.log 2 := by
  rfl

theorem CC20GammaSpectralData.coefficient_band
    (data : CC20GammaSpectralData) :
    13 < data.coefficient ∧ data.coefficient < 17 := by
  exact cc20EndpointCoefficient_band
    data.gamma_lower data.gamma_upper

theorem CC20GammaSpectralData.coefficient_positive
    (data : CC20GammaSpectralData) : 0 < data.coefficient := by
  exact lt_trans (by norm_num) data.coefficient_band.1

/-! ## 2. Positive-trace data attached to the certificate -/

/-- A positive Hilbert-Schmidt trace together with the remaining CC20 endpoint
bound, using one coefficient owner throughout. -/
structure CC20EndpointOperatorTraceData
    (g : CompactLogTest)
    {ι H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (basis : HilbertBasis ι ℂ H) where
  spectral : CC20GammaSpectralData
  traceData : PositiveTrace.BasisHilbertSchmidtData basis
  endpoint_bound :
    traceData.hsNormSq -
        cc20RankOneBadDirection spectral.coefficient g ≤
      cc20WInfinityLog g.convolutionSquare

noncomputable def CC20EndpointOperatorTraceData.toCertificate
    {g : CompactLogTest}
    {ι H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {basis : HilbertBasis ι ℂ H}
    (data : CC20EndpointOperatorTraceData g basis) :
    CC20EndpointTraceCertificate g where
  coefficient := data.spectral.coefficient
  trace := data.traceData.hsNormSq
  trace_nonnegative :=
    PositiveTrace.BasisHilbertSchmidtData.hsNormSq_nonnegative data.traceData
  endpoint_bound := data.endpoint_bound

theorem CC20EndpointOperatorTraceData.realTrace_eq_hsNormSq
    {g : CompactLogTest}
    {ι H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {basis : HilbertBasis ι ℂ H}
    (data : CC20EndpointOperatorTraceData g basis) :
    (PositiveTrace.ordinaryTraceAlong basis
      data.traceData.positiveComposition).re = data.traceData.hsNormSq := by
  rw [data.traceData.ordinaryTrace_positiveComposition]
  simp

theorem qw_nonneg_of_cc20EndpointOperatorTraceData
    (g : CompactLogTest)
    (hvanishes : CC20VanishesOn C1.healthyCC20TestSpace
        cc20TripleFiniteVanishingSet g)
    (hsupport : Function.support g.convolutionSquare.test ⊆
      Set.Ioo (-Real.log 2) (Real.log 2))
    {ι H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {basis : HilbertBasis ι ℂ H}
    (data : CC20EndpointOperatorTraceData g basis) :
    0 ≤ C1SameOwnerWeil.qw g := by
  exact qw_nonneg_of_cc20EndpointTraceCertificate g hvanishes hsupport
    data.toCertificate

/-! ## 3. The scalar rank-one transfer behind Lemma `second` -/

/-- The scaled negative form is bounded by the rank-one term once the repaired
quadratic form is nonnegative.  This is the exact algebraic transfer used after
the operator estimate; the estimate itself remains a caller premise. -/
theorem cc20ScaledNegativeForm_le_rankOne
    (data : CC20GammaSpectralData)
    {q rank : ℝ}
    (hshift : 0 ≤ q + data.gamma * rank) :
    -(4 / Real.log 2) * q ≤ data.coefficient * rank := by
  have hlog_pos : 0 < Real.log 2 := by
    exact lt_trans (by norm_num) Real.log_two_gt_d9
  have hscale : 0 ≤ (4 : ℝ) / Real.log 2 := by
    exact div_nonneg (by norm_num) hlog_pos.le
  have hmul : 0 ≤ (4 / Real.log 2) * (q + data.gamma * rank) :=
    mul_nonneg hscale hshift
  have hcoef : data.coefficient = (4 / Real.log 2) * data.gamma := by
    unfold CC20GammaSpectralData.coefficient
    field_simp [ne_of_gt hlog_pos]
  rw [hcoef]
  nlinarith [hmul]

/-- If the trace is the scaled negative form, the corrected residual is
nonpositive.  This isolates the part of the endpoint argument that is purely
algebraic from the still-open comparison with `WInfinity`. -/
theorem cc20EndpointResidual_nonpositive_of_shifted_form
    (data : CC20GammaSpectralData)
    {trace q rank : ℝ}
    (htrace : trace = -(4 / Real.log 2) * q)
    (hshift : 0 ≤ q + data.gamma * rank) :
    trace - data.coefficient * rank ≤ 0 := by
  rw [htrace]
  linarith [cc20ScaledNegativeForm_le_rankOne data hshift]

/-! ## Caller-supplied zero-trace witness -/

/-- A caller-supplied nonnegative `W∞` value produces the degenerate
zero-trace certificate.

This is deliberately support-free: the support and prime-free hypotheses
belong to the downstream `qw` consumer, while this definition only wires the
endpoint data into the certificate interface.  It is a regression witness,
not the nontrivial CC20 trace estimate.  The certificate is a data
structure, so the constructor is a definition, not a theorem. -/
noncomputable def zeroTraceCertificate_of_nonnegative_wInfinity
    (data : CC20GammaSpectralData)
    (g : CompactLogTest)
    (hvanishes : CC20VanishesOn C1.healthyCC20TestSpace
        cc20TripleFiniteVanishingSet g)
    (hwinf : 0 ≤ cc20WInfinityLog g.convolutionSquare) :
    CC20EndpointTraceCertificate g := by
  refine
    { coefficient := data.coefficient
      trace := 0
      trace_nonnegative := le_rfl
      endpoint_bound := ?_ }
  rw [cc20RankOneBadDirection_eq_zero_of_vanishesOn_cc20Triple
    data.coefficient g hvanishes]
  simpa using hwinf

end C1CC20EndpointCertificateData
end Source
end ConnesWeilRH
