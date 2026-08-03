/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCanonicalRealGate
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSRawEndpointSupportBound
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSSupportMajorant
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaJointProducer

/-!
# Support-only bound for the canonical real Gate 3U contract

For an arbitrary visible-prime family, the existing raw endpoint estimate
pays the inverse square of the finite Euler lower factor.  That cost is not
uniform over unrelated families.  The canonical family is different: all of
its visible primes come from the compact arithmetic support of the same
selected owner, so its cardinality is controlled by that owner's support
radius.

Using the coarse source bound `a_p <= 3/4`, every lower Euler factor is at
least `1/4`.  Consequently

`lowerFactor(canonicalFamily owner)^(-2)
  <= 16^(ceil(exp(supportRadius)) + 1)`.

Combining this with the already proved raw endpoint support estimate gives an
explicit support-only majorant for `canonicalRealGate3UAt`.  No
source-to-ambient trace cycle, dual-coframe carrier identification, or
branchwise physical estimate is used.  The exponential cardinality majorant
is deliberately coarse; this module closes the canonical-family real Gate
contract, not the older uniform contract over arbitrary unrelated families.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSCanonicalSupportGate3U

open MeasureTheory
open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CC20Concrete.CompactRootHalfLinePair
open CC20Concrete.PositiveTrace
open CCM24FiniteSBandTrace
open CCM24FiniteSCanonicalCompletedResponse
open CCM24FiniteSCanonicalRealGate
open CCM24FiniteSCommonBoundaryPair
open CCM24FiniteSCompletedJuliaJointProducer
open CCM24FiniteSGramResponse
open CCM24FiniteSProjectionTrace
open CCM24FiniteSProjectionTrace.FinitePrimePowerFamily
open CCM24FiniteSRawEndpointSupportBound
open CCM24FiniteSSupportMajorant
open CCM24SourceProlateTrace

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-! ## Canonical lower-factor cost -/

/-- The inverse square of a finite Euler lower product has the coarse bound
`16^length`.  This is a fixed-family estimate, not a uniform-in-family
cancellation theorem. -/
theorem finiteEulerLowerFactor_inv_sq_le_sixteen_pow_length
    (S : List CCM24VisiblePrime) :
    ((finiteEulerLowerFactor S) ^ 2)⁻¹ <= (16 : ℝ) ^ S.length := by
  induction S with
  | nil => norm_num [finiteEulerLowerFactor]
  | cons p S ih =>
      have hpCoefficient :
          ccm24PrimeEulerCoefficient p <= (3 / 4 : ℝ) :=
        ccm24PrimeEulerCoefficient_le_three_quarters p
      have hpLowerPos : 0 < 1 - ccm24PrimeEulerCoefficient p :=
        primeEulerLowerFactor_pos p
      have hpInvSq :
          ((1 - ccm24PrimeEulerCoefficient p) ^ 2)⁻¹ <= (16 : ℝ) := by
        apply (inv_le_iff_one_le_mul₀ (sq_pos_of_pos hpLowerPos)).2
        nlinarith [sq_nonneg (1 - ccm24PrimeEulerCoefficient p)]
      change
        (((1 - ccm24PrimeEulerCoefficient p) *
          finiteEulerLowerFactor S) ^ 2)⁻¹ <=
            (16 : ℝ) ^ (S.length + 1)
      rw [mul_pow, mul_inv_rev, mul_comm]
      calc
        ((1 - ccm24PrimeEulerCoefficient p) ^ 2)⁻¹ *
            ((finiteEulerLowerFactor S) ^ 2)⁻¹ <=
          16 * (16 : ℝ) ^ S.length := by
            exact mul_le_mul hpInvSq ih (by positivity) (by norm_num)
        _ = (16 : ℝ) ^ (S.length + 1) := by
          rw [pow_succ]
          ring

/-- Every visible prime in the canonical family lies inside the logarithmic
support radius of the same selected square. -/
theorem canonicalVisiblePrime_log_le_supportRadius
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    {p : CCM24VisiblePrime}
    (hp : p ∈ (canonicalFamily owner).visiblePrimes) :
    Real.log (p : ℝ) <= owner.supportRadius := by
  have hpOwner : p ∈ (ofSelectedOwner owner).visiblePrimes := by
    simpa only [canonicalFamily] using hp
  obtain ⟨m, hm⟩ :=
    (ofSelectedOwner owner).exists_term_of_mem_visiblePrimes hpOwner
  have hm0 : m ≠ 0 :=
    (ofSelectedOwner owner).exponent_ne_zero (p.1, m) hm
  have hterm : owner.finitePrimeTerm (p.1 ^ m) ≠ 0 :=
    finitePrimeTerm_pow_ne_zero_of_mem_ofSelectedOwner owner hm
  have hsupport :=
    owner.abs_log_le_supportRadius_of_finitePrimeTerm_ne_zero hterm
  have hlogPos : 0 < Real.log (p : ℝ) :=
    Real.log_pos (by exact_mod_cast p.property)
  have hmOne : (1 : ℝ) <= m := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr hm0
  have hmultiple : (m : ℝ) * Real.log (p : ℝ) <= owner.supportRadius := by
    calc
      (m : ℝ) * Real.log (p : ℝ) =
          Real.log (((p.1 ^ m : ℕ) : ℝ)) := by
            simp only [Nat.cast_pow, Real.log_pow]
      _ <= |Real.log (((p.1 ^ m : ℕ) : ℝ))| := le_abs_self _
      _ <= owner.supportRadius := hsupport
  nlinarith

/-- The canonical visible-prime list has support-controlled cardinality. -/
theorem canonicalVisiblePrimes_length_le_supportCardinality
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner) :
    (canonicalFamily owner).visiblePrimes.length <=
      Nat.ceil (Real.exp owner.supportRadius) + 1 := by
  classical
  let cutoff := owner.supportRadius
  let S := (canonicalFamily owner).visiblePrimes
  have hfilter :
      S.filter (fun p : CCM24VisiblePrime => Real.log (p : ℝ) <= cutoff) = S := by
    apply List.filter_eq_self.2
    intro p hp
    exact decide_eq_true (by
      simpa only [cutoff] using
        canonicalVisiblePrime_log_le_supportRadius owner hp)
  have hlength := length_filter_log_le cutoff S
    (canonicalFamily owner).visiblePrimes_nodup
  rw [hfilter] at hlength
  exact hlength

/-- The inverse lower-factor square of the canonical family is bounded by a
function of the same owner's compact support radius only. -/
theorem canonicalFiniteEulerLowerFactor_inv_sq_le_supportCardinality
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner) :
    ((finiteEulerLowerFactor (canonicalFamily owner).visiblePrimes) ^ 2)⁻¹ <=
      (16 : ℝ) ^
        (Nat.ceil (Real.exp owner.supportRadius) + 1) := by
  calc
    ((finiteEulerLowerFactor (canonicalFamily owner).visiblePrimes) ^ 2)⁻¹ <=
        (16 : ℝ) ^ (canonicalFamily owner).visiblePrimes.length :=
      finiteEulerLowerFactor_inv_sq_le_sixteen_pow_length _
    _ <= (16 : ℝ) ^
        (Nat.ceil (Real.exp owner.supportRadius) + 1) := by
      exact pow_le_pow_right₀ (by norm_num)
        (canonicalVisiblePrimes_length_le_supportCardinality owner)

/-! ## Canonical real Gate -/

/-- Explicit majorant for the canonical real Gate.  Its finite-Euler cost is
a function of the selected support radius; its remaining terms are the fixed
completed physical energy of the same compact root. -/
noncomputable def canonicalRealGate3USupportMajorant
    {nu : Type*} (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (a c : ℝ)
    (globalBasis : HilbertBasis nu ℂ finiteSCarrier) : ℝ :=
  (16 : ℝ) ^
      (Nat.ceil (Real.exp owner.supportRadius) + 1) *
    (6 + 2 * (∑' i, ‖sourceProlateHilbertSchmidtFactor lambda
      (globalBasis i)‖ ^ 2)) *
    ((c - a) ^ 2 *
      SchwartzMap.seminorm ℂ 0 0 owner.sourceTest.test ^ 2)

/-- The existing raw endpoint estimate and the support-controlled canonical
lower factor prove the canonical-family real Gate 3U contract outright. -/
theorem canonicalRealGate3UAt_of_supportMajorant
    {rho : Type*} (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale)
    (a c : ℝ) (hac : a <= c)
    (hsupp : Function.support owner.sourceTest.test <= Set.Icc a c)
    {iota kappa tau iotaR kappaR tauR nu mu : Type*}
    (negativeBasis : HilbertBasis iota ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis kappa ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis tau ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (reflectedNegativeBasis : HilbertBasis iotaR ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (reflectedPositiveBasis : HilbertBasis kappaR ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (reflectedOutputBasis : HilbertBasis tauR ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis nu ℂ finiteSCarrier)
    (boundaryBasis : HilbertBasis mu ℂ (commonBoundaryCarrier a c))
    (sourceBasis : HilbertBasis rho ℂ (sourceSoninCarrier lambda))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2) :
    canonicalRealGate3UAt owner lambda sourceBasis
      (canonicalRealGate3USupportMajorant owner lambda a c globalBasis) := by
  rw [canonicalRealGate3UAt_iff_sourceBandRealBound]
  have hraw := sourceBandGramTrace_norm_le_invLowerFactorSq_supportEnergy
    owner lambda (canonicalFamily owner) a c hac hsupp negativeBasis
    positiveBasis outputBasis reflectedNegativeBasis reflectedPositiveBasis
    reflectedOutputBasis globalBasis boundaryBasis sourceBasis hfactor
  have hinv :=
    canonicalFiniteEulerLowerFactor_inv_sq_le_supportCardinality owner
  calc
    |(ordinaryTraceAlong sourceBasis
        (sourceBandGramResponse owner lambda (canonicalFamily owner))).re| <=
      ‖ordinaryTraceAlong sourceBasis
        (sourceBandGramResponse owner lambda (canonicalFamily owner))‖ :=
          Complex.abs_re_le_norm _
    _ <= ((finiteEulerLowerFactor
          (canonicalFamily owner).visiblePrimes) ^ 2)⁻¹ *
        (6 + 2 * (∑' i, ‖sourceProlateHilbertSchmidtFactor lambda
          (globalBasis i)‖ ^ 2)) *
        ((c - a) ^ 2 *
          SchwartzMap.seminorm ℂ 0 0 owner.sourceTest.test ^ 2) := hraw
    _ <= (16 : ℝ) ^
          (Nat.ceil (Real.exp owner.supportRadius) + 1) *
        (6 + 2 * (∑' i, ‖sourceProlateHilbertSchmidtFactor lambda
          (globalBasis i)‖ ^ 2)) *
        ((c - a) ^ 2 *
          SchwartzMap.seminorm ℂ 0 0 owner.sourceTest.test ^ 2) := by
      gcongr
    _ = canonicalRealGate3USupportMajorant owner lambda a c globalBasis := rfl

end CCM24FiniteSCanonicalSupportGate3U
end CCM25Concrete
end Source
end ConnesWeilRH
