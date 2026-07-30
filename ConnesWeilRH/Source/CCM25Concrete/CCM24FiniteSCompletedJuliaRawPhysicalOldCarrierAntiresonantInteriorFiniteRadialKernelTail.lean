/-
Copyright (c) 2026 Connes-WeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantGeometricBoundaryResolvent
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorSwappedLocalPairRadialColumnBridge
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSSchurMarkovPolarTraceBridge

/-!
# Kernel and exact tail of a finite radial column

Proof 639 retains only the first `N` cells of the genuine radial renewal

```text
q C u, q^2 C V u, ..., q^N C V^(N-1) u.
```

This module determines what that finite observation does and does not see.
The complete geometric radial boundary has the exact finite-prefix split

```text
G u = sum_(n < N) q^(n+1) C V^n u + q^N G(V^N u).
```

Consequently, on the kernel of Proof 639's finite column, the whole radial
response is exactly the unobserved tail `q^N G(V^N u)`; it is not zero by
formal renewal algebra.  The module also proves directly on the actual
whole-line `L2` carrier that every vector whose support starts at least `N`
prime cells beyond the CCM24 radial boundary lies in this finite-column
kernel.

Thus a factorization of the complete swapped cofactor through a fixed finite
column requires a new source theorem annihilating the complete coupled
cofactor on all such tail vectors.  Compactness, trace cancellation, and the
finite-column norm bound do not provide that theorem.  No physical branch is
split here, and no claim is made that an actual tail vector survives the
complete cofactor.  Bone 1, Gate 3U, the finite-S sign, Burnol's identity, and
RH remain open.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorFiniteRadialKernelTail

open MeasureTheory Set
open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CCM24FiniteSActualJuliaRangeSineAmbientScaleGuard
open CCM24FiniteSActualSchurCascade
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantGeometricBoundaryReadout
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantGeometricBoundaryResolvent
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorFiniteRadialBlockColumn
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorSwappedLocalPairRadialColumnBridge
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantRadialBlockRecurrence
open CCM24FiniteSFrameGramCalculus
open CCM24FiniteSProjectionTrace
open CCM24FiniteSSchurMarkovPolarTraceBridge

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-! ## Exact finite-prefix decomposition of the genuine radial renewal -/

/-- The operator-valued prefix corresponding exactly to Proof 639's first
`N` orthogonal coordinates. -/
noncomputable def primeEulerRadialGeometricBoundaryPrefix
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime) (N : Nat) :
    finiteSCarrier →L[ℂ] finiteSCarrier :=
  ∑ n ∈ Finset.range N,
    primeEulerRadialGeometricBoundaryTerm lambda p n

/-- Shifting the geometric series by `N` cells factors out the genuine Euler
weight and the `N`th radial-tail iterate. -/
theorem tsum_primeEulerRadialGeometricBoundaryTerm_add_eq_tail
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime) (N : Nat) :
    (∑' n : Nat,
        primeEulerRadialGeometricBoundaryTerm lambda p (n + N)) =
      ((ccm24PrimeEulerCoefficient p : ℂ) ^ N) •
        (primeEulerRadialGeometricBoundary lambda p ∘L
          (primeEulerRadialTail lambda p) ^ N) := by
  let term := primeEulerRadialGeometricBoundaryTerm lambda p
  let V := primeEulerRadialTail lambda p
  have hterm : Summable term :=
    summable_primeEulerRadialGeometricBoundaryTerm lambda p
  have hshift : ∀ n : Nat,
      term (n + N) =
        ((ccm24PrimeEulerCoefficient p : ℂ) ^ N) •
          (term n ∘L V ^ N) := by
    intro n
    induction N with
    | zero =>
        apply ContinuousLinearMap.ext
        intro x
        simp only [add_zero, pow_zero, one_smul,
          ContinuousLinearMap.comp_apply, ContinuousLinearMap.one_apply]
    | succ N ih =>
        have ih' :
            primeEulerRadialGeometricBoundaryTerm lambda p (n + N) =
              ((ccm24PrimeEulerCoefficient p : ℂ) ^ N) •
                (primeEulerRadialGeometricBoundaryTerm lambda p n ∘L
                  (primeEulerRadialTail lambda p) ^ N) := by
          simpa only [term, V] using ih
        change
          primeEulerRadialGeometricBoundaryTerm lambda p (n + (N + 1)) =
            ((ccm24PrimeEulerCoefficient p : ℂ) ^ (N + 1)) •
              (primeEulerRadialGeometricBoundaryTerm lambda p n ∘L
                (primeEulerRadialTail lambda p) ^ (N + 1))
        rw [show n + (N + 1) = (n + N) + 1 by omega]
        rw [primeEulerRadialGeometricBoundaryTerm_succ, ih']
        apply ContinuousLinearMap.ext
        intro x
        simp only [ContinuousLinearMap.comp_apply,
          ContinuousLinearMap.smul_apply, smul_smul, pow_succ,
          ContinuousLinearMap.mul_apply]
        module
  calc
    (∑' n : Nat, term (n + N)) =
        ∑' n : Nat,
          ((ccm24PrimeEulerCoefficient p : ℂ) ^ N) •
            (term n ∘L V ^ N) := tsum_congr hshift
    _ = ((ccm24PrimeEulerCoefficient p : ℂ) ^ N) •
        (∑' n : Nat, term n ∘L V ^ N) := by
      rw [tsum_const_smul'']
    _ = ((ccm24PrimeEulerCoefficient p : ℂ) ^ N) •
        ((∑' n : Nat, term n) ∘L V ^ N) := by
      congr 1
      change (∑' n : Nat, term n * V ^ N) =
        (∑' n : Nat, term n) * V ^ N
      rw [hterm.tsum_mul_right]
    _ = ((ccm24PrimeEulerCoefficient p : ℂ) ^ N) •
        (primeEulerRadialGeometricBoundary lambda p ∘L
          (primeEulerRadialTail lambda p) ^ N) := by
      rfl

/-- The complete radial renewal is its first `N` cells plus one exact
unobserved tail.  This identity is valid for every finite `N`; no support or
route-validity premise is used. -/
theorem primeEulerRadialGeometricBoundary_eq_prefix_add_tail
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime) (N : Nat) :
    primeEulerRadialGeometricBoundary lambda p =
      primeEulerRadialGeometricBoundaryPrefix lambda p N +
        ((ccm24PrimeEulerCoefficient p : ℂ) ^ N) •
          (primeEulerRadialGeometricBoundary lambda p ∘L
            (primeEulerRadialTail lambda p) ^ N) := by
  let term := primeEulerRadialGeometricBoundaryTerm lambda p
  have hterm : Summable term :=
    summable_primeEulerRadialGeometricBoundaryTerm lambda p
  calc
    primeEulerRadialGeometricBoundary lambda p =
        ∑' n : Nat, term n := by rfl
    _ = (∑ n ∈ Finset.range N, term n) +
        ∑' n : Nat, term (n + N) := by
      exact (hterm.sum_add_tsum_nat_add N).symm
    _ = primeEulerRadialGeometricBoundaryPrefix lambda p N +
        ((ccm24PrimeEulerCoefficient p : ℂ) ^ N) •
          (primeEulerRadialGeometricBoundary lambda p ∘L
            (primeEulerRadialTail lambda p) ^ N) := by
      rw [tsum_primeEulerRadialGeometricBoundaryTerm_add_eq_tail]
      rfl

/-! ## What a zero finite column actually implies -/

/-- Exact kernel description of Proof 639's column: it vanishes precisely
when each of the first `N` unweighted radial boundary blocks vanishes.  The
Euler weights lose no kernel because `q_p > 0`. -/
theorem finiteRadialColumn_eq_zero_iff_first_boundary_blocks_eq_zero
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) (N : Nat)
    (x : sourceSoninCarrier lambda) :
    finitePrimeEulerRadialGeometricBoundaryColumn lambda p S N x = 0 ↔
      ∀ n : Nat, n < N →
        primeEulerRadialBoundaryStep lambda p
          (((primeEulerRadialTail lambda p) ^ n)
            (newSuffixFrame lambda S x)) = 0 := by
  have hq : (ccm24PrimeEulerCoefficient p : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr
      (ne_of_gt (ccm24PrimeEulerCoefficient_pos p))
  constructor
  · intro hcolumn n hn
    let i : Fin N := ⟨n, hn⟩
    have hi := congrArg
      (fun y : PiLp 2 (fun _ : Fin N => finiteSCarrier) => y i) hcolumn
    have hweighted :
        ((ccm24PrimeEulerCoefficient p : ℂ) ^ (n + 1)) •
          primeEulerRadialBoundaryStep lambda p
            (((primeEulerRadialTail lambda p) ^ n)
              (newSuffixFrame lambda S x)) = 0 := by
      simpa only [finitePrimeEulerRadialGeometricBoundaryColumn_apply,
        primeEulerRadialGeometricBoundaryTerm,
        ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
        PiLp.zero_apply, i] using hi
    exact (smul_eq_zero.mp hweighted).resolve_left
      (pow_ne_zero (n + 1) hq)
  · intro hblocks
    apply PiLp.ext
    intro i
    have hi := hblocks i i.isLt
    simp only [finitePrimeEulerRadialGeometricBoundaryColumn_apply,
      primeEulerRadialGeometricBoundaryTerm,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
      hi, smul_zero, PiLp.zero_apply]

/-- A zero finite orthogonal column kills exactly its operator-valued prefix. -/
theorem prefix_apply_eq_zero_of_finiteRadialColumn_eq_zero
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) (N : Nat)
    (x : sourceSoninCarrier lambda)
    (hcolumn :
      finitePrimeEulerRadialGeometricBoundaryColumn lambda p S N x = 0) :
    primeEulerRadialGeometricBoundaryPrefix lambda p N
        (newSuffixFrame lambda S x) = 0 := by
  have hterm : ∀ n ∈ Finset.range N,
      primeEulerRadialGeometricBoundaryTerm lambda p n
          (newSuffixFrame lambda S x) = 0 := by
    intro n hn
    have hnlt : n < N := Finset.mem_range.mp hn
    let i : Fin N := ⟨n, hnlt⟩
    have hi := congrArg
      (fun y : PiLp 2 (fun _ : Fin N => finiteSCarrier) => y i) hcolumn
    simpa only [finitePrimeEulerRadialGeometricBoundaryColumn_apply,
      PiLp.zero_apply] using hi
  change (ContinuousLinearMap.apply ℂ finiteSCarrier
      (newSuffixFrame lambda S x))
    (∑ n ∈ Finset.range N,
      primeEulerRadialGeometricBoundaryTerm lambda p n) = 0
  rw [map_sum]
  exact Finset.sum_eq_zero hterm

/-- On the finite-column kernel, the complete geometric radial response is
precisely the unobserved `N`-cell tail.  A finite prefix therefore gives no
formal kernel containment for the complete renewal. -/
theorem geometricBoundary_apply_eq_tail_of_finiteRadialColumn_eq_zero
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) (N : Nat)
    (x : sourceSoninCarrier lambda)
    (hcolumn :
      finitePrimeEulerRadialGeometricBoundaryColumn lambda p S N x = 0) :
    primeEulerRadialGeometricBoundary lambda p
        (newSuffixFrame lambda S x) =
      ((ccm24PrimeEulerCoefficient p : ℂ) ^ N) •
        primeEulerRadialGeometricBoundary lambda p
          (((primeEulerRadialTail lambda p) ^ N)
            (newSuffixFrame lambda S x)) := by
  have hprefix := prefix_apply_eq_zero_of_finiteRadialColumn_eq_zero
    lambda p S N x hcolumn
  have hsplit := congrArg
    (fun operator : finiteSCarrier →L[ℂ] finiteSCarrier =>
      operator (newSuffixFrame lambda S x))
    (primeEulerRadialGeometricBoundary_eq_prefix_add_tail lambda p N)
  simpa only [ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    hprefix, zero_add] using hsplit

/-! ## Actual deep radial-support kernel -/

/-- A vector has an `N`-cell radial margin when it vanishes below the CCM24
boundary advanced by `N * log(p)`. -/
def HasPrimeRadialCellMargin
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (N : Nat) (u : finiteSCarrier) : Prop :=
  ∀ᵐ t : ℝ ∂volume,
    t < Real.log lambda + (N : ℝ) * Real.log p → u t = 0

/-- One positive prime translation consumes exactly one radial support cell. -/
theorem hasPrimeRadialCellMargin_translation_of_succ
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (N : Nat) (u : finiteSCarrier)
    (hu : HasPrimeRadialCellMargin lambda p (N + 1) u) :
    HasPrimeRadialCellMargin lambda p N
      (cc20GlobalLogTranslation (Real.log p) u) := by
  have hshift :=
    (measurePreserving_add_right volume (Real.log p)).quasiMeasurePreserving.ae
      hu
  filter_upwards
    [cc20GlobalLogTranslation_coeFn (Real.log p) u, hshift] with
      t htranslation hzero
  intro ht
  rw [htranslation]
  apply hzero
  push_cast at ht ⊢
  nlinarith

/-- Every nonnegative radial margin implies membership in the base CCM24
radial-support subspace. -/
theorem mem_radialSupport_of_hasPrimeRadialCellMargin
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (N : Nat) (u : finiteSCarrier)
    (hu : HasPrimeRadialCellMargin lambda p N u) :
    u ∈ ccm24LogRadialSupportClosedSubspace lambda := by
  rw [mem_ccm24LogRadialSupportClosedSubspace_iff]
  filter_upwards [hu] with t hzero
  intro ht
  apply hzero
  have hp : 0 ≤ Real.log (p : ℝ) :=
    Real.log_nonneg (by exact_mod_cast p.property.le)
  have hmargin : 0 ≤ (N : ℝ) * Real.log (p : ℝ) :=
    mul_nonneg (Nat.cast_nonneg N) hp
  linarith

/-- At one occupied margin cell, the current boundary block vanishes and the
compressed radial tail is the literal positive translation. -/
theorem boundaryStep_eq_zero_and_tail_eq_translation_of_margin_succ
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (N : Nat) (u : finiteSCarrier)
    (hu : HasPrimeRadialCellMargin lambda p (N + 1) u) :
    primeEulerRadialBoundaryStep lambda p u = 0 ∧
      primeEulerRadialTail lambda p u =
        cc20GlobalLogTranslation (Real.log p) u := by
  have huMem := mem_radialSupport_of_hasPrimeRadialCellMargin
    lambda p (N + 1) u hu
  have htranslatedMargin :=
    hasPrimeRadialCellMargin_translation_of_succ lambda p N u hu
  have htranslatedMem := mem_radialSupport_of_hasPrimeRadialCellMargin
    lambda p N (cc20GlobalLogTranslation (Real.log p) u)
      htranslatedMargin
  have huFixed : radialSupportProjection lambda u = u := by
    exact Submodule.starProjection_eq_self_iff.mpr huMem
  have htranslatedFixed :
      radialSupportProjection lambda
          (cc20GlobalLogTranslation (Real.log p) u) =
        cc20GlobalLogTranslation (Real.log p) u := by
    exact Submodule.starProjection_eq_self_iff.mpr htranslatedMem
  constructor
  · simp only [primeEulerRadialBoundaryStep, radialComplement,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.id_apply, huFixed]
    change cc20GlobalLogTranslation (Real.log p) u -
      radialSupportProjection lambda
        (cc20GlobalLogTranslation (Real.log p) u) = 0
    rw [htranslatedFixed, sub_self]
  · simp only [primeEulerRadialTail, ContinuousLinearMap.comp_apply,
      huFixed]
    change radialSupportProjection lambda
      (cc20GlobalLogTranslation (Real.log p) u) =
        cc20GlobalLogTranslation (Real.log p) u
    exact htranslatedFixed

/-- A vector beginning `N` cells beyond the radial boundary is invisible to
every one of the first `N` genuine boundary blocks. -/
theorem boundaryStep_tail_pow_eq_zero_of_hasPrimeRadialCellMargin
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (N : Nat) (u : finiteSCarrier)
    (hu : HasPrimeRadialCellMargin lambda p N u) :
    ∀ n : Nat, n < N →
      primeEulerRadialBoundaryStep lambda p
        (((primeEulerRadialTail lambda p) ^ n) u) = 0 := by
  induction N generalizing u with
  | zero =>
      intro n hn
      omega
  | succ N ih =>
      intro n hn
      have hstep :=
        boundaryStep_eq_zero_and_tail_eq_translation_of_margin_succ
          lambda p N u (by simpa only [Nat.succ_eq_add_one] using hu)
      cases n with
      | zero =>
          simpa only [pow_zero, ContinuousLinearMap.one_apply] using hstep.1
      | succ n =>
          have hnN : n < N := Nat.lt_of_succ_lt_succ hn
          have htranslatedMargin :=
            hasPrimeRadialCellMargin_translation_of_succ lambda p N u
              (by simpa only [Nat.succ_eq_add_one] using hu)
          have htailMargin : HasPrimeRadialCellMargin lambda p N
              (primeEulerRadialTail lambda p u) := by
            rwa [hstep.2]
          have hzero := ih
            (primeEulerRadialTail lambda p u) htailMargin n hnN
          rw [primeEulerRadialTailIterate_succ_apply]
          exact hzero

/-- Source-facing form: any actual suffix vector with an `N`-cell radial
margin lies in the kernel of Proof 639's first-`N` column. -/
theorem finiteRadialColumn_eq_zero_of_newFrame_hasPrimeRadialCellMargin
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) (N : Nat)
    (x : sourceSoninCarrier lambda)
    (hmargin : HasPrimeRadialCellMargin lambda p N
      (newSuffixFrame lambda S x)) :
    finitePrimeEulerRadialGeometricBoundaryColumn lambda p S N x = 0 := by
  apply PiLp.ext
  intro i
  have hblock :=
    boundaryStep_tail_pow_eq_zero_of_hasPrimeRadialCellMargin
      lambda p N (newSuffixFrame lambda S x) hmargin i i.isLt
  simp only [finitePrimeEulerRadialGeometricBoundaryColumn_apply,
    primeEulerRadialGeometricBoundaryTerm,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    hblock, smul_zero, PiLp.zero_apply]

/-! ## Exact missing producer for finite-column kernel containment -/

/-- Any supplied finite-column readout must annihilate the complete coupled
cofactor on every actual tail vector with `N`-cell radial margin.  This is the
source theorem which a finite-cell route must establish; Proof 639's norm
bound does not imply it. -/
theorem completeCofactor_eq_zero_of_margin_of_finiteRadialReadoutData
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {p : CCM24VisiblePrime}
    {S : List CCM24VisiblePrime} {N : Nat} {bound : Real}
    (data : SuffixSwappedLocalCofactorFiniteRadialReadoutData
      owner lambda p S N bound)
    (x : sourceSoninCarrier lambda)
    (hmargin : HasPrimeRadialCellMargin lambda p N
      (newSuffixFrame lambda S x)) :
    suffixActualBandCompleteSwappedLocalCofactor owner lambda p S x = 0 := by
  apply completeSwappedLocalCofactor_eq_zero_of_finiteRadialColumn_eq_zero
    data x
  exact finiteRadialColumn_eq_zero_of_newFrame_hasPrimeRadialCellMargin
    lambda p S N x hmargin

/-- Conversely, one complete-cofactor survivor in the explicit radial tail
kernel rules out every bounded readout through that fixed finite column. -/
theorem no_finiteRadialReadoutData_of_margin_cofactor_survivor
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {p : CCM24VisiblePrime}
    {S : List CCM24VisiblePrime} {N : Nat}
    (x : sourceSoninCarrier lambda)
    (hmargin : HasPrimeRadialCellMargin lambda p N
      (newSuffixFrame lambda S x))
    (hsurvivor :
      suffixActualBandCompleteSwappedLocalCofactor owner lambda p S x ≠ 0)
    (bound : Real) :
    ¬ Nonempty (SuffixSwappedLocalCofactorFiniteRadialReadoutData
      owner lambda p S N bound) := by
  rintro ⟨data⟩
  exact hsurvivor
    (completeCofactor_eq_zero_of_margin_of_finiteRadialReadoutData
      data x hmargin)

end
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorFiniteRadialKernelTail
end CCM25Concrete
end Source
end ConnesWeilRH
