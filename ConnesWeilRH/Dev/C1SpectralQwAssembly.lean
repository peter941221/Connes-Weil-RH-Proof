import ConnesWeilRH.Dev.C1SpectralOfflinePairing
import ConnesWeilRH.Dev.C1SpectralSummability
import ConnesWeilRH.Dev.C1CenterTwoCriterionBridge
import ConnesWeilRH.Dev.C1SpectralVanishingTransfer

/-!
# C1SpectralQwAssembly - the hqw reduction ledger

This leaf assembles the landed blocks of the hqw sign attack
(`docs/proofs/1040_hqw_sign_attack.md` section 5) into the exact shape of the
remaining obligation:

```text
qw g = onLineSpectralMass g + offLineSpectralMass g        (W3 + Gate-2 face)
offLineSpectralMass g = 2 * Re (rightHalfSpectralSum g)    (W4b-pairing)
onLineSpectralMass g >= 0                                   (W1)
```

so that `0 <= qw g` follows from ONE named inequality about the right-half
spectral sum, or from its modulus form `offLineNormMass g <= onLineSpectralMass g`.
No vanishing hypothesis is consumed by the ledger itself: the reduction is pure
bookkeeping, and the role of the F-vanishing subspace is delegated entirely to
the inequality premise (that is where the RH content lives).

Consumers on the coverage chain: the two `hqw_of_forall_vanishing_*` theorems
produce exactly the per-test input of
`frontierStatus_healthyCriterionState_of_rankOneCorrection`
(`Dev/C1Stage3FrontierStatus.lean`) and match the right-hand side of
`healthyCriterionState_iff_all_vanishing_spectral_nonnegative`
(`Dev/C1CenterTwoCriterionBridge.lean`).
-/

namespace ConnesWeilRH
namespace Source
namespace C1SpectralQwAssembly

open CC20YoshidaNearZeros
open CCM25Concrete.CompactLogConvolution
open C1SameOwnerWeil
open C1SpectralWeil
open C1SpectralOnlineSplit
open C1SpectralOfflinePairing
open C1SpectralSummability
open C1CenterTwoCriterionBridge
open C1SpectralVanishingTransfer

noncomputable section

/-! ### The two-block ledger -/

/-- The right-half spectral sum whose real part carries the off-line residual
after the W4b-pairing collapse. -/
def rightHalfSpectralSum (g : CompactLogTest) : Complex :=
  ∑' rho : sourceNontrivialZeroSet,
    Set.indicator rightHalfOffLine (spectralTerm g.convolutionSquare) rho

theorem summable_rightHalfSpectralTerm (g : CompactLogTest) :
    Summable (fun rho : sourceNontrivialZeroSet =>
      Set.indicator rightHalfOffLine (spectralTerm g.convolutionSquare) rho) :=
  (spectralSummable g.convolutionSquare).indicator rightHalfOffLine

/-- The Weil value of one root splits into its critical-line mass and its
off-line residual.  Unconditional in `g`: absolute summability holds for every
compact log test. -/
theorem qw_eq_onLineSpectralMass_add_offLineSpectralMass (g : CompactLogTest) :
    C1SameOwnerWeil.qw g = onLineSpectralMass g + offLineSpectralMass g := by
  rw [qw_eq_spectralWeilValue_centerTwo]
  exact spectralWeilValue_eq_onLineSpectralMass_add_offLineSpectralMass g
    (spectralSummable g.convolutionSquare)

/-- The ledger in pair form: the off-line residual is collapsed onto the right
half by the W4b-pairing involution reindex. -/
theorem qw_eq_onLine_add_two_mul_re_rightHalfSpectralSum (g : CompactLogTest) :
    C1SameOwnerWeil.qw g = onLineSpectralMass g + 2 * (rightHalfSpectralSum g).re := by
  rw [qw_eq_onLineSpectralMass_add_offLineSpectralMass,
    offLineSpectralMass_eq_two_mul_re_tsum_rightHalf g
      (spectralSummable g.convolutionSquare)]
  rfl

/-! ### The right-half sufficient condition -/

/-- If the right-half spectral sum does not dip below minus half the on-line
mass, then `qw` is nonnegative.  This is the single named inequality of the
W4b-bound; the F-vanishing subspace enters only where this premise is proved. -/
theorem qw_nonneg_of_rightHalfSpectralSum_re_ge_neg_half_onLine
    (g : CompactLogTest)
    (hre : (rightHalfSpectralSum g).re ≥ -(1 / 2 : Real) * onLineSpectralMass g) :
    0 ≤ C1SameOwnerWeil.qw g := by
  rw [qw_eq_onLine_add_two_mul_re_rightHalfSpectralSum]
  linarith

/-! ### The modulus ladder -/

/-- The nonnegative scalar majorant series is summable for every compact log
test.  This is the absolute-convergence face of `spectralSummable`, read off
the same shell argument. -/
theorem summable_spectralNormTerm (F : CompactLogTest) :
    Summable (spectralNormTerm F) := by
  obtain ⟨B, hB, hpoint⟩ := exists_spectral_laplaceAt_dyadic_tail_bound F
  refine summable_of_shifted_geometric_shell_weight_bound
    (spectralNormTerm F) (fun rho => (xiMultiplicity rho : Real))
    spectralHeightShell (spectralNormTerm_nonnegative F)
    spectralHeightShell_partition spectralHeightShell_finite hB
    (by norm_num) (by norm_num)
    (fun n => spectralHeightMultiplicity_geometric_bound n) ?_
  intro n rho
  unfold spectralNormTerm
  exact mul_le_mul_of_nonneg_left (hpoint n rho)
    (Nat.cast_nonneg (xiMultiplicity rho))

/-- The norm of one off-line indicator term is the indicator of the scalar
majorant. -/
theorem norm_offLineSpectralTerm_eq (g : CompactLogTest)
    (rho : sourceNontrivialZeroSet) :
    ‖offLineSpectralTerm g rho‖ =
      Set.indicator offLineZeroSet (spectralNormTerm g.convolutionSquare) rho := by
  by_cases h : rho ∈ offLineZeroSet
  · rw [offLineSpectralTerm, Set.indicator_of_mem h, norm_spectralTerm,
      Set.indicator_of_mem h]
  · have e1 : offLineSpectralTerm g rho = 0 := by simp [offLineSpectralTerm, h]
    have e2 : Set.indicator offLineZeroSet
        (spectralNormTerm g.convolutionSquare) rho = 0 := by simp [h]
    rw [e1, e2, norm_zero]

/-- The total off-line modulus mass: the summed scalar majorant restricted to
the off-line zeros. -/
def offLineNormMass (g : CompactLogTest) : Real :=
  ∑' rho : sourceNontrivialZeroSet,
    Set.indicator offLineZeroSet (spectralNormTerm g.convolutionSquare) rho

/-- The off-line residual is bounded below by the negative of its modulus
mass.  This drops all cancellation structure: it is the termwise-cheapest
sufficient route to the sign. -/
theorem offLineSpectralMass_ge_neg_offLineNormMass (g : CompactLogTest) :
    -offLineNormMass g ≤ offLineSpectralMass g := by
  have hsumt : Summable (offLineSpectralTerm g) :=
    summable_offLineSpectralTerm g (spectralSummable g.convolutionSquare)
  have hsumn : Summable (fun rho : sourceNontrivialZeroSet =>
      Set.indicator offLineZeroSet (spectralNormTerm g.convolutionSquare) rho) :=
    (summable_spectralNormTerm g.convolutionSquare).indicator offLineZeroSet
  have habs : Summable (fun rho : sourceNontrivialZeroSet =>
      ‖offLineSpectralTerm g rho‖) :=
    hsumn.congr fun rho => (norm_offLineSpectralTerm_eq g rho).symm
  have hnormeq : (∑' rho : sourceNontrivialZeroSet, ‖offLineSpectralTerm g rho‖) =
      offLineNormMass g :=
    tsum_congr fun rho => norm_offLineSpectralTerm_eq g rho
  have hchain : ‖∑' rho : sourceNontrivialZeroSet, offLineSpectralTerm g rho‖ ≤
      offLineNormMass g :=
    (norm_tsum_le_tsum_norm habs).trans hnormeq.le
  have habsre : |(∑' rho : sourceNontrivialZeroSet, offLineSpectralTerm g rho).re| ≤
      ‖∑' rho : sourceNontrivialZeroSet, offLineSpectralTerm g rho‖ :=
    Complex.abs_re_le_norm _
  have hre : -offLineNormMass g ≤
      (∑' rho : sourceNontrivialZeroSet, offLineSpectralTerm g rho).re := by
    have hneg : -‖∑' rho : sourceNontrivialZeroSet, offLineSpectralTerm g rho‖ ≤
        (∑' rho : sourceNontrivialZeroSet, offLineSpectralTerm g rho).re := by
      have hle := neg_le_abs
        (∑' rho : sourceNontrivialZeroSet, offLineSpectralTerm g rho).re
      linarith
    linarith
  unfold offLineSpectralMass
  exact hre

/-- The modulus ladder: `qw` beats the on-line mass minus the off-line modulus
mass. -/
theorem qw_ge_onLine_sub_offLineNormMass (g : CompactLogTest) :
    C1SameOwnerWeil.qw g ≥ onLineSpectralMass g - offLineNormMass g := by
  rw [qw_eq_onLineSpectralMass_add_offLineSpectralMass]
  linarith [offLineSpectralMass_ge_neg_offLineNormMass g]

/-- Modulus-form sufficient condition: if the off-line modulus mass is
dominated by the on-line mass, then `qw` is nonnegative. -/
theorem qw_nonneg_of_offLineNormMass_le_onLineSpectralMass
    (g : CompactLogTest)
    (hle : offLineNormMass g ≤ onLineSpectralMass g) :
    0 ≤ C1SameOwnerWeil.qw g := by
  have h := qw_ge_onLine_sub_offLineNormMass g
  linarith

/-! ### The arithmetic binding (vanishing face) -/

/-- On the F-vanishing subspace (for `F` containing the half node), the
two-block spectral ledger equals the pole-free arithmetic readback of W2.
This is the identity a W4b-bound attack from the arithmetic side must close. -/
theorem onLine_add_offLine_eq_neg_archimedeanTerm_sub_finitePrimeSum
    {F : Finset CriticalVanishingPoint} (g : CompactLogTest)
    (hhalf : CriticalVanishingPoint.half ∈ F)
    (hvanishes : CC20VanishesOn C1.healthyCC20TestSpace F g) :
    onLineSpectralMass g + offLineSpectralMass g =
      -C1SameOwnerWeil.archimedeanTerm g.convolutionSquare -
        C1SameOwnerWeil.finitePrimeSum g.convolutionSquare := by
  rw [← qw_eq_onLineSpectralMass_add_offLineSpectralMass g,
    qw_eq_neg_archimedeanTerm_sub_finitePrimeSum_of_vanishesOn_of_mem_half
      g hhalf hvanishes]

/-! ### The hqw reduction -/

/-- The route obligation `hqw` follows from the right-half inequality on the
vanishing subspace.  Pure bookkeeping: no vanishing input is consumed here. -/
theorem hqw_of_forall_vanishing_rightHalf_bound
    {F : Finset CriticalVanishingPoint}
    (hbound : ∀ g : CompactLogTest, CC20VanishesOn C1.healthyCC20TestSpace F g →
      (rightHalfSpectralSum g).re ≥ -(1 / 2 : Real) * onLineSpectralMass g) :
    ∀ g : CompactLogTest, CC20VanishesOn C1.healthyCC20TestSpace F g →
      0 ≤ C1SameOwnerWeil.qw g :=
  fun g hg => qw_nonneg_of_rightHalfSpectralSum_re_ge_neg_half_onLine g (hbound g hg)

/-- The same reduction in modulus form. -/
theorem hqw_of_forall_vanishing_offLineNormMass_le
    {F : Finset CriticalVanishingPoint}
    (hbound : ∀ g : CompactLogTest, CC20VanishesOn C1.healthyCC20TestSpace F g →
      offLineNormMass g ≤ onLineSpectralMass g) :
    ∀ g : CompactLogTest, CC20VanishesOn C1.healthyCC20TestSpace F g →
      0 ≤ C1SameOwnerWeil.qw g :=
  fun g hg => qw_nonneg_of_offLineNormMass_le_onLineSpectralMass g (hbound g hg)

/-! ### Axiom-cleanliness audit -/

#print axioms rightHalfSpectralSum
#print axioms summable_rightHalfSpectralTerm
#print axioms qw_eq_onLineSpectralMass_add_offLineSpectralMass
#print axioms qw_eq_onLine_add_two_mul_re_rightHalfSpectralSum
#print axioms qw_nonneg_of_rightHalfSpectralSum_re_ge_neg_half_onLine
#print axioms summable_spectralNormTerm
#print axioms norm_offLineSpectralTerm_eq
#print axioms offLineNormMass
#print axioms offLineSpectralMass_ge_neg_offLineNormMass
#print axioms qw_ge_onLine_sub_offLineNormMass
#print axioms qw_nonneg_of_offLineNormMass_le_onLineSpectralMass
#print axioms onLine_add_offLine_eq_neg_archimedeanTerm_sub_finitePrimeSum
#print axioms hqw_of_forall_vanishing_rightHalf_bound
#print axioms hqw_of_forall_vanishing_offLineNormMass_le

end
end C1SpectralQwAssembly
end Source
end ConnesWeilRH