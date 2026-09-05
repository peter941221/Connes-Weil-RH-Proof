/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1T2Assembly
import ConnesWeilRH.Dev.C1XiCenterTwoArithmeticAssembly

/-!
# Record 1143: P2 zero-sum identity audit (pre-brick B1 of map 005)

Statement-level identity audit for the single remaining C3 obligation P2.
No sign theorem is asserted and RH is not claimed; every ingredient is a
landed result (record 1123 `defectGate_singleton_eq_sub`, the triple-
vanishing `qw` readback in `C1HealthyYoshidaDetector`, the `psi`/`qw`
definitions in `C1SameOwnerWeil`, and the unconditional arithmetic-
spectral balance `centerTwo_arithmetic_eq_spectral` in
`C1XiCenterTwoArithmeticAssembly`).

The chain pinned here, for triple-vanishing healthy detectors `g` and
windows `W`:

* `ICgate F.convolutionSquare = - qw F` (the 1140 gate arithmetic, as a
  named equation).
* The one-window Stage-B defect gate is the difference of the same-owner
  Weil values: `qw W - qw g`.
* Zero-sum form: the defect gate is the spectral difference
  `spectralWeilValue W.convolutionSquare - spectralWeilValue g.convolutionSquare`.
* Positive-form admission wall: any certified window (`hcert`) forces
  `mu < ICgate (ICdefect ...)` from the bare positivity of the detector
  gate - with no vanishing input - and from the detector negativity `qw g < 0`.

This is the formal core behind the Line-S verdict delivered in
docs/proofs/1144: a channel decomposition of the spectral difference sums
to the same number, so no rearrangement can bring the defect gate under
`epsilon <= mu`.
-/

namespace ConnesWeilRH
namespace Source
namespace C1P2DefectZeroSumIdentity

open MeasureTheory Set Filter
open CCM25Concrete.CompactLogConvolution
open C1HboxRationalData
open C1GateLevelTransferClasses
open C1HkerSpan
open C1WindowRationalIngest
open C1LocalConfigurationDomination
open C1SameOwnerWeil
open C1HealthyYoshidaDetector
open C1GateMatrixRepresentation
open C1ArchimedeanIntegrabilityGeneric
open C1OrbitWindowSemiLocalGate
open C1SpectralWeil
open C1XiCenterTwoArithmeticAssembly
open scoped BigOperators ContDiff Filter Topology

/-- S1: on a triple-vanishing healthy test the configuration gate of the
Hermitian square is exactly the negative same-owner Weil value. -/
theorem icgate_convolutionSquare_eq_neg_qw (F : CompactLogTest)
    (hvanish : CC20VanishesOn C1.healthyCC20TestSpace
      cc20TripleFiniteVanishingSet F) :
    ICgate F.convolutionSquare = -C1SameOwnerWeil.qw F := by
  unfold ICgate
  have h :=
    qw_eq_neg_archimedeanTerm_sub_finitePrimeSum_of_vanishesOn_cc20Triple
      F hvanish
  linarith

/-- S2: the one-window Stage-B defect gate is the difference of the
same-owner Weil values of window and detector. -/
theorem defectGate_eq_qw_sub (g W : CompactLogTest)
    (hgv : CC20VanishesOn C1.healthyCC20TestSpace
      cc20TripleFiniteVanishingSet g)
    (hWv : CC20VanishesOn C1.healthyCC20TestSpace
      cc20TripleFiniteVanishingSet W) :
    ICgate (ICdefect g.convolutionSquare {()}
      (fun _ => W.convolutionSquare) (fun _ => 1))
      = C1SameOwnerWeil.qw W - C1SameOwnerWeil.qw g := by
  rw [C1T2Assembly.defectGate_singleton_eq_sub g W,
    icgate_convolutionSquare_eq_neg_qw g hgv,
    icgate_convolutionSquare_eq_neg_qw W hWv]
  ring

/-- S3: zero-sum form - the defect gate is the spectral difference of the
two Hermitian squares, unconditionally on both factors. -/
theorem defectGate_eq_spectralValue_sub (g W : CompactLogTest)
    (hgv : CC20VanishesOn C1.healthyCC20TestSpace
      cc20TripleFiniteVanishingSet g)
    (hWv : CC20VanishesOn C1.healthyCC20TestSpace
      cc20TripleFiniteVanishingSet W) :
    ICgate (ICdefect g.convolutionSquare {()}
      (fun _ => W.convolutionSquare) (fun _ => 1))
      = spectralWeilValue W.convolutionSquare
        - spectralWeilValue g.convolutionSquare := by
  rw [defectGate_eq_qw_sub g W hgv hWv]

  have hW : C1SameOwnerWeil.qw W
      = spectralWeilValue W.convolutionSquare := by
    rw [C1SameOwnerWeil.qw_eq_psi_square]
    exact centerTwo_arithmetic_eq_spectral _
  have hg : C1SameOwnerWeil.qw g
      = spectralWeilValue g.convolutionSquare := by
    rw [C1SameOwnerWeil.qw_eq_psi_square]
    exact centerTwo_arithmetic_eq_spectral _
  rw [hW, hg]

/-- S4: the positive-form admission wall.  A certified window
(`ICgate W.convolutionSquare <= -mu`) and a positive detector gate force
the defect gate above `mu`.  No vanishing input is used. -/
theorem defectGate_gt_add_mu (g W : CompactLogTest) {mu : Real}
    (hgpos : 0 < ICgate g.convolutionSquare)
    (hcert : ICgate W.convolutionSquare ≤ -mu) :
    mu < ICgate (ICdefect g.convolutionSquare {()}
      (fun _ => W.convolutionSquare) (fun _ => 1)) := by
  rw [C1T2Assembly.defectGate_singleton_eq_sub g W]
  linarith

/-- S5: the same wall starting from the detector branch `qw g < 0` - the
gate positivity is re-derived exactly as in
`no_stageB_budget_of_qw_negative`. -/
theorem defectGate_gt_add_mu_of_qw_negative (g W : CompactLogTest)
    (hgv : CC20VanishesOn C1.healthyCC20TestSpace
      cc20TripleFiniteVanishingSet g)
    (hnegative : C1SameOwnerWeil.qw g < 0) {mu : Real}
    (hcert : ICgate W.convolutionSquare ≤ -mu) :
    mu < ICgate (ICdefect g.convolutionSquare {()}
      (fun _ => W.convolutionSquare) (fun _ => 1)) := by
  refine defectGate_gt_add_mu g W ?_ hcert
  unfold ICgate
  have h :=
    qw_eq_neg_archimedeanTerm_sub_finitePrimeSum_of_vanishesOn_cc20Triple
      g hgv
  linarith

end C1P2DefectZeroSumIdentity
end Source
end ConnesWeilRH
