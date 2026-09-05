/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1P2DefectZeroSumIdentity

/-!
# Record 1143 audit: axiom checks and fidelity example for the P2
zero-sum identity brick.

Gate G2: every brick declaration prints exactly
`'ConnesWeilRH.Source.C1P2DefectZeroSumIdentity.*' does not depend on any
axioms` beyond `[propext, Classical.choice, Quot.sound]` and carries zero
`sorryAx`.
Gate G3: the fidelity example re-derives the spectral-difference form
from explicit hypotheses.
-/

open ConnesWeilRH Source C1P2DefectZeroSumIdentity
open CCM25Concrete.CompactLogConvolution
open C1HealthyYoshidaDetector
open C1LocalConfigurationDomination
open C1SpectralWeil

#print axioms icgate_convolutionSquare_eq_neg_qw
#print axioms defectGate_eq_qw_sub
#print axioms defectGate_eq_spectralValue_sub
#print axioms defectGate_gt_add_mu
#print axioms defectGate_gt_add_mu_of_qw_negative

-- G3 fidelity: the zero-sum form, re-derived from explicit hypotheses.
example (g W : CompactLogTest)
    (hgv : CC20VanishesOn C1.healthyCC20TestSpace
      cc20TripleFiniteVanishingSet g)
    (hWv : CC20VanishesOn C1.healthyCC20TestSpace
      cc20TripleFiniteVanishingSet W) :
    ICgate (ICdefect g.convolutionSquare {()}
      (fun _ => W.convolutionSquare) (fun _ => 1))
      = spectralWeilValue W.convolutionSquare
        - spectralWeilValue g.convolutionSquare :=
  defectGate_eq_spectralValue_sub g W hgv hWv
