/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1EntrywiseBound
import ConnesWeilRH.Dev.C1HboxRationalData
import ConnesWeilRH.Dev.C1TboxPullthrough

open Matrix

/-!
# Audit for record 1119 (Hbox data + T-box pull-through)

Focused axiom sweep (pre-registration section 3, G2) over every public
declaration of the three new modules, with zero `sorry` allowed; the
allowed axiom set is exactly {propext, Classical.choice, Quot.sound}.

The G3 fidelity shapes (section 2) are re-printed at the end as `example`
blocks: `tbox_q28`'s hypotheses are literally the radius form
`|Gt i j - Q28.G i j| <= radG_q28 i j`, and `absolute_true_q28`'s LHS is
literally `ICgate ((w).convolutionSquare)` with RHS `-mu_q28`.
-/

#print axioms ConnesWeilRH.Source.C1EntrywiseBound.qform_sym_half
#print axioms ConnesWeilRH.Source.C1EntrywiseBound.entrywise_triple

#print axioms ConnesWeilRH.Source.C1HboxRationalData.hsymRadG_q28
#print axioms ConnesWeilRH.Source.C1HboxRationalData.hsymRadM_q28
#print axioms ConnesWeilRH.Source.C1HboxRationalData.hrevG_q28
#print axioms ConnesWeilRH.Source.C1HboxRationalData.hrevM_q28
#print axioms ConnesWeilRH.Source.C1HboxRationalData.habsK_q28
#print axioms ConnesWeilRH.Source.C1HboxRationalData.habsLam_q28
#print axioms ConnesWeilRH.Source.C1HboxRationalData.hLamL_q28
#print axioms ConnesWeilRH.Source.C1HboxRationalData.hLLam_q28
#print axioms ConnesWeilRH.Source.C1HboxRationalData.hDredRad_q28
#print axioms ConnesWeilRH.Source.C1HboxRationalData.hRadp_q28
#print axioms ConnesWeilRH.Source.C1HboxRationalData.hsymRadG_q38
#print axioms ConnesWeilRH.Source.C1HboxRationalData.hsymRadM_q38
#print axioms ConnesWeilRH.Source.C1HboxRationalData.hrevG_q38
#print axioms ConnesWeilRH.Source.C1HboxRationalData.hrevM_q38
#print axioms ConnesWeilRH.Source.C1HboxRationalData.habsK_q38
#print axioms ConnesWeilRH.Source.C1HboxRationalData.habsLam_q38
#print axioms ConnesWeilRH.Source.C1HboxRationalData.hLamL_q38
#print axioms ConnesWeilRH.Source.C1HboxRationalData.hLLam_q38
#print axioms ConnesWeilRH.Source.C1HboxRationalData.hDredRad_q38
#print axioms ConnesWeilRH.Source.C1HboxRationalData.hRadp_q38
#print axioms ConnesWeilRH.Source.C1HboxRationalData.hsymRadG_q48
#print axioms ConnesWeilRH.Source.C1HboxRationalData.hsymRadM_q48
#print axioms ConnesWeilRH.Source.C1HboxRationalData.hrevG_q48
#print axioms ConnesWeilRH.Source.C1HboxRationalData.hrevM_q48
#print axioms ConnesWeilRH.Source.C1HboxRationalData.habsK_q48
#print axioms ConnesWeilRH.Source.C1HboxRationalData.habsLam_q48
#print axioms ConnesWeilRH.Source.C1HboxRationalData.hLamL_q48
#print axioms ConnesWeilRH.Source.C1HboxRationalData.hLLam_q48
#print axioms ConnesWeilRH.Source.C1HboxRationalData.hDredRad_q48
#print axioms ConnesWeilRH.Source.C1HboxRationalData.hRadp_q48

#print axioms ConnesWeilRH.Source.C1TboxPullthrough.tbox_of_identities
#print axioms ConnesWeilRH.Source.C1TboxPullthrough.hUneg_q28
#print axioms ConnesWeilRH.Source.C1TboxPullthrough.hUabs_q28
#print axioms ConnesWeilRH.Source.C1TboxPullthrough.hDtwo_q28
#print axioms ConnesWeilRH.Source.C1TboxPullthrough.tbox_q28
#print axioms ConnesWeilRH.Source.C1TboxPullthrough.tbox_true_q28
#print axioms ConnesWeilRH.Source.C1TboxPullthrough.absolute_true_q28
#print axioms ConnesWeilRH.Source.C1TboxPullthrough.hUneg_q38
#print axioms ConnesWeilRH.Source.C1TboxPullthrough.hUabs_q38
#print axioms ConnesWeilRH.Source.C1TboxPullthrough.hDtwo_q38
#print axioms ConnesWeilRH.Source.C1TboxPullthrough.tbox_q38
#print axioms ConnesWeilRH.Source.C1TboxPullthrough.tbox_true_q38
#print axioms ConnesWeilRH.Source.C1TboxPullthrough.absolute_true_q38
#print axioms ConnesWeilRH.Source.C1TboxPullthrough.hUneg_q48
#print axioms ConnesWeilRH.Source.C1TboxPullthrough.hUabs_q48
#print axioms ConnesWeilRH.Source.C1TboxPullthrough.hDtwo_q48
#print axioms ConnesWeilRH.Source.C1TboxPullthrough.tbox_q48
#print axioms ConnesWeilRH.Source.C1TboxPullthrough.tbox_true_q48
#print axioms ConnesWeilRH.Source.C1TboxPullthrough.absolute_true_q48

/-- G3 fidelity (radius form): `tbox_q28` elaborates with the hypotheses
literally `|Gt i j - Q28.G i j| <= radG_q28 i j` and
`|Mt i j - Q28.M i j| <= radM_q28 i j`. -/
example (Gt Mt : Matrix (Fin 8) (Fin 8) ℝ)
    (hG : ∀ i j, |Gt i j - ConnesWeilRH.Source.C1WindowRationalIngest.Q28.G i j|
      ≤ ConnesWeilRH.Source.C1HboxRationalData.radG_q28 i j)
    (hM : ∀ i j, |Mt i j - ConnesWeilRH.Source.C1WindowRationalIngest.Q28.M i j|
      ≤ ConnesWeilRH.Source.C1HboxRationalData.radM_q28 i j)
    (c : Fin 8 → ℝ) (hc : ConnesWeilRH.Source.C1WindowRationalIngest.Q28.R.mulVec c = 0) :
    c ⬝ᵥ (Mt *ᵥ c) ≤ ConnesWeilRH.Source.C1WindowRationalIngest.Q28.U
      * c ⬝ᵥ (Gt *ᵥ c) :=
  ConnesWeilRH.Source.C1TboxPullthrough.tbox_q28 Gt Mt hG hM c hc

/-- G3 fidelity (absolute form over true data): the LHS is literally the
record-1117 `ICgate` on the convolution square and the RHS the named
margin `-mu_q28`; the only analytic hypothesis is `Hbox`. -/
example {w : ConnesWeilRH.Source.CCM25Concrete.CompactLogConvolution.CompactLogTest}
    {G_true M_true : Matrix (Fin 8) (Fin 8) ℝ} {c : Fin 8 → ℝ}
    (hrep : ConnesWeilRH.Source.C1LocalConfigurationDomination.ICgate
        w.convolutionSquare = c ⬝ᵥ (M_true *ᵥ c))
    (hker : ConnesWeilRH.Source.C1WindowRationalIngest.Q28.R.mulVec c = 0)
    (hnorm : c ⬝ᵥ (G_true *ᵥ c) = 1)
    (hbox : ConnesWeilRH.Source.C1HboxRationalData.Hbox
      ConnesWeilRH.Source.C1HboxRationalData.GLo_q28
      ConnesWeilRH.Source.C1HboxRationalData.GHi_q28
      ConnesWeilRH.Source.C1HboxRationalData.MLo_q28
      ConnesWeilRH.Source.C1HboxRationalData.MHi_q28 G_true M_true) :
    ConnesWeilRH.Source.C1LocalConfigurationDomination.ICgate w.convolutionSquare
      ≤ -ConnesWeilRH.Source.C1GateLevelTransferClasses.mu_q28 :=
  ConnesWeilRH.Source.C1TboxPullthrough.absolute_true_q28 hrep hker hnorm hbox
