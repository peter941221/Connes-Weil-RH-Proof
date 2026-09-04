/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1HkerSpan

open Matrix

/-!
# Audit for record 1120 (Hker via C1 span-level annihilation)

Focused axiom sweep (pre-registration section 2, G2) over every public
declaration of the new module, with zero `sorry` allowed; the allowed
axiom set is exactly {propext, Classical.choice, Quot.sound}.

The G3 fidelity shapes (section 2) are re-printed at the end as `example`
blocks: `tbox_spanK_q28` elaborates with the radius hypotheses and
conclusion literally as in 1119's audit, and `absolute_spanK_q28` with
LHS literally `ICgate ((w).convolutionSquare)` and RHS `-mu_q28`.
-/

#print axioms ConnesWeilRH.Source.C1HkerSpan.hkerC1_of_RK0
#print axioms ConnesWeilRH.Source.C1HkerSpan.RK0_q28
#print axioms ConnesWeilRH.Source.C1HkerSpan.RK0_q38
#print axioms ConnesWeilRH.Source.C1HkerSpan.RK0_q48
#print axioms ConnesWeilRH.Source.C1HkerSpan.hkerC1_q28
#print axioms ConnesWeilRH.Source.C1HkerSpan.hkerC1_q38
#print axioms ConnesWeilRH.Source.C1HkerSpan.hkerC1_q48
#print axioms ConnesWeilRH.Source.C1HkerSpan.tbox_spanK_q28
#print axioms ConnesWeilRH.Source.C1HkerSpan.tbox_spanK_q38
#print axioms ConnesWeilRH.Source.C1HkerSpan.tbox_spanK_q48
#print axioms ConnesWeilRH.Source.C1HkerSpan.absolute_spanK_q28
#print axioms ConnesWeilRH.Source.C1HkerSpan.absolute_spanK_q38
#print axioms ConnesWeilRH.Source.C1HkerSpan.absolute_spanK_q48

/-- G3 fidelity (span T-box): `tbox_spanK_q28` elaborates with the radius
hypotheses literally `|Gt i j - Q28.G i j| <= radG_q28 i j` and the
conclusion on the coefficient vector `Q28.K.mulVec y`. -/
example (Gt Mt : Matrix (Fin 8) (Fin 8) ℝ)
    (hG : ∀ i j, |Gt i j - ConnesWeilRH.Source.C1WindowRationalIngest.Q28.G i j|
      ≤ ConnesWeilRH.Source.C1HboxRationalData.radG_q28 i j)
    (hM : ∀ i j, |Mt i j - ConnesWeilRH.Source.C1WindowRationalIngest.Q28.M i j|
      ≤ ConnesWeilRH.Source.C1HboxRationalData.radM_q28 i j)
    (y : Fin 5 → ℝ) :
    ConnesWeilRH.Source.C1WindowRationalIngest.Q28.K.mulVec y ⬝ᵥ
        (Mt *ᵥ (ConnesWeilRH.Source.C1WindowRationalIngest.Q28.K.mulVec y))
      ≤ ConnesWeilRH.Source.C1WindowRationalIngest.Q28.U *
        (ConnesWeilRH.Source.C1WindowRationalIngest.Q28.K.mulVec y ⬝ᵥ
          (Gt *ᵥ (ConnesWeilRH.Source.C1WindowRationalIngest.Q28.K.mulVec y))) :=
  ConnesWeilRH.Source.C1HkerSpan.tbox_spanK_q28 Gt Mt hG hM y

/-- G3 fidelity (span absolute form): the LHS is literally the
record-1117 `ICgate` on the convolution square and the RHS the named
margin `-mu_q28`; the only analytic hypothesis is `Hbox`, and the hker
slot is closed by the C1 span identity. -/
example {w : ConnesWeilRH.Source.CCM25Concrete.CompactLogConvolution.CompactLogTest}
    {G_true M_true : Matrix (Fin 8) (Fin 8) ℝ} {y : Fin 5 → ℝ}
    (hrep : ConnesWeilRH.Source.C1LocalConfigurationDomination.ICgate
        w.convolutionSquare
      = ConnesWeilRH.Source.C1WindowRationalIngest.Q28.K.mulVec y ⬝ᵥ
        (M_true *ᵥ (ConnesWeilRH.Source.C1WindowRationalIngest.Q28.K.mulVec y)))
    (hnorm : ConnesWeilRH.Source.C1WindowRationalIngest.Q28.K.mulVec y ⬝ᵥ
        (G_true *ᵥ (ConnesWeilRH.Source.C1WindowRationalIngest.Q28.K.mulVec y)) = 1)
    (hbox : ConnesWeilRH.Source.C1HboxRationalData.Hbox
      ConnesWeilRH.Source.C1HboxRationalData.GLo_q28
      ConnesWeilRH.Source.C1HboxRationalData.GHi_q28
      ConnesWeilRH.Source.C1HboxRationalData.MLo_q28
      ConnesWeilRH.Source.C1HboxRationalData.MHi_q28 G_true M_true) :
    ConnesWeilRH.Source.C1LocalConfigurationDomination.ICgate w.convolutionSquare
      ≤ -ConnesWeilRH.Source.C1GateLevelTransferClasses.mu_q28 :=
  ConnesWeilRH.Source.C1HkerSpan.absolute_spanK_q28 hrep hnorm hbox
