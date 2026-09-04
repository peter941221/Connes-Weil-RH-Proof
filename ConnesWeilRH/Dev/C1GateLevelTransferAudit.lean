/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1GateLevelTransfer
import ConnesWeilRH.Dev.C1GateLevelTransferClasses

/-!
# Audit for record 1118 (T1 class==>matrix transfer)

Closes registered owed item (i): the focused axiom sweep over the five
kernel declarations of `C1GateLevelTransfer` plus the record's new headlines
(per-class falsifier checks `hslack_*`, box instantiations `whitenedBox_*`,
named margins `mu_*_pos`, and the s2 ratio/absolute headlines).
Acceptance (1118 pre-registration section 3, G2) is exactly the three
standard axioms on each, with zero `sorryAx` lines in the build log.

The s2 fidelity shapes (section 3, G3) are re-printed as the two `example`
blocks at the end over binder names `G_true` / `M_true`: LHS literally
`ICgate ((w).convolutionSquare)`, RHS `U * c ⬝ᵥ (G_true *ᵥ c)` (ratio) resp.
`-mu` (absolute).
-/

#print axioms ConnesWeilRH.Source.C1GateLevelTransfer.two_abs_mul_le_sq_add_sq
#print axioms ConnesWeilRH.Source.C1GateLevelTransfer.qformDoubleSum
#print axioms ConnesWeilRH.Source.C1GateLevelTransfer.sumUnivSplit
#print axioms ConnesWeilRH.Source.C1GateLevelTransfer.lbCollect
#print axioms ConnesWeilRH.Source.C1GateLevelTransfer.qform_nonneg_whitenedBox

#print axioms ConnesWeilRH.Source.C1GateLevelTransferClasses.hslack_q28
#print axioms ConnesWeilRH.Source.C1GateLevelTransferClasses.hslack_q38
#print axioms ConnesWeilRH.Source.C1GateLevelTransferClasses.hslack_q48
#print axioms ConnesWeilRH.Source.C1GateLevelTransferClasses.whitenedBox_q28
#print axioms ConnesWeilRH.Source.C1GateLevelTransferClasses.whitenedBox_q38
#print axioms ConnesWeilRH.Source.C1GateLevelTransferClasses.whitenedBox_q48
#print axioms ConnesWeilRH.Source.C1GateLevelTransferClasses.mu_q28_pos
#print axioms ConnesWeilRH.Source.C1GateLevelTransferClasses.mu_q38_pos
#print axioms ConnesWeilRH.Source.C1GateLevelTransferClasses.mu_q48_pos
#print axioms ConnesWeilRH.Source.C1GateLevelTransferClasses.ratio_q28
#print axioms ConnesWeilRH.Source.C1GateLevelTransferClasses.ratio_q38
#print axioms ConnesWeilRH.Source.C1GateLevelTransferClasses.ratio_q48
#print axioms ConnesWeilRH.Source.C1GateLevelTransferClasses.absolute_q28
#print axioms ConnesWeilRH.Source.C1GateLevelTransferClasses.absolute_q38
#print axioms ConnesWeilRH.Source.C1GateLevelTransferClasses.absolute_q48
#print axioms ConnesWeilRH.Source.C1GateLevelTransferClasses.ratio_headline
#print axioms ConnesWeilRH.Source.C1GateLevelTransferClasses.absolute_headline

/-- G3 ratio-form fidelity shape: the headline elaborates with the record-1117
`ICgate` literally on the LHS and `U * c ⬝ᵥ (G_true *ᵥ c)` on the RHS. -/
example {n : ℕ} {U : ℝ} {G_true M_true : Matrix (Fin n) (Fin n) ℝ}
    {w : ConnesWeilRH.Source.CCM25Concrete.CompactLogConvolution.CompactLogTest}
    {c : Fin n → ℝ}
    (hrep : ConnesWeilRH.Source.C1LocalConfigurationDomination.ICgate
        w.convolutionSquare = c ⬝ᵥ (M_true *ᵥ c))
    (hcert : c ⬝ᵥ (M_true *ᵥ c) ≤ U * c ⬝ᵥ (G_true *ᵥ c)) :
    ConnesWeilRH.Source.C1LocalConfigurationDomination.ICgate w.convolutionSquare
        ≤ U * c ⬝ᵥ (G_true *ᵥ c) :=
  ConnesWeilRH.Source.C1GateLevelTransferClasses.ratio_headline hrep hcert

/-- G3 absolute-form fidelity shape: with the L2-normalization slot the bound
pins at the named margin `-mu`. -/
example {n : ℕ} {U : ℝ} {G_true M_true : Matrix (Fin n) (Fin n) ℝ}
    {w : ConnesWeilRH.Source.CCM25Concrete.CompactLogConvolution.CompactLogTest}
    {c : Fin n → ℝ}
    (hrep : ConnesWeilRH.Source.C1LocalConfigurationDomination.ICgate
        w.convolutionSquare = c ⬝ᵥ (M_true *ᵥ c))
    (hcert : c ⬝ᵥ (M_true *ᵥ c) ≤ U * c ⬝ᵥ (G_true *ᵥ c))
    (hnorm : c ⬝ᵥ (G_true *ᵥ c) = 1) :
    ConnesWeilRH.Source.C1LocalConfigurationDomination.ICgate w.convolutionSquare
        ≤ U :=
  ConnesWeilRH.Source.C1GateLevelTransferClasses.absolute_headline hrep hcert hnorm
