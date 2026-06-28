/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Source.CCM25Concrete.PrimePowerTerm

/-!
# CCM25 fixed-lambda finite-prime certificate

This module combines two separate finite-prime obligations:

* source prime-power support at one fixed `lambda`;
* pointwise finite-prime atom normalization.

The result is still fixed-`lambda`. It does not prove the broader
`forall lambda` source interface.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace FinitePrimeCertificate

structure FixedLambdaFinitePrimeCertificate
    (W : WeilFormSymbols) (f g : TestFunction) (lambda : ℝ) where
  support :
    PrimePowerSupport.SourcePrimePowerSupportSkeletonAtLambda W f g lambda
  terms : PrimePowerTerm.SourcePrimePowerTermNormalization W f g

structure FixedLambdaFinitePrimeAtomCertificate
    (W : WeilFormSymbols) (f g : TestFunction) (lambda : ℝ) where
  support :
    PrimePowerSupport.SourcePrimePowerSupportSkeletonAtLambda W f g lambda
  atoms : PrimePowerTerm.SourceFinitePrimeAtomNormalization W f g

structure FixedLambdaFinitePrimeArithmeticCertificate
    (W : WeilFormSymbols) (f g : TestFunction) (lambda : ℝ) where
  support :
    PrimePowerSupport.SourcePrimePowerArithmeticSupportSkeletonAtLambda
      W f g lambda
  atoms :
    PrimePowerArithmetic.SourceFinitePrimeArithmeticNormalization W f g
  atomsUseSupportSourceTest :
    PrimePowerArithmetic.UsesSourceTest atoms support.sourceTest

def certificate_of_atom_certificate
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeAtomCertificate W f g lambda) :
    FixedLambdaFinitePrimeCertificate W f g lambda where
  support := h.support
  terms := PrimePowerTerm.source_terms_of_atom_normalization h.atoms

noncomputable def atom_certificate_of_arithmetic_certificate
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeArithmeticCertificate W f g lambda) :
    FixedLambdaFinitePrimeAtomCertificate W f g lambda where
  support :=
    PrimePowerSupport.support_skeleton_of_arithmetic_support_skeleton
      h.support
  atoms := PrimePowerTerm.source_atoms_of_arithmetic_normalization h.atoms

noncomputable def certificate_of_arithmetic_certificate
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeArithmeticCertificate W f g lambda) :
    FixedLambdaFinitePrimeCertificate W f g lambda :=
  certificate_of_atom_certificate
    (atom_certificate_of_arithmetic_certificate h)

theorem support_prime_power_index_iff_of_arithmetic_certificate
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeArithmeticCertificate W f g lambda) :
    ∀ n : ℕ,
      (PrimePowerSupport.support_skeleton_of_arithmetic_support_skeleton
        h.support).sourcePrimePowerIndex n ↔
        PrimePowerArithmetic.SourcePrimePowerIndex n :=
  fun _ => Iff.rfl

theorem atom_term_normalization_of_certificate
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeAtomCertificate W f g lambda) :
    WeilFormSymbols.FinitePrimeTermNormalizationStatement W f g :=
  PrimePowerTerm.finite_prime_term_normalization_of_source_atoms h.atoms

theorem arithmetic_term_normalization_of_certificate
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeArithmeticCertificate W f g lambda) :
    WeilFormSymbols.FinitePrimeTermNormalizationStatement W f g :=
  PrimePowerTerm.finite_prime_term_normalization_of_source_arithmetic
    h.atoms

theorem arithmetic_atoms_use_support_source_test
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeArithmeticCertificate W f g lambda) :
    PrimePowerArithmetic.UsesSourceTest h.atoms h.support.sourceTest :=
  h.atomsUseSupportSourceTest

theorem arithmetic_atom_source_test_of_certificate
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeArithmeticCertificate W f g lambda)
    (n : ℕ) :
    (h.atoms.atIndex n).sourceTest = h.support.sourceTest :=
  h.atomsUseSupportSourceTest n

theorem arithmetic_atom_pairing_evaluation_source_test_of_certificate
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeArithmeticCertificate W f g lambda)
    (n : ℕ) :
    (h.atoms.atIndex n).sourcePairing.model.sourceEvaluation.sourceTest =
      h.support.sourceTest :=
  PrimePowerArithmetic.source_pairing_evaluation_uses_normalization_source_test
    h.atomsUseSupportSourceTest n

theorem arithmetic_global_index_source_data_of_certificate
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeArithmeticCertificate W f g lambda)
    {n : ℕ} (hn : n ∈ W.globalPrimeIndexSet) :
    PrimePowerArithmetic.SourcePrimePowerIndex n ∧
      h.support.sourceTest.sourceAtomVisible n :=
  (h.support.globalExact n).1 hn

theorem arithmetic_global_index_prime_power_of_certificate
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeArithmeticCertificate W f g lambda)
    {n : ℕ} (hn : n ∈ W.globalPrimeIndexSet) :
    PrimePowerArithmetic.SourcePrimePowerIndex n :=
  (arithmetic_global_index_source_data_of_certificate h hn).1

theorem arithmetic_global_index_visible_of_certificate
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeArithmeticCertificate W f g lambda)
    {n : ℕ} (hn : n ∈ W.globalPrimeIndexSet) :
    h.support.sourceTest.sourceAtomVisible n :=
  (arithmetic_global_index_source_data_of_certificate h hn).2

theorem arithmetic_global_index_one_lt_of_certificate
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeArithmeticCertificate W f g lambda)
    {n : ℕ} (hn : n ∈ W.globalPrimeIndexSet) :
    1 < n :=
  PrimePowerArithmetic.source_prime_power_index_one_lt
    (arithmetic_global_index_prime_power_of_certificate h hn)

theorem arithmetic_restricted_index_source_data_of_certificate
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeArithmeticCertificate W f g lambda)
    {n : ℕ} (hn : n ∈ W.restrictedPrimeIndexSet lambda) :
    PrimePowerArithmetic.SourcePrimePowerIndex n ∧
      h.support.sourceTest.sourceAtomVisible n ∧
        PrimePowerSupport.SourceLambdaCut lambda n :=
  (h.support.restrictedExact n).1 hn

theorem arithmetic_restricted_index_lambda_cut_of_certificate
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeArithmeticCertificate W f g lambda)
    {n : ℕ} (hn : n ∈ W.restrictedPrimeIndexSet lambda) :
    PrimePowerSupport.SourceLambdaCut lambda n :=
  (arithmetic_restricted_index_source_data_of_certificate h hn).2.2

theorem arithmetic_restricted_index_prime_power_of_certificate
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeArithmeticCertificate W f g lambda)
    {n : ℕ} (hn : n ∈ W.restrictedPrimeIndexSet lambda) :
    PrimePowerArithmetic.SourcePrimePowerIndex n :=
  (arithmetic_restricted_index_source_data_of_certificate h hn).1

theorem arithmetic_restricted_index_visible_of_certificate
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeArithmeticCertificate W f g lambda)
    {n : ℕ} (hn : n ∈ W.restrictedPrimeIndexSet lambda) :
    h.support.sourceTest.sourceAtomVisible n :=
  (arithmetic_restricted_index_source_data_of_certificate h hn).2.1

theorem arithmetic_restricted_index_one_lt_of_certificate
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeArithmeticCertificate W f g lambda)
    {n : ℕ} (hn : n ∈ W.restrictedPrimeIndexSet lambda) :
    1 < n :=
  PrimePowerSupport.source_lambda_cut_one_lt
    (arithmetic_restricted_index_lambda_cut_of_certificate h hn)

theorem arithmetic_restricted_index_le_lambda_sq_of_certificate
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeArithmeticCertificate W f g lambda)
    {n : ℕ} (hn : n ∈ W.restrictedPrimeIndexSet lambda) :
    (n : ℝ) ≤ lambda ^ 2 :=
  PrimePowerSupport.source_lambda_cut_le_lambda_sq
    (arithmetic_restricted_index_lambda_cut_of_certificate h hn)

theorem arithmetic_atom_formula_of_certificate
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeArithmeticCertificate W f g lambda)
    (n : ℕ) :
    W.finitePrimeTerm n (W.convolutionStar f g) =
      PrimePowerArithmetic.SourceFinitePrimeEvaluatorAtom W f g n
        (h.atoms.atIndex n) :=
  PrimePowerTerm.finite_prime_term_formula_of_source_arithmetic_data
    (h.atoms.atIndex n)

theorem arithmetic_atom_formula_of_global_index_certificate
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeArithmeticCertificate W f g lambda)
    {n : ℕ} (_hn : n ∈ W.globalPrimeIndexSet) :
    W.finitePrimeTerm n (W.convolutionStar f g) =
      PrimePowerArithmetic.SourceFinitePrimeEvaluatorAtom W f g n
        (h.atoms.atIndex n) :=
  arithmetic_atom_formula_of_certificate h n

theorem arithmetic_atom_formula_of_restricted_index_certificate
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeArithmeticCertificate W f g lambda)
    {n : ℕ} (_hn : n ∈ W.restrictedPrimeIndexSet lambda) :
    W.finitePrimeTerm n (W.convolutionStar f g) =
      PrimePowerArithmetic.SourceFinitePrimeEvaluatorAtom W f g n
        (h.atoms.atIndex n) :=
  arithmetic_atom_formula_of_certificate h n

theorem arithmetic_finite_prime_sum_formula_of_certificate
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeArithmeticCertificate W f g lambda)
    (indexSet : Finset ℕ) :
    (∑ n ∈ indexSet, W.finitePrimeTerm n (W.convolutionStar f g)) =
      PrimePowerArithmetic.SourceFinitePrimeEvaluatorSum
        W f g indexSet h.atoms := by
  dsimp [PrimePowerArithmetic.SourceFinitePrimeEvaluatorSum]
  exact Finset.sum_congr rfl (by
    intro n hn
    exact arithmetic_atom_formula_of_certificate h n)

theorem arithmetic_global_sum_formula_of_certificate
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeArithmeticCertificate W f g lambda) :
    (∑ n ∈ W.globalPrimeIndexSet,
      W.finitePrimeTerm n (W.convolutionStar f g)) =
      PrimePowerArithmetic.SourceGlobalFinitePrimeEvaluatorSum
        W f g h.atoms := by
  dsimp [PrimePowerArithmetic.SourceGlobalFinitePrimeEvaluatorSum]
  exact arithmetic_finite_prime_sum_formula_of_certificate
    h W.globalPrimeIndexSet

theorem arithmetic_restricted_sum_formula_of_certificate
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeArithmeticCertificate W f g lambda) :
    (∑ n ∈ W.restrictedPrimeIndexSet lambda,
      W.finitePrimeTerm n (W.convolutionStar f g)) =
      PrimePowerArithmetic.SourceRestrictedFinitePrimeEvaluatorSum
        W f g lambda h.atoms := by
  dsimp [PrimePowerArithmetic.SourceRestrictedFinitePrimeEvaluatorSum]
  exact arithmetic_finite_prime_sum_formula_of_certificate
    h (W.restrictedPrimeIndexSet lambda)

def source_prime_power_support_of_certificate
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeCertificate W f g lambda) :
    PrimePowerSupport.SourcePrimePowerSupportAtLambda W f g lambda :=
  PrimePowerSupport.source_prime_power_support_of_skeleton h.support
    (PrimePowerTerm.finite_prime_term_normalization_of_source_terms h.terms)

def exact_support_of_certificate
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeCertificate W f g lambda) :
    FinitePrimeExact.ExactSupportAtLambda W f g lambda :=
  PrimePowerSupport.exact_support_of_source_prime_power_support
    (source_prime_power_support_of_certificate h)

def source_prime_power_support_of_atom_certificate
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeAtomCertificate W f g lambda) :
    PrimePowerSupport.SourcePrimePowerSupportAtLambda W f g lambda :=
  source_prime_power_support_of_certificate
    (certificate_of_atom_certificate h)

noncomputable def source_prime_power_support_of_arithmetic_certificate
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeArithmeticCertificate W f g lambda) :
    PrimePowerSupport.SourcePrimePowerSupportAtLambda W f g lambda :=
  source_prime_power_support_of_certificate
    (certificate_of_arithmetic_certificate h)

def exact_support_of_atom_certificate
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeAtomCertificate W f g lambda) :
    FinitePrimeExact.ExactSupportAtLambda W f g lambda :=
  exact_support_of_certificate (certificate_of_atom_certificate h)

noncomputable def exact_support_of_arithmetic_certificate
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeArithmeticCertificate W f g lambda) :
    FinitePrimeExact.ExactSupportAtLambda W f g lambda :=
  exact_support_of_certificate (certificate_of_arithmetic_certificate h)

theorem one_lt_lambda_of_certificate
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeCertificate W f g lambda) :
    1 < lambda :=
  h.support.oneLtLambda

theorem visible_iff_of_certificate
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeCertificate W f g lambda) :
    ∀ n : ℕ,
      W.finitePrimeAtomVisible n (W.convolutionStar f g) ↔
        h.support.sourcePrimePowerIndex n ∧
          h.support.sourceAtomVisible n (W.convolutionStar f g) :=
  h.support.visibleIff

theorem global_exact_of_certificate
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeCertificate W f g lambda) :
    ∀ n : ℕ,
      n ∈ W.globalPrimeIndexSet ↔
        h.support.sourcePrimePowerIndex n ∧
          h.support.sourceAtomVisible n (W.convolutionStar f g) :=
  h.support.globalExact

theorem restricted_exact_of_certificate
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeCertificate W f g lambda) :
    ∀ n : ℕ,
      n ∈ W.restrictedPrimeIndexSet lambda ↔
        h.support.sourcePrimePowerIndex n ∧
          h.support.sourceAtomVisible n (W.convolutionStar f g) ∧
            PrimePowerSupport.SourceLambdaCut lambda n :=
  h.support.restrictedExact

theorem visible_atoms_in_lambda_cut_of_certificate
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeCertificate W f g lambda) :
    ∀ n : ℕ,
      W.finitePrimeAtomVisible n (W.convolutionStar f g) →
        PrimePowerSupport.SourceLambdaCut lambda n :=
  h.support.visibleAtomsInLambdaCut

theorem term_normalization_of_certificate
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeCertificate W f g lambda) :
    WeilFormSymbols.FinitePrimeTermNormalizationStatement W f g :=
  PrimePowerTerm.finite_prime_term_normalization_of_source_terms h.terms

theorem visibility_at_lambda_of_certificate
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeCertificate W f g lambda) :
    FinitePrimeExact.FinitePrimeVisibilityAtLambdaStatement W f g lambda :=
  FinitePrimeExact.visibility_at_lambda_of_exact_support
    (exact_support_of_certificate h)

end FinitePrimeCertificate
end CCM25Concrete
end Source
end ConnesWeilRH
