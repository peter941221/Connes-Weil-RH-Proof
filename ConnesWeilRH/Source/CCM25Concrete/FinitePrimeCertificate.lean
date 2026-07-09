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
  atomsWithSourceTest :
    PrimePowerArithmetic.SourceFinitePrimeArithmeticNormalizationForSourceTest
      W f g support.sourceTest

def FixedLambdaFinitePrimeArithmeticCertificate.atoms
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeArithmeticCertificate W f g lambda) :
    PrimePowerArithmetic.SourceFinitePrimeArithmeticNormalization W f g :=
  h.atomsWithSourceTest.toNormalization

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
  PrimePowerArithmetic.SourceFinitePrimeArithmeticNormalizationForSourceTest.toNormalization_uses_sourceTest
    h.atomsWithSourceTest

theorem arithmetic_atom_source_test_of_certificate
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeArithmeticCertificate W f g lambda)
    (n : ℕ) :
    (h.atoms.atIndex n).sourceTest = h.support.sourceTest :=
  arithmetic_atoms_use_support_source_test h n

theorem arithmetic_atom_pairing_evaluation_source_test_of_certificate
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeArithmeticCertificate W f g lambda)
    (n : ℕ) :
    (h.atoms.atIndex n).sourcePairing.model.sourceEvaluation.sourceTest =
      h.support.sourceTest :=
  PrimePowerArithmetic.source_pairing_evaluation_uses_normalization_source_test
    (arithmetic_atoms_use_support_source_test h) n

theorem arithmetic_atom_visible_in_support_source_test_of_certificate
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeArithmeticCertificate W f g lambda)
    (n : ℕ) :
    h.support.sourceTest.sourceAtomVisible n :=
  PrimePowerArithmetic.source_atom_visible_uses_normalization_source_test
    (arithmetic_atoms_use_support_source_test h) n

theorem arithmetic_atom_visible_in_pairing_source_test_of_certificate
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeArithmeticCertificate W f g lambda)
    (n : ℕ) :
    (h.atoms.atIndex n).sourcePairing.model.sourceEvaluation.sourceTest.sourceAtomVisible n :=
  PrimePowerArithmetic.source_atom_visible_in_pairing_source_test
    (h.atoms.atIndex n)

theorem arithmetic_global_index_source_data_of_certificate
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeArithmeticCertificate W f g lambda)
    {n : ℕ} (hn : n ∈ W.globalPrimeIndexSet) :
    PrimePowerSupport.SourceGlobalIndexData W f g n := by
  exact h.support.globalIndexData n hn

theorem arithmetic_global_index_visible_atom_data_of_certificate
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeArithmeticCertificate W f g lambda)
    {n : ℕ} (hn : n ∈ W.globalPrimeIndexSet) :
    PrimePowerSupport.SourceVisibleAtomData W f g n :=
  PrimePowerSupport.source_global_index_to_visible_atom_data
    (arithmetic_global_index_source_data_of_certificate h hn)

theorem arithmetic_global_index_prime_power_of_certificate
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeArithmeticCertificate W f g lambda)
    {n : ℕ} (hn : n ∈ W.globalPrimeIndexSet) :
    IsPrimePow n :=
  PrimePowerSupport.source_global_index_prime_power_index
    (arithmetic_global_index_source_data_of_certificate h hn)

theorem arithmetic_global_index_isPrimePow_of_certificate
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeArithmeticCertificate W f g lambda)
    {n : ℕ} (hn : n ∈ W.globalPrimeIndexSet) :
    IsPrimePow n :=
  arithmetic_global_index_prime_power_of_certificate h hn

theorem arithmetic_global_index_visible_of_certificate
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeArithmeticCertificate W f g lambda)
    {n : ℕ} (hn : n ∈ W.globalPrimeIndexSet) :
    h.support.sourceTest.sourceAtomVisible n :=
  (PrimePowerTest.route_visibility_iff_source_visibility
    h.support.sourceTest n).1
    (PrimePowerSupport.source_global_index_visible
      (arithmetic_global_index_source_data_of_certificate h hn))

theorem arithmetic_global_index_one_lt_of_certificate
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeArithmeticCertificate W f g lambda)
    {n : ℕ} (hn : n ∈ W.globalPrimeIndexSet) :
    1 < n :=
  IsPrimePow.one_lt
    (arithmetic_global_index_prime_power_of_certificate h hn)

theorem arithmetic_restricted_index_source_data_of_certificate
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeArithmeticCertificate W f g lambda)
    {n : ℕ} (hn : n ∈ W.restrictedPrimeIndexSet lambda) :
    PrimePowerSupport.SourceRestrictedIndexData W f g lambda n := by
  exact h.support.restrictedIndexData n hn

theorem arithmetic_restricted_index_global_source_data_of_certificate
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeArithmeticCertificate W f g lambda)
    {n : ℕ} (hn : n ∈ W.restrictedPrimeIndexSet lambda) :
    PrimePowerSupport.SourceGlobalIndexData W f g n :=
  PrimePowerSupport.source_restricted_index_to_global_index_data
    (arithmetic_restricted_index_source_data_of_certificate h hn)

theorem arithmetic_restricted_index_visible_atom_data_of_certificate
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeArithmeticCertificate W f g lambda)
    {n : ℕ} (hn : n ∈ W.restrictedPrimeIndexSet lambda) :
    PrimePowerSupport.SourceVisibleAtomData W f g n :=
  PrimePowerSupport.source_restricted_index_to_visible_atom_data
    (arithmetic_restricted_index_source_data_of_certificate h hn)

theorem arithmetic_restricted_index_lambda_cut_of_certificate
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeArithmeticCertificate W f g lambda)
    {n : ℕ} (hn : n ∈ W.restrictedPrimeIndexSet lambda) :
    1 < n ∧ (n : ℝ) ≤ lambda ^ 2 :=
  PrimePowerSupport.source_restricted_index_lambda_cut
    (arithmetic_restricted_index_source_data_of_certificate h hn)

theorem arithmetic_restricted_index_prime_power_of_certificate
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeArithmeticCertificate W f g lambda)
    {n : ℕ} (hn : n ∈ W.restrictedPrimeIndexSet lambda) :
    IsPrimePow n :=
  PrimePowerSupport.source_restricted_index_prime_power_index
    (arithmetic_restricted_index_source_data_of_certificate h hn)

theorem arithmetic_restricted_index_isPrimePow_of_certificate
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeArithmeticCertificate W f g lambda)
    {n : ℕ} (hn : n ∈ W.restrictedPrimeIndexSet lambda) :
    IsPrimePow n :=
  arithmetic_restricted_index_prime_power_of_certificate h hn

theorem arithmetic_restricted_index_visible_of_certificate
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeArithmeticCertificate W f g lambda)
    {n : ℕ} (hn : n ∈ W.restrictedPrimeIndexSet lambda) :
    h.support.sourceTest.sourceAtomVisible n :=
  (PrimePowerTest.route_visibility_iff_source_visibility
    h.support.sourceTest n).1
    (PrimePowerSupport.source_restricted_index_visible
      (arithmetic_restricted_index_source_data_of_certificate h hn))

theorem arithmetic_restricted_index_one_lt_of_certificate
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeArithmeticCertificate W f g lambda)
    {n : ℕ} (hn : n ∈ W.restrictedPrimeIndexSet lambda) :
    1 < n :=
  PrimePowerSupport.source_restricted_index_one_lt
    (arithmetic_restricted_index_source_data_of_certificate h hn)

theorem arithmetic_restricted_index_le_lambda_sq_of_certificate
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeArithmeticCertificate W f g lambda)
    {n : ℕ} (hn : n ∈ W.restrictedPrimeIndexSet lambda) :
    (n : ℝ) ≤ lambda ^ 2 :=
  PrimePowerSupport.source_restricted_index_le_lambda_sq
    (arithmetic_restricted_index_source_data_of_certificate h hn)

theorem arithmetic_atom_formula_of_certificate
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeArithmeticCertificate W f g lambda)
    (n : ℕ) :
    W.finitePrimeTerm n (W.convolutionStar f g) =
      PrimePowerArithmetic.SourceFinitePrimeEvaluatorAtom W f g n
        (h.atoms.atIndex n) :=
  PrimePowerTerm.finite_prime_term_formula_of_source_arithmetic_data
    (h.atoms.atIndex n)

def arithmetic_data_on_global_index_set_of_certificate
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeArithmeticCertificate W f g lambda) :
    PrimePowerArithmetic.SourceGlobalFinitePrimeArithmeticData W f g where
  atIndex := fun n _ => h.atoms.atIndex n

def arithmetic_data_on_restricted_index_set_of_certificate
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeArithmeticCertificate W f g lambda) :
    PrimePowerArithmetic.SourceRestrictedFinitePrimeArithmeticData
      W f g lambda where
  atIndex := fun n _ => h.atoms.atIndex n

theorem arithmetic_atom_formula_of_global_index_certificate
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeArithmeticCertificate W f g lambda)
    {n : ℕ} (hn : n ∈ W.globalPrimeIndexSet) :
    W.finitePrimeTerm n (W.convolutionStar f g) =
      PrimePowerArithmetic.SourceFinitePrimeEvaluatorAtom W f g n
        ((arithmetic_data_on_global_index_set_of_certificate h).atIndex n hn) :=
  PrimePowerArithmetic.source_on_index_set_finite_prime_term_formula_source_evaluator
    (arithmetic_data_on_global_index_set_of_certificate h) hn

theorem arithmetic_atom_formula_of_restricted_index_certificate
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeArithmeticCertificate W f g lambda)
    {n : ℕ} (hn : n ∈ W.restrictedPrimeIndexSet lambda) :
    W.finitePrimeTerm n (W.convolutionStar f g) =
      PrimePowerArithmetic.SourceFinitePrimeEvaluatorAtom W f g n
        ((arithmetic_data_on_restricted_index_set_of_certificate h).atIndex n hn) :=
  PrimePowerArithmetic.source_on_index_set_finite_prime_term_formula_source_evaluator
    (arithmetic_data_on_restricted_index_set_of_certificate h) hn

theorem arithmetic_global_scoped_sum_eq_global_sum_of_certificate
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeArithmeticCertificate W f g lambda) :
    PrimePowerArithmetic.SourceGlobalFinitePrimeEvaluatorSumOnIndexSet
        W f g (arithmetic_data_on_global_index_set_of_certificate h) =
      PrimePowerArithmetic.SourceGlobalFinitePrimeEvaluatorSum W f g h.atoms :=
  PrimePowerArithmetic.source_global_finite_prime_evaluator_sum_on_index_set_of_global
    h.atoms

theorem arithmetic_restricted_scoped_sum_eq_restricted_sum_of_certificate
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeArithmeticCertificate W f g lambda) :
    PrimePowerArithmetic.SourceRestrictedFinitePrimeEvaluatorSumOnIndexSet
        W f g lambda
        (arithmetic_data_on_restricted_index_set_of_certificate h) =
      PrimePowerArithmetic.SourceRestrictedFinitePrimeEvaluatorSum
        W f g lambda h.atoms :=
  PrimePowerArithmetic.source_restricted_finite_prime_evaluator_sum_on_index_set_of_global
    h.atoms

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

theorem arithmetic_von_mangoldt_pairing_sum_formula_of_certificate
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeArithmeticCertificate W f g lambda)
    (indexSet : Finset ℕ) :
    (∑ n ∈ indexSet, W.vonMangoldtWeight n * W.primePowerPairing n f g) =
      PrimePowerArithmetic.SourceFinitePrimeEvaluatorSum
        W f g indexSet h.atoms := by
  dsimp [PrimePowerArithmetic.SourceFinitePrimeEvaluatorSum]
  exact Finset.sum_congr rfl (by
    intro n hn
    exact
      PrimePowerArithmetic.source_von_mangoldt_pairing_product_formula_source_evaluator
        (h.atoms.atIndex n))

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

theorem arithmetic_global_von_mangoldt_pairing_sum_formula_of_certificate
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeArithmeticCertificate W f g lambda) :
    (∑ n ∈ W.globalPrimeIndexSet,
      W.vonMangoldtWeight n * W.primePowerPairing n f g) =
      PrimePowerArithmetic.SourceGlobalFinitePrimeEvaluatorSum
        W f g h.atoms := by
  dsimp [PrimePowerArithmetic.SourceGlobalFinitePrimeEvaluatorSum]
  exact arithmetic_von_mangoldt_pairing_sum_formula_of_certificate
    h W.globalPrimeIndexSet

theorem arithmetic_global_mathlib_sum_formula_of_certificate
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeArithmeticCertificate W f g lambda) :
    (∑ n ∈ W.globalPrimeIndexSet,
      W.finitePrimeTerm n (W.convolutionStar f g)) =
      PrimePowerArithmetic.MathlibGlobalFinitePrimeEvaluatorSumOnIndexSet
        W f g (arithmetic_data_on_global_index_set_of_certificate h) := by
  calc
    (∑ n ∈ W.globalPrimeIndexSet,
      W.finitePrimeTerm n (W.convolutionStar f g)) =
        PrimePowerArithmetic.SourceGlobalFinitePrimeEvaluatorSum W f g h.atoms :=
      arithmetic_global_sum_formula_of_certificate h
    _ =
        PrimePowerArithmetic.SourceGlobalFinitePrimeEvaluatorSumOnIndexSet W f g
          (arithmetic_data_on_global_index_set_of_certificate h) :=
      (arithmetic_global_scoped_sum_eq_global_sum_of_certificate h).symm
    _ =
        PrimePowerArithmetic.MathlibGlobalFinitePrimeEvaluatorSumOnIndexSet W f g
          (arithmetic_data_on_global_index_set_of_certificate h) :=
      PrimePowerArithmetic.source_global_finite_prime_evaluator_sum_on_index_set_eq_mathlib
        _

theorem arithmetic_global_mathlib_von_mangoldt_pairing_sum_formula_of_certificate
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeArithmeticCertificate W f g lambda) :
    (∑ n ∈ W.globalPrimeIndexSet,
      W.vonMangoldtWeight n * W.primePowerPairing n f g) =
      PrimePowerArithmetic.MathlibGlobalFinitePrimeEvaluatorSumOnIndexSet
        W f g (arithmetic_data_on_global_index_set_of_certificate h) := by
  calc
    (∑ n ∈ W.globalPrimeIndexSet,
      W.vonMangoldtWeight n * W.primePowerPairing n f g) =
        PrimePowerArithmetic.SourceGlobalFinitePrimeEvaluatorSum W f g h.atoms :=
      arithmetic_global_von_mangoldt_pairing_sum_formula_of_certificate h
    _ =
        PrimePowerArithmetic.SourceGlobalFinitePrimeEvaluatorSumOnIndexSet W f g
          (arithmetic_data_on_global_index_set_of_certificate h) :=
      (arithmetic_global_scoped_sum_eq_global_sum_of_certificate h).symm
    _ =
        PrimePowerArithmetic.MathlibGlobalFinitePrimeEvaluatorSumOnIndexSet W f g
          (arithmetic_data_on_global_index_set_of_certificate h) :=
      PrimePowerArithmetic.source_global_finite_prime_evaluator_sum_on_index_set_eq_mathlib
        _

theorem arithmetic_global_mathlib_sum_formula_data_of_certificate
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeArithmeticCertificate W f g lambda) :
    PrimePowerArithmetic.MathlibGlobalFinitePrimeSumFormulaData
      W f g (arithmetic_data_on_global_index_set_of_certificate h) where
  finitePrimeTermSumReadOff :=
    arithmetic_global_mathlib_sum_formula_of_certificate h
  vonMangoldtPairingSumReadOff :=
    arithmetic_global_mathlib_von_mangoldt_pairing_sum_formula_of_certificate h

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

theorem arithmetic_restricted_von_mangoldt_pairing_sum_formula_of_certificate
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeArithmeticCertificate W f g lambda) :
    (∑ n ∈ W.restrictedPrimeIndexSet lambda,
      W.vonMangoldtWeight n * W.primePowerPairing n f g) =
      PrimePowerArithmetic.SourceRestrictedFinitePrimeEvaluatorSum
        W f g lambda h.atoms := by
  dsimp [PrimePowerArithmetic.SourceRestrictedFinitePrimeEvaluatorSum]
  exact arithmetic_von_mangoldt_pairing_sum_formula_of_certificate
    h (W.restrictedPrimeIndexSet lambda)

theorem arithmetic_restricted_mathlib_sum_formula_of_certificate
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeArithmeticCertificate W f g lambda) :
    (∑ n ∈ W.restrictedPrimeIndexSet lambda,
      W.finitePrimeTerm n (W.convolutionStar f g)) =
      PrimePowerArithmetic.MathlibRestrictedFinitePrimeEvaluatorSumOnIndexSet
        W f g lambda
        (arithmetic_data_on_restricted_index_set_of_certificate h) := by
  calc
    (∑ n ∈ W.restrictedPrimeIndexSet lambda,
      W.finitePrimeTerm n (W.convolutionStar f g)) =
        PrimePowerArithmetic.SourceRestrictedFinitePrimeEvaluatorSum
          W f g lambda h.atoms :=
      arithmetic_restricted_sum_formula_of_certificate h
    _ =
        PrimePowerArithmetic.SourceRestrictedFinitePrimeEvaluatorSumOnIndexSet
          W f g lambda
          (arithmetic_data_on_restricted_index_set_of_certificate h) :=
      (arithmetic_restricted_scoped_sum_eq_restricted_sum_of_certificate h).symm
    _ =
        PrimePowerArithmetic.MathlibRestrictedFinitePrimeEvaluatorSumOnIndexSet
          W f g lambda
          (arithmetic_data_on_restricted_index_set_of_certificate h) :=
      PrimePowerArithmetic.source_restricted_finite_prime_evaluator_sum_on_index_set_eq_mathlib
        _

theorem arithmetic_restricted_mathlib_von_mangoldt_pairing_sum_formula_of_certificate
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeArithmeticCertificate W f g lambda) :
    (∑ n ∈ W.restrictedPrimeIndexSet lambda,
      W.vonMangoldtWeight n * W.primePowerPairing n f g) =
      PrimePowerArithmetic.MathlibRestrictedFinitePrimeEvaluatorSumOnIndexSet
        W f g lambda
        (arithmetic_data_on_restricted_index_set_of_certificate h) := by
  calc
    (∑ n ∈ W.restrictedPrimeIndexSet lambda,
      W.vonMangoldtWeight n * W.primePowerPairing n f g) =
        PrimePowerArithmetic.SourceRestrictedFinitePrimeEvaluatorSum
          W f g lambda h.atoms :=
      arithmetic_restricted_von_mangoldt_pairing_sum_formula_of_certificate h
    _ =
        PrimePowerArithmetic.SourceRestrictedFinitePrimeEvaluatorSumOnIndexSet
          W f g lambda
          (arithmetic_data_on_restricted_index_set_of_certificate h) :=
      (arithmetic_restricted_scoped_sum_eq_restricted_sum_of_certificate h).symm
    _ =
        PrimePowerArithmetic.MathlibRestrictedFinitePrimeEvaluatorSumOnIndexSet
          W f g lambda
          (arithmetic_data_on_restricted_index_set_of_certificate h) :=
      PrimePowerArithmetic.source_restricted_finite_prime_evaluator_sum_on_index_set_eq_mathlib
        _

theorem arithmetic_restricted_mathlib_sum_formula_data_of_certificate
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeArithmeticCertificate W f g lambda) :
    PrimePowerArithmetic.MathlibRestrictedFinitePrimeSumFormulaData
      W f g lambda (arithmetic_data_on_restricted_index_set_of_certificate h) where
  finitePrimeTermSumReadOff :=
    arithmetic_restricted_mathlib_sum_formula_of_certificate h
  vonMangoldtPairingSumReadOff :=
    arithmetic_restricted_mathlib_von_mangoldt_pairing_sum_formula_of_certificate h

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
  PrimePowerSupport.source_prime_power_support_of_skeleton h.support
    (PrimePowerTerm.finite_prime_term_normalization_of_source_atoms h.atoms)

def support_skeleton_of_arithmetic_certificate
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeArithmeticCertificate W f g lambda) :
    PrimePowerSupport.SourcePrimePowerSupportSkeletonAtLambda W f g lambda where
  oneLtLambda := h.support.oneLtLambda
  visibleIff := by
    intro n
    constructor
    · intro hvisible
      exact
        { primePowerIndex := (h.atoms.atIndex n).sourcePrimePowerIndex
          atomVisible := hvisible }
    · intro hdata
      exact hdata.atomVisible
  globalIndexData := h.support.globalIndexData
  routeVisibleGlobalIndex := h.support.routeVisibleGlobalIndex
  restrictedIndexData := h.support.restrictedIndexData
  routeVisibleRestrictedIndex := h.support.routeVisibleRestrictedIndex

noncomputable def source_prime_power_support_of_arithmetic_certificate
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeArithmeticCertificate W f g lambda) :
    PrimePowerSupport.SourcePrimePowerSupportAtLambda W f g lambda :=
  PrimePowerSupport.source_prime_power_support_of_skeleton
    (support_skeleton_of_arithmetic_certificate h)
    (arithmetic_term_normalization_of_certificate h)

def exact_support_of_atom_certificate
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeAtomCertificate W f g lambda) :
    FinitePrimeExact.ExactSupportAtLambda W f g lambda :=
  PrimePowerSupport.exact_support_of_source_prime_power_support
    (source_prime_power_support_of_atom_certificate h)

noncomputable def exact_support_of_arithmetic_certificate
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeArithmeticCertificate W f g lambda) :
    FinitePrimeExact.ExactSupportAtLambda W f g lambda :=
  PrimePowerSupport.exact_support_of_source_prime_power_support
    (source_prime_power_support_of_arithmetic_certificate h)

structure FixedLambdaFinitePrimeConcreteObject
    (W : WeilFormSymbols) (f g : TestFunction) (lambda : ℝ) where
  certificate : FixedLambdaFinitePrimeArithmeticCertificate W f g lambda

noncomputable def concrete_object_of_arithmetic_certificate
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeArithmeticCertificate W f g lambda) :
    FixedLambdaFinitePrimeConcreteObject W f g lambda where
  certificate := h

def FixedLambdaFinitePrimeConcreteObject.sourceTest
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeConcreteObject W f g lambda) :
    PrimePowerTest.SourceTestEvaluationInterface W f g :=
  h.certificate.support.sourceTest

theorem FixedLambdaFinitePrimeConcreteObject.sourceTest_eq_support
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeConcreteObject W f g lambda) :
    h.sourceTest = h.certificate.support.sourceTest :=
  rfl

def FixedLambdaFinitePrimeConcreteObject.atomData
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeConcreteObject W f g lambda)
    (n : ℕ) :
    PrimePowerArithmetic.SourceFinitePrimeArithmeticData W f g n :=
  h.certificate.atoms.atIndex n

def FixedLambdaFinitePrimeConcreteObject.localFormulaData
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeConcreteObject W f g lambda)
    (n : ℕ) :
    PrimePowerArithmetic.SourceFinitePrimeLocalFormulaData W f g n
      (h.atomData n) :=
  PrimePowerArithmetic.source_finite_prime_local_formula_data
    (h.certificate.atoms.atIndex n)

def FixedLambdaFinitePrimeConcreteObject.globalArithmeticData
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeConcreteObject W f g lambda) :
    PrimePowerArithmetic.SourceGlobalFinitePrimeArithmeticData W f g :=
  arithmetic_data_on_global_index_set_of_certificate h.certificate

def FixedLambdaFinitePrimeConcreteObject.restrictedArithmeticData
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeConcreteObject W f g lambda) :
    PrimePowerArithmetic.SourceRestrictedFinitePrimeArithmeticData
      W f g lambda :=
  arithmetic_data_on_restricted_index_set_of_certificate h.certificate

def FixedLambdaFinitePrimeConcreteObject.globalSumFormulaData
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeConcreteObject W f g lambda) :
    PrimePowerArithmetic.MathlibGlobalFinitePrimeSumFormulaData
      W f g (arithmetic_data_on_global_index_set_of_certificate h.certificate) :=
  arithmetic_global_mathlib_sum_formula_data_of_certificate h.certificate

def FixedLambdaFinitePrimeConcreteObject.restrictedSumFormulaData
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeConcreteObject W f g lambda) :
    PrimePowerArithmetic.MathlibRestrictedFinitePrimeSumFormulaData
      W f g lambda
        (arithmetic_data_on_restricted_index_set_of_certificate h.certificate) :=
  arithmetic_restricted_mathlib_sum_formula_data_of_certificate h.certificate

def FixedLambdaFinitePrimeConcreteObject.visibleArithmeticData
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeConcreteObject W f g lambda) :
    PrimePowerArithmetic.SourceVisibleFinitePrimeArithmeticData
      W f g h.sourceTest where
  atVisibleIndex := fun n _ => h.atomData n

noncomputable def FixedLambdaFinitePrimeConcreteObject.exactSupport
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeConcreteObject W f g lambda) :
    FinitePrimeExact.ExactSupportAtLambda W f g lambda :=
  exact_support_of_arithmetic_certificate h.certificate

@[simp] theorem FixedLambdaFinitePrimeConcreteObject.visibleArithmeticData_atVisibleIndex
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeConcreteObject W f g lambda)
    {n : ℕ} (hn : h.sourceTest.sourceAtomVisible n) :
    (h.visibleArithmeticData).atVisibleIndex n hn = h.atomData n :=
  rfl

theorem concrete_object_source_test_eq_support
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeConcreteObject W f g lambda) :
    h.sourceTest = h.certificate.support.sourceTest :=
  h.sourceTest_eq_support

theorem FixedLambdaFinitePrimeConcreteObject.globalIndexData
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeConcreteObject W f g lambda)
    {n : ℕ}
    (hn : n ∈ W.globalPrimeIndexSet) :
    PrimePowerSupport.SourceGlobalIndexData W f g n := by
  let hdata := h.certificate.support.globalIndexData n hn
  exact
    { primePowerIndex := hdata.primePowerIndex
      atomVisible := hdata.atomVisible }

theorem FixedLambdaFinitePrimeConcreteObject.restrictedIndexData
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeConcreteObject W f g lambda)
    {n : ℕ}
    (hn : n ∈ W.restrictedPrimeIndexSet lambda) :
    PrimePowerSupport.SourceRestrictedIndexData W f g lambda n := by
  let hdata := h.certificate.support.restrictedIndexData n hn
  exact
    { primePowerIndex := hdata.primePowerIndex
      atomVisible := hdata.atomVisible
      lambdaCut := hdata.lambdaCut }

theorem concrete_object_global_index_prime_power
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeConcreteObject W f g lambda)
    {n : ℕ} (hn : n ∈ W.globalPrimeIndexSet) :
    IsPrimePow n :=
  (h.globalIndexData hn).primePowerIndex

theorem concrete_object_global_index_isPrimePow
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeConcreteObject W f g lambda)
    {n : ℕ} (hn : n ∈ W.globalPrimeIndexSet) :
    IsPrimePow n :=
  concrete_object_global_index_prime_power h hn

theorem concrete_object_global_index_visible
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeConcreteObject W f g lambda)
    {n : ℕ} (hn : n ∈ W.globalPrimeIndexSet) :
    h.sourceTest.sourceAtomVisible n :=
  (PrimePowerTest.route_visibility_iff_source_visibility
    h.sourceTest n).1
    (h.globalIndexData hn).atomVisible

theorem concrete_object_global_index_weight_read_off
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeConcreteObject W f g lambda)
    {n : ℕ} (hn : n ∈ W.globalPrimeIndexSet) :
    W.vonMangoldtWeight n = ArithmeticFunction.vonMangoldt n :=
  PrimePowerArithmetic.source_on_index_set_weight_read_off
    h.globalArithmeticData hn

theorem concrete_object_global_index_pairing_formula_source_evaluator
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeConcreteObject W f g lambda)
    {n : ℕ} (hn : n ∈ W.globalPrimeIndexSet) :
    let atom := h.globalArithmeticData.atIndex n hn
    W.primePowerPairing n f g =
      (1 / Real.sqrt (n : ℝ)) *
        (atom.sourcePairing.model.sourceEvaluation.sourceEvaluator.valueAt
            (W.convolutionStar f g) (n : ℝ) +
          atom.sourcePairing.model.sourceEvaluation.sourceEvaluator.valueAt
            (W.convolutionStar f g) ((n : ℝ)⁻¹)) :=
  by
    let sourceEvaluation :=
      (h.globalArithmeticData.atIndex n hn).sourcePairing.model.sourceEvaluation
    rw [PrimePowerArithmetic.source_on_index_set_pairing_formula_source_evaluations
        h.globalArithmeticData hn,
      PrimePowerEvaluation.source_forward_value_at_source_points sourceEvaluation,
      PrimePowerEvaluation.source_inverse_value_at_source_points sourceEvaluation]

theorem concrete_object_global_index_pairing_formula_source_evaluations
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeConcreteObject W f g lambda)
    {n : ℕ} (hn : n ∈ W.globalPrimeIndexSet) :
    let atom := h.globalArithmeticData.atIndex n hn
    W.primePowerPairing n f g =
      (1 / Real.sqrt (n : ℝ)) *
        (atom.sourcePairing.model.sourceEvaluation.forwardValue +
          atom.sourcePairing.model.sourceEvaluation.inverseValue) :=
  PrimePowerArithmetic.source_on_index_set_pairing_formula_source_evaluations
    h.globalArithmeticData hn

theorem concrete_object_global_index_term_formula_source_evaluator
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeConcreteObject W f g lambda)
    {n : ℕ} (hn : n ∈ W.globalPrimeIndexSet) :
    W.finitePrimeTerm n (W.convolutionStar f g) =
      PrimePowerArithmetic.SourceFinitePrimeEvaluatorAtom W f g n
        (h.globalArithmeticData.atIndex n hn) :=
  PrimePowerArithmetic.source_on_index_set_finite_prime_term_formula_source_evaluator
    h.globalArithmeticData hn

theorem concrete_object_global_index_term_formula_source_evaluations
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeConcreteObject W f g lambda)
    {n : ℕ} (hn : n ∈ W.globalPrimeIndexSet) :
    let atom := h.globalArithmeticData.atIndex n hn
    W.finitePrimeTerm n (W.convolutionStar f g) =
      ArithmeticFunction.vonMangoldt n *
        ((1 / Real.sqrt (n : ℝ)) *
          (atom.sourcePairing.model.sourceEvaluation.forwardValue +
            atom.sourcePairing.model.sourceEvaluation.inverseValue)) :=
  PrimePowerArithmetic.source_on_index_set_finite_prime_term_formula_mathlib_source_evaluations
    h.globalArithmeticData hn

theorem concrete_object_global_index_von_mangoldt_pairing_formula_source_evaluations
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeConcreteObject W f g lambda)
    {n : ℕ} (hn : n ∈ W.globalPrimeIndexSet) :
    let atom := h.globalArithmeticData.atIndex n hn
    W.vonMangoldtWeight n * W.primePowerPairing n f g =
      ArithmeticFunction.vonMangoldt n *
        ((1 / Real.sqrt (n : ℝ)) *
          (atom.sourcePairing.model.sourceEvaluation.forwardValue +
            atom.sourcePairing.model.sourceEvaluation.inverseValue)) :=
  PrimePowerArithmetic.source_on_index_set_von_mangoldt_pairing_product_formula_source_evaluations
    h.globalArithmeticData hn

theorem concrete_object_restricted_index_prime_power
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeConcreteObject W f g lambda)
    {n : ℕ} (hn : n ∈ W.restrictedPrimeIndexSet lambda) :
    IsPrimePow n :=
  (h.restrictedIndexData hn).primePowerIndex

theorem concrete_object_restricted_index_isPrimePow
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeConcreteObject W f g lambda)
    {n : ℕ} (hn : n ∈ W.restrictedPrimeIndexSet lambda) :
    IsPrimePow n :=
  concrete_object_restricted_index_prime_power h hn

theorem concrete_object_restricted_index_visible
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeConcreteObject W f g lambda)
    {n : ℕ} (hn : n ∈ W.restrictedPrimeIndexSet lambda) :
    h.sourceTest.sourceAtomVisible n :=
  (PrimePowerTest.route_visibility_iff_source_visibility
    h.sourceTest n).1
    (h.restrictedIndexData hn).atomVisible

theorem concrete_object_restricted_index_lambda_cut
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeConcreteObject W f g lambda)
    {n : ℕ} (hn : n ∈ W.restrictedPrimeIndexSet lambda) :
    1 < n ∧ (n : ℝ) ≤ lambda ^ 2 :=
  (h.restrictedIndexData hn).lambdaCut

theorem concrete_object_restricted_index_weight_read_off
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeConcreteObject W f g lambda)
    {n : ℕ} (hn : n ∈ W.restrictedPrimeIndexSet lambda) :
    W.vonMangoldtWeight n = ArithmeticFunction.vonMangoldt n :=
  PrimePowerArithmetic.source_on_index_set_weight_read_off
    h.restrictedArithmeticData hn

theorem concrete_object_restricted_index_pairing_formula_source_evaluator
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeConcreteObject W f g lambda)
    {n : ℕ} (hn : n ∈ W.restrictedPrimeIndexSet lambda) :
    let atom := h.restrictedArithmeticData.atIndex n hn
    W.primePowerPairing n f g =
      (1 / Real.sqrt (n : ℝ)) *
        (atom.sourcePairing.model.sourceEvaluation.sourceEvaluator.valueAt
            (W.convolutionStar f g) (n : ℝ) +
          atom.sourcePairing.model.sourceEvaluation.sourceEvaluator.valueAt
            (W.convolutionStar f g) ((n : ℝ)⁻¹)) :=
  by
    let sourceEvaluation :=
      (h.restrictedArithmeticData.atIndex n hn).sourcePairing.model.sourceEvaluation
    rw [PrimePowerArithmetic.source_on_index_set_pairing_formula_source_evaluations
        h.restrictedArithmeticData hn,
      PrimePowerEvaluation.source_forward_value_at_source_points sourceEvaluation,
      PrimePowerEvaluation.source_inverse_value_at_source_points sourceEvaluation]

theorem concrete_object_restricted_index_pairing_formula_source_evaluations
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeConcreteObject W f g lambda)
    {n : ℕ} (hn : n ∈ W.restrictedPrimeIndexSet lambda) :
    let atom := h.restrictedArithmeticData.atIndex n hn
    W.primePowerPairing n f g =
      (1 / Real.sqrt (n : ℝ)) *
        (atom.sourcePairing.model.sourceEvaluation.forwardValue +
          atom.sourcePairing.model.sourceEvaluation.inverseValue) :=
  PrimePowerArithmetic.source_on_index_set_pairing_formula_source_evaluations
    h.restrictedArithmeticData hn

theorem concrete_object_restricted_index_term_formula_source_evaluator
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeConcreteObject W f g lambda)
    {n : ℕ} (hn : n ∈ W.restrictedPrimeIndexSet lambda) :
    W.finitePrimeTerm n (W.convolutionStar f g) =
      PrimePowerArithmetic.SourceFinitePrimeEvaluatorAtom W f g n
        (h.restrictedArithmeticData.atIndex n hn) :=
  PrimePowerArithmetic.source_on_index_set_finite_prime_term_formula_source_evaluator
    h.restrictedArithmeticData hn

theorem concrete_object_restricted_index_term_formula_source_evaluations
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeConcreteObject W f g lambda)
    {n : ℕ} (hn : n ∈ W.restrictedPrimeIndexSet lambda) :
    let atom := h.restrictedArithmeticData.atIndex n hn
    W.finitePrimeTerm n (W.convolutionStar f g) =
      ArithmeticFunction.vonMangoldt n *
        ((1 / Real.sqrt (n : ℝ)) *
          (atom.sourcePairing.model.sourceEvaluation.forwardValue +
            atom.sourcePairing.model.sourceEvaluation.inverseValue)) :=
  PrimePowerArithmetic.source_on_index_set_finite_prime_term_formula_mathlib_source_evaluations
    h.restrictedArithmeticData hn

theorem concrete_object_restricted_index_von_mangoldt_pairing_formula_source_evaluations
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeConcreteObject W f g lambda)
    {n : ℕ} (hn : n ∈ W.restrictedPrimeIndexSet lambda) :
    let atom := h.restrictedArithmeticData.atIndex n hn
    W.vonMangoldtWeight n * W.primePowerPairing n f g =
      ArithmeticFunction.vonMangoldt n *
        ((1 / Real.sqrt (n : ℝ)) *
          (atom.sourcePairing.model.sourceEvaluation.forwardValue +
            atom.sourcePairing.model.sourceEvaluation.inverseValue)) :=
  PrimePowerArithmetic.source_on_index_set_von_mangoldt_pairing_product_formula_source_evaluations
    h.restrictedArithmeticData hn

theorem concrete_object_weight_read_off
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeConcreteObject W f g lambda)
    (n : ℕ) :
    W.vonMangoldtWeight n = ArithmeticFunction.vonMangoldt n := by
  exact (h.localFormulaData n).weightReadOff

theorem concrete_object_weight_eq_mathlib
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeConcreteObject W f g lambda)
    (n : ℕ) :
    W.vonMangoldtWeight n = ArithmeticFunction.vonMangoldt n :=
  concrete_object_weight_read_off h n

theorem concrete_object_pairing_formula_source_evaluator
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeConcreteObject W f g lambda)
    (n : ℕ) :
    W.primePowerPairing n f g =
      (1 / Real.sqrt (n : ℝ)) *
        ((h.atomData n).sourcePairing.model.sourceEvaluation.sourceEvaluator.valueAt
            (W.convolutionStar f g) (n : ℝ) +
          (h.atomData n).sourcePairing.model.sourceEvaluation.sourceEvaluator.valueAt
            (W.convolutionStar f g) ((n : ℝ)⁻¹)) := by
  rw [PrimePowerArithmetic.source_pairing_formula_source_evaluations
      (h.atomData n),
    PrimePowerEvaluation.source_forward_value_at_source_points
      (h.atomData n).sourcePairing.model.sourceEvaluation,
    PrimePowerEvaluation.source_inverse_value_at_source_points
      (h.atomData n).sourcePairing.model.sourceEvaluation]

theorem concrete_object_pairing_formula_source_evaluations
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeConcreteObject W f g lambda)
    (n : ℕ) :
    W.primePowerPairing n f g =
      (1 / Real.sqrt (n : ℝ)) *
        ((h.atomData n).sourcePairing.model.sourceEvaluation.forwardValue +
          (h.atomData n).sourcePairing.model.sourceEvaluation.inverseValue) :=
  PrimePowerArithmetic.source_pairing_formula_source_evaluations
    (h.atomData n)

theorem concrete_object_term_formula_mathlib_pairing
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeConcreteObject W f g lambda)
    (n : ℕ) :
    W.finitePrimeTerm n (W.convolutionStar f g) =
      ArithmeticFunction.vonMangoldt n * W.primePowerPairing n f g :=
  PrimePowerArithmetic.source_finite_prime_term_formula_mathlib_pairing
    (h.atomData n)

theorem concrete_object_term_formula_source_evaluator
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeConcreteObject W f g lambda)
    (n : ℕ) :
    W.finitePrimeTerm n (W.convolutionStar f g) =
      PrimePowerArithmetic.SourceFinitePrimeEvaluatorAtom W f g n
        (h.atomData n) := by
  rw [concrete_object_term_formula_mathlib_pairing h n]
  dsimp [PrimePowerArithmetic.SourceFinitePrimeEvaluatorAtom]
  congr 1
  exact concrete_object_pairing_formula_source_evaluations h n

theorem concrete_object_term_formula_source_evaluations
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeConcreteObject W f g lambda)
    (n : ℕ) :
    let atom := h.atomData n
    W.finitePrimeTerm n (W.convolutionStar f g) =
      ArithmeticFunction.vonMangoldt n *
        ((1 / Real.sqrt (n : ℝ)) *
          (atom.sourcePairing.model.sourceEvaluation.forwardValue +
            atom.sourcePairing.model.sourceEvaluation.inverseValue)) :=
  PrimePowerArithmetic.source_finite_prime_term_formula_mathlib_source_evaluations
    (h.atomData n)

theorem concrete_object_von_mangoldt_pairing_product_formula_source_evaluations
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeConcreteObject W f g lambda)
    (n : ℕ) :
    let atom := h.atomData n
    W.vonMangoldtWeight n * W.primePowerPairing n f g =
      ArithmeticFunction.vonMangoldt n *
        ((1 / Real.sqrt (n : ℝ)) *
          (atom.sourcePairing.model.sourceEvaluation.forwardValue +
            atom.sourcePairing.model.sourceEvaluation.inverseValue)) :=
  PrimePowerArithmetic.source_von_mangoldt_pairing_product_formula_source_evaluations
    (h.atomData n)

theorem concrete_object_global_finite_prime_term_sum_read_off
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeConcreteObject W f g lambda) :
    (∑ n ∈ W.globalPrimeIndexSet,
      W.finitePrimeTerm n (W.convolutionStar f g)) =
      PrimePowerArithmetic.SourceGlobalFinitePrimeEvaluatorSum
        W f g h.certificate.atoms := by
  rw [← arithmetic_global_scoped_sum_eq_global_sum_of_certificate
    h.certificate]
  exact h.globalSumFormulaData.finitePrimeTermSumReadOff

theorem concrete_object_global_von_mangoldt_pairing_sum_read_off
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeConcreteObject W f g lambda) :
    (∑ n ∈ W.globalPrimeIndexSet,
      W.vonMangoldtWeight n * W.primePowerPairing n f g) =
      PrimePowerArithmetic.SourceGlobalFinitePrimeEvaluatorSum
        W f g h.certificate.atoms := by
  rw [← arithmetic_global_scoped_sum_eq_global_sum_of_certificate
    h.certificate]
  exact h.globalSumFormulaData.vonMangoldtPairingSumReadOff

theorem concrete_object_restricted_finite_prime_term_sum_read_off
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeConcreteObject W f g lambda) :
    (∑ n ∈ W.restrictedPrimeIndexSet lambda,
      W.finitePrimeTerm n (W.convolutionStar f g)) =
      PrimePowerArithmetic.SourceRestrictedFinitePrimeEvaluatorSum
        W f g lambda h.certificate.atoms := by
  rw [← arithmetic_restricted_scoped_sum_eq_restricted_sum_of_certificate
    h.certificate]
  exact h.restrictedSumFormulaData.finitePrimeTermSumReadOff

theorem concrete_object_restricted_von_mangoldt_pairing_sum_read_off
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeConcreteObject W f g lambda) :
    (∑ n ∈ W.restrictedPrimeIndexSet lambda,
      W.vonMangoldtWeight n * W.primePowerPairing n f g) =
      PrimePowerArithmetic.SourceRestrictedFinitePrimeEvaluatorSum
        W f g lambda h.certificate.atoms := by
  rw [← arithmetic_restricted_scoped_sum_eq_restricted_sum_of_certificate
    h.certificate]
  exact h.restrictedSumFormulaData.vonMangoldtPairingSumReadOff

theorem concrete_object_global_mathlib_finite_prime_term_sum_read_off
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeConcreteObject W f g lambda) :
    (∑ n ∈ W.globalPrimeIndexSet,
      W.finitePrimeTerm n (W.convolutionStar f g)) =
      PrimePowerArithmetic.MathlibGlobalFinitePrimeEvaluatorSumOnIndexSet
        W f g (arithmetic_data_on_global_index_set_of_certificate h.certificate) :=
  h.globalSumFormulaData.finitePrimeTermSumReadOff

theorem concrete_object_global_mathlib_von_mangoldt_pairing_sum_read_off
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeConcreteObject W f g lambda) :
    (∑ n ∈ W.globalPrimeIndexSet,
      W.vonMangoldtWeight n * W.primePowerPairing n f g) =
      PrimePowerArithmetic.MathlibGlobalFinitePrimeEvaluatorSumOnIndexSet
        W f g (arithmetic_data_on_global_index_set_of_certificate h.certificate) :=
  h.globalSumFormulaData.vonMangoldtPairingSumReadOff

theorem concrete_object_restricted_mathlib_finite_prime_term_sum_read_off
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeConcreteObject W f g lambda) :
    (∑ n ∈ W.restrictedPrimeIndexSet lambda,
      W.finitePrimeTerm n (W.convolutionStar f g)) =
      PrimePowerArithmetic.MathlibRestrictedFinitePrimeEvaluatorSumOnIndexSet
        W f g lambda
        (arithmetic_data_on_restricted_index_set_of_certificate h.certificate) :=
  h.restrictedSumFormulaData.finitePrimeTermSumReadOff

theorem concrete_object_restricted_mathlib_von_mangoldt_pairing_sum_read_off
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeConcreteObject W f g lambda) :
    (∑ n ∈ W.restrictedPrimeIndexSet lambda,
      W.vonMangoldtWeight n * W.primePowerPairing n f g) =
      PrimePowerArithmetic.MathlibRestrictedFinitePrimeEvaluatorSumOnIndexSet
        W f g lambda
        (arithmetic_data_on_restricted_index_set_of_certificate h.certificate) :=
  h.restrictedSumFormulaData.vonMangoldtPairingSumReadOff

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
        PrimePowerSupport.SourceVisibleAtomData W f g n :=
  h.support.visibleIff

theorem global_exact_of_certificate
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeCertificate W f g lambda) :
    ∀ n : ℕ,
      n ∈ W.globalPrimeIndexSet ↔
        PrimePowerSupport.SourceGlobalIndexData W f g n :=
  fun n => by
    constructor
    · exact h.support.globalIndexData n
    · intro hdata
      exact h.support.routeVisibleGlobalIndex n
        ((h.support.visibleIff n).2
          (PrimePowerSupport.source_global_index_to_visible_atom_data hdata))

theorem restricted_exact_of_certificate
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeCertificate W f g lambda) :
    ∀ n : ℕ,
      n ∈ W.restrictedPrimeIndexSet lambda ↔
        PrimePowerSupport.SourceRestrictedIndexData W f g lambda n :=
  fun n => by
    constructor
    · exact h.support.restrictedIndexData n
    · intro hdata
      exact h.support.routeVisibleRestrictedIndex n
        ((h.support.visibleIff n).2
          (PrimePowerSupport.source_restricted_index_to_visible_atom_data hdata))
        hdata.lambdaCut.1 hdata.lambdaCut.2

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
