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

theorem arithmetic_atom_visible_in_support_source_test_of_certificate
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeArithmeticCertificate W f g lambda)
    (n : ℕ) :
    h.support.sourceTest.sourceAtomVisible n :=
  PrimePowerArithmetic.source_atom_visible_uses_normalization_source_test
    h.atomsUseSupportSourceTest n

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
    PrimePowerSupport.SourceGlobalIndexData
      PrimePowerArithmetic.SourcePrimePowerIndex
      h.support.sourceTest.sourceAtomVisible n := by
  let hdata := (h.support.globalExact n).1 hn
  exact
    { primePowerIndex := hdata.primePowerIndex
      atomVisible := hdata.atomVisible }

theorem arithmetic_global_index_prime_power_of_certificate
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeArithmeticCertificate W f g lambda)
    {n : ℕ} (hn : n ∈ W.globalPrimeIndexSet) :
    PrimePowerArithmetic.SourcePrimePowerIndex n :=
  (arithmetic_global_index_source_data_of_certificate h hn).primePowerIndex

theorem arithmetic_global_index_isPrimePow_of_certificate
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeArithmeticCertificate W f g lambda)
    {n : ℕ} (hn : n ∈ W.globalPrimeIndexSet) :
    IsPrimePow n :=
  PrimePowerArithmetic.source_prime_power_index_iff_mathlib.1
    (arithmetic_global_index_prime_power_of_certificate h hn)

theorem arithmetic_global_index_visible_of_certificate
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeArithmeticCertificate W f g lambda)
    {n : ℕ} (hn : n ∈ W.globalPrimeIndexSet) :
    h.support.sourceTest.sourceAtomVisible n :=
  (arithmetic_global_index_source_data_of_certificate h hn).atomVisible

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
    PrimePowerSupport.SourceRestrictedIndexData
      PrimePowerArithmetic.SourcePrimePowerIndex
      h.support.sourceTest.sourceAtomVisible lambda n := by
  let hdata := (h.support.restrictedExact n).1 hn
  exact
    { primePowerIndex := hdata.primePowerIndex
      atomVisible := hdata.atomVisible
      lambdaCut := hdata.lambdaCut }

theorem arithmetic_restricted_index_lambda_cut_of_certificate
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeArithmeticCertificate W f g lambda)
    {n : ℕ} (hn : n ∈ W.restrictedPrimeIndexSet lambda) :
    PrimePowerSupport.SourceLambdaCut lambda n :=
  (arithmetic_restricted_index_source_data_of_certificate h hn).lambdaCut

theorem arithmetic_restricted_index_prime_power_of_certificate
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeArithmeticCertificate W f g lambda)
    {n : ℕ} (hn : n ∈ W.restrictedPrimeIndexSet lambda) :
    PrimePowerArithmetic.SourcePrimePowerIndex n :=
  (arithmetic_restricted_index_source_data_of_certificate h hn).primePowerIndex

theorem arithmetic_restricted_index_isPrimePow_of_certificate
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeArithmeticCertificate W f g lambda)
    {n : ℕ} (hn : n ∈ W.restrictedPrimeIndexSet lambda) :
    IsPrimePow n :=
  PrimePowerArithmetic.source_prime_power_index_iff_mathlib.1
    (arithmetic_restricted_index_prime_power_of_certificate h hn)

theorem arithmetic_restricted_index_visible_of_certificate
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeArithmeticCertificate W f g lambda)
    {n : ℕ} (hn : n ∈ W.restrictedPrimeIndexSet lambda) :
    h.support.sourceTest.sourceAtomVisible n :=
  (arithmetic_restricted_index_source_data_of_certificate h hn).atomVisible

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

theorem arithmetic_global_sum_formula_data_of_certificate
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeArithmeticCertificate W f g lambda) :
    PrimePowerArithmetic.SourceGlobalFinitePrimeSumFormulaData
      W f g h.atoms where
  finitePrimeTermSumReadOff :=
    arithmetic_global_sum_formula_of_certificate h
  vonMangoldtPairingSumReadOff :=
    arithmetic_global_von_mangoldt_pairing_sum_formula_of_certificate h

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

theorem arithmetic_restricted_sum_formula_data_of_certificate
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeArithmeticCertificate W f g lambda) :
    PrimePowerArithmetic.SourceRestrictedFinitePrimeSumFormulaData
      W f g lambda h.atoms where
  finitePrimeTermSumReadOff :=
    arithmetic_restricted_sum_formula_of_certificate h
  vonMangoldtPairingSumReadOff :=
    arithmetic_restricted_von_mangoldt_pairing_sum_formula_of_certificate h

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

structure FixedLambdaFinitePrimeConcreteObject
    (W : WeilFormSymbols) (f g : TestFunction) (lambda : ℝ) where
  certificate : FixedLambdaFinitePrimeArithmeticCertificate W f g lambda
  exactSupport : FinitePrimeExact.ExactSupportAtLambda W f g lambda
  sourceTest : PrimePowerTest.SourceTestEvaluationInterface W f g
  sourceTest_eq_support :
    sourceTest = certificate.support.sourceTest
  atomsUseSourceTest :
    PrimePowerArithmetic.UsesSourceTest certificate.atoms sourceTest
  atomData :
    ∀ n : ℕ, PrimePowerArithmetic.SourceFinitePrimeArithmeticData W f g n
  atomData_eq_certificate :
    ∀ n : ℕ, atomData n = certificate.atoms.atIndex n
  globalIndexData :
    ∀ {n : ℕ},
      n ∈ W.globalPrimeIndexSet →
        PrimePowerSupport.SourceGlobalIndexData
          PrimePowerArithmetic.SourcePrimePowerIndex
          sourceTest.sourceAtomVisible n
  restrictedIndexData :
    ∀ {n : ℕ},
      n ∈ W.restrictedPrimeIndexSet lambda →
        PrimePowerSupport.SourceRestrictedIndexData
          PrimePowerArithmetic.SourcePrimePowerIndex
          sourceTest.sourceAtomVisible lambda n
  localFormulaData :
    ∀ n : ℕ,
      PrimePowerArithmetic.SourceFinitePrimeLocalFormulaData W f g n
        (atomData n)
  globalSumFormulaData :
    PrimePowerArithmetic.SourceGlobalFinitePrimeSumFormulaData
      W f g certificate.atoms
  restrictedSumFormulaData :
    PrimePowerArithmetic.SourceRestrictedFinitePrimeSumFormulaData
      W f g lambda certificate.atoms

noncomputable def concrete_object_of_arithmetic_certificate
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeArithmeticCertificate W f g lambda) :
    FixedLambdaFinitePrimeConcreteObject W f g lambda where
  certificate := h
  exactSupport := exact_support_of_arithmetic_certificate h
  sourceTest := h.support.sourceTest
  sourceTest_eq_support := rfl
  atomsUseSourceTest := arithmetic_atoms_use_support_source_test h
  atomData := h.atoms.atIndex
  atomData_eq_certificate := fun _ => rfl
  globalIndexData := by
    intro n hn
    exact arithmetic_global_index_source_data_of_certificate h hn
  restrictedIndexData := by
    intro n hn
    exact arithmetic_restricted_index_source_data_of_certificate h hn
  localFormulaData := fun n =>
    PrimePowerArithmetic.source_finite_prime_local_formula_data
      (h.atoms.atIndex n)
  globalSumFormulaData :=
    arithmetic_global_sum_formula_data_of_certificate h
  restrictedSumFormulaData :=
    arithmetic_restricted_sum_formula_data_of_certificate h

theorem concrete_object_source_test_eq_support
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeConcreteObject W f g lambda) :
    h.sourceTest = h.certificate.support.sourceTest :=
  h.sourceTest_eq_support

theorem concrete_object_global_index_prime_power
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeConcreteObject W f g lambda)
    {n : ℕ} (hn : n ∈ W.globalPrimeIndexSet) :
    PrimePowerArithmetic.SourcePrimePowerIndex n :=
  (h.globalIndexData hn).primePowerIndex

theorem concrete_object_global_index_isPrimePow
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeConcreteObject W f g lambda)
    {n : ℕ} (hn : n ∈ W.globalPrimeIndexSet) :
    IsPrimePow n :=
  PrimePowerArithmetic.source_prime_power_index_iff_mathlib.1
    (concrete_object_global_index_prime_power h hn)

theorem concrete_object_global_index_visible
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeConcreteObject W f g lambda)
    {n : ℕ} (hn : n ∈ W.globalPrimeIndexSet) :
    h.sourceTest.sourceAtomVisible n :=
  (h.globalIndexData hn).atomVisible

theorem concrete_object_restricted_index_prime_power
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeConcreteObject W f g lambda)
    {n : ℕ} (hn : n ∈ W.restrictedPrimeIndexSet lambda) :
    PrimePowerArithmetic.SourcePrimePowerIndex n :=
  (h.restrictedIndexData hn).primePowerIndex

theorem concrete_object_restricted_index_isPrimePow
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeConcreteObject W f g lambda)
    {n : ℕ} (hn : n ∈ W.restrictedPrimeIndexSet lambda) :
    IsPrimePow n :=
  PrimePowerArithmetic.source_prime_power_index_iff_mathlib.1
    (concrete_object_restricted_index_prime_power h hn)

theorem concrete_object_restricted_index_visible
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeConcreteObject W f g lambda)
    {n : ℕ} (hn : n ∈ W.restrictedPrimeIndexSet lambda) :
    h.sourceTest.sourceAtomVisible n :=
  (h.restrictedIndexData hn).atomVisible

theorem concrete_object_restricted_index_lambda_cut
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeConcreteObject W f g lambda)
    {n : ℕ} (hn : n ∈ W.restrictedPrimeIndexSet lambda) :
    PrimePowerSupport.SourceLambdaCut lambda n :=
  (h.restrictedIndexData hn).lambdaCut

theorem concrete_object_weight_read_off
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeConcreteObject W f g lambda)
    (n : ℕ) :
    W.vonMangoldtWeight n =
      PrimePowerArithmetic.SourceVonMangoldtWeight n :=
  (h.localFormulaData n).weightReadOff

theorem concrete_object_weight_eq_mathlib
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeConcreteObject W f g lambda)
    (n : ℕ) :
    W.vonMangoldtWeight n = ArithmeticFunction.vonMangoldt n := by
  rw [concrete_object_weight_read_off h n,
    PrimePowerArithmetic.source_von_mangoldt_weight_eq_mathlib]

theorem concrete_object_pairing_formula_source_evaluator
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeConcreteObject W f g lambda)
    (n : ℕ) :
    W.primePowerPairing n f g =
      (1 / Real.sqrt (n : ℝ)) *
        ((h.atomData n).sourcePairing.model.sourceEvaluation.sourceEvaluator.valueAt
            (W.convolutionStar f g) (n : ℝ) +
          (h.atomData n).sourcePairing.model.sourceEvaluation.sourceEvaluator.valueAt
            (W.convolutionStar f g) ((n : ℝ)⁻¹)) :=
  (h.localFormulaData n).pairingFormulaSourceEvaluator

theorem concrete_object_term_formula_source_evaluator
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeConcreteObject W f g lambda)
    (n : ℕ) :
    W.finitePrimeTerm n (W.convolutionStar f g) =
      PrimePowerArithmetic.SourceFinitePrimeEvaluatorAtom W f g n
        (h.atomData n) :=
  (h.localFormulaData n).termFormulaSourceEvaluator

theorem concrete_object_term_formula_mathlib_pairing
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeConcreteObject W f g lambda)
    (n : ℕ) :
    W.finitePrimeTerm n (W.convolutionStar f g) =
      ArithmeticFunction.vonMangoldt n * W.primePowerPairing n f g :=
  PrimePowerArithmetic.source_finite_prime_term_formula_mathlib_pairing
    (h.atomData n)

theorem concrete_object_global_finite_prime_term_sum_read_off
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeConcreteObject W f g lambda) :
    (∑ n ∈ W.globalPrimeIndexSet,
      W.finitePrimeTerm n (W.convolutionStar f g)) =
      PrimePowerArithmetic.SourceGlobalFinitePrimeEvaluatorSum
        W f g h.certificate.atoms :=
  h.globalSumFormulaData.finitePrimeTermSumReadOff

theorem concrete_object_global_von_mangoldt_pairing_sum_read_off
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeConcreteObject W f g lambda) :
    (∑ n ∈ W.globalPrimeIndexSet,
      W.vonMangoldtWeight n * W.primePowerPairing n f g) =
      PrimePowerArithmetic.SourceGlobalFinitePrimeEvaluatorSum
        W f g h.certificate.atoms :=
  h.globalSumFormulaData.vonMangoldtPairingSumReadOff

theorem concrete_object_restricted_finite_prime_term_sum_read_off
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeConcreteObject W f g lambda) :
    (∑ n ∈ W.restrictedPrimeIndexSet lambda,
      W.finitePrimeTerm n (W.convolutionStar f g)) =
      PrimePowerArithmetic.SourceRestrictedFinitePrimeEvaluatorSum
        W f g lambda h.certificate.atoms :=
  h.restrictedSumFormulaData.finitePrimeTermSumReadOff

theorem concrete_object_restricted_von_mangoldt_pairing_sum_read_off
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeConcreteObject W f g lambda) :
    (∑ n ∈ W.restrictedPrimeIndexSet lambda,
      W.vonMangoldtWeight n * W.primePowerPairing n f g) =
      PrimePowerArithmetic.SourceRestrictedFinitePrimeEvaluatorSum
        W f g lambda h.certificate.atoms :=
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
        PrimePowerSupport.SourceVisibleAtomData h.support.sourcePrimePowerIndex
          (fun n => h.support.sourceAtomVisible n (W.convolutionStar f g)) n :=
  h.support.visibleIff

theorem global_exact_of_certificate
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeCertificate W f g lambda) :
    ∀ n : ℕ,
      n ∈ W.globalPrimeIndexSet ↔
        PrimePowerSupport.SourceGlobalIndexData h.support.sourcePrimePowerIndex
          (fun n => h.support.sourceAtomVisible n (W.convolutionStar f g)) n :=
  h.support.globalExact

theorem restricted_exact_of_certificate
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeCertificate W f g lambda) :
    ∀ n : ℕ,
      n ∈ W.restrictedPrimeIndexSet lambda ↔
        PrimePowerSupport.SourceRestrictedIndexData h.support.sourcePrimePowerIndex
          (fun n => h.support.sourceAtomVisible n (W.convolutionStar f g))
          lambda n :=
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

theorem restricted_index_set_eq_global_of_certificate
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeCertificate W f g lambda) :
    W.restrictedPrimeIndexSet lambda = W.globalPrimeIndexSet :=
  FinitePrimeExact.restricted_index_set_eq_global_of_exact_support
    (exact_support_of_certificate h)

theorem restricted_index_set_eq_global_of_arithmetic_certificate
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : FixedLambdaFinitePrimeArithmeticCertificate W f g lambda) :
    W.restrictedPrimeIndexSet lambda = W.globalPrimeIndexSet :=
  FinitePrimeExact.restricted_index_set_eq_global_of_exact_support
    (exact_support_of_arithmetic_certificate h)

end FinitePrimeCertificate
end CCM25Concrete
end Source
end ConnesWeilRH
