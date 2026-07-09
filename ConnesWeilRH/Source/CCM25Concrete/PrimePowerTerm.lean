/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Source.CCM25Concrete.PrimePowerSupport
import ConnesWeilRH.Source.CCM25Concrete.PrimePowerArithmetic

/-!
# CCM25 pointwise finite-prime term normalization

This module isolates the local finite-prime atom before any finite sum is
formed. The local atom is the source `Lambda(n) * <g|T(n)g>` normalization; the
minus sign belongs to the surrounding `Psi` or `QW_lambda` formula.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace PrimePowerTerm

structure SourceFinitePrimeAtomData
    (W : WeilFormSymbols) (f g : TestFunction) (n : ℕ) where
  sourcePrimePowerIndex : IsPrimePow n
  sourceAtomVisible :
    W.finitePrimeAtomVisible n (W.convolutionStar f g)
  sourcePairing :
    PrimePowerPairing.SourcePrimePowerPairingData W f g n
  sourcePrimePowerPairing : ℝ
  sourcePrimePowerPairing_eq_sourcePairing :
    sourcePrimePowerPairing = sourcePairing.model.sourceTPairing
  weightReadOff :
    W.vonMangoldtWeight n = ArithmeticFunction.vonMangoldt n
  pairingReadOff :
    W.primePowerPairing n f g = sourcePrimePowerPairing
  termReadOff :
    W.finitePrimeTerm n (W.convolutionStar f g) =
      ArithmeticFunction.vonMangoldt n * sourcePrimePowerPairing

structure SourcePrimePowerTermAtIndex
    (W : WeilFormSymbols) (f g : TestFunction) (n : ℕ) where
  sourcePrimePowerIndex : IsPrimePow n
  sourceAtomVisible :
    W.finitePrimeAtomVisible n (W.convolutionStar f g)
  normalized :
    W.finitePrimeTerm n (W.convolutionStar f g) =
      W.vonMangoldtWeight n * W.primePowerPairing n f g

def source_prime_power_term_of_atom_data
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h : SourceFinitePrimeAtomData W f g n) :
    SourcePrimePowerTermAtIndex W f g n where
  sourcePrimePowerIndex := h.sourcePrimePowerIndex
  sourceAtomVisible := h.sourceAtomVisible
  normalized := by
    rw [h.termReadOff, h.weightReadOff, h.pairingReadOff]

theorem source_prime_power_term_of_atom_data_index
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h : SourceFinitePrimeAtomData W f g n) :
    (source_prime_power_term_of_atom_data h).sourcePrimePowerIndex =
      h.sourcePrimePowerIndex :=
  rfl

theorem source_prime_power_term_of_atom_data_visible
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h : SourceFinitePrimeAtomData W f g n) :
    (source_prime_power_term_of_atom_data h).sourceAtomVisible =
      h.sourceAtomVisible :=
  rfl

theorem source_prime_power_term_of_atom_data_normalized_apply
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h : SourceFinitePrimeAtomData W f g n) :
    W.finitePrimeTerm n (W.convolutionStar f g) =
      W.vonMangoldtWeight n * W.primePowerPairing n f g :=
  (source_prime_power_term_of_atom_data h).normalized

noncomputable def source_atom_data_of_arithmetic_data
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h :
      PrimePowerArithmetic.SourceFinitePrimeArithmeticData W f g n) :
    SourceFinitePrimeAtomData W f g n where
  sourcePrimePowerIndex :=
    h.sourcePrimePowerIndex
  sourceAtomVisible := h.sourceAtomVisible
  sourcePairing := h.sourcePairing
  sourcePrimePowerPairing := h.sourcePrimePowerPairing
  sourcePrimePowerPairing_eq_sourcePairing := by
    calc
      h.sourcePrimePowerPairing = W.primePowerPairing n f g :=
        h.pairingReadOff.symm
      _ = h.sourcePairing.model.sourceTPairing :=
        h.sourcePairing.pairingReadOff
  weightReadOff := h.weightReadOff
  pairingReadOff := h.pairingReadOff
  termReadOff := h.termReadOff

theorem source_atom_data_of_arithmetic_data_index
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h :
      PrimePowerArithmetic.SourceFinitePrimeArithmeticData W f g n) :
    (source_atom_data_of_arithmetic_data h).sourcePrimePowerIndex =
      h.sourcePrimePowerIndex :=
  rfl

theorem source_atom_data_of_arithmetic_data_visible
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h :
      PrimePowerArithmetic.SourceFinitePrimeArithmeticData W f g n) :
    (source_atom_data_of_arithmetic_data h).sourceAtomVisible =
      h.sourceAtomVisible :=
  rfl

theorem source_atom_data_of_arithmetic_data_pairing_data
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h :
      PrimePowerArithmetic.SourceFinitePrimeArithmeticData W f g n) :
    (source_atom_data_of_arithmetic_data h).sourcePairing =
      h.sourcePairing :=
  rfl

theorem source_atom_data_of_arithmetic_data_pairing_value
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h :
      PrimePowerArithmetic.SourceFinitePrimeArithmeticData W f g n) :
    (source_atom_data_of_arithmetic_data h).sourcePrimePowerPairing =
      h.sourcePrimePowerPairing :=
  rfl

theorem source_atom_data_of_arithmetic_data_weight_read_off
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h :
      PrimePowerArithmetic.SourceFinitePrimeArithmeticData W f g n) :
    (source_atom_data_of_arithmetic_data h).weightReadOff =
      h.weightReadOff :=
  rfl

theorem source_atom_data_of_arithmetic_data_pairing_read_off
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h :
      PrimePowerArithmetic.SourceFinitePrimeArithmeticData W f g n) :
    (source_atom_data_of_arithmetic_data h).pairingReadOff =
      h.pairingReadOff :=
  rfl

theorem source_atom_data_of_arithmetic_data_term_read_off
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h :
      PrimePowerArithmetic.SourceFinitePrimeArithmeticData W f g n) :
    (source_atom_data_of_arithmetic_data h).termReadOff =
      h.termReadOff :=
  rfl

theorem source_atom_data_of_arithmetic_data_weight_read_off_apply
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h :
      PrimePowerArithmetic.SourceFinitePrimeArithmeticData W f g n) :
    W.vonMangoldtWeight n = ArithmeticFunction.vonMangoldt n :=
  (source_atom_data_of_arithmetic_data h).weightReadOff

theorem source_atom_data_of_arithmetic_data_pairing_read_off_apply
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h :
      PrimePowerArithmetic.SourceFinitePrimeArithmeticData W f g n) :
    W.primePowerPairing n f g =
      (source_atom_data_of_arithmetic_data h).sourcePrimePowerPairing :=
  (source_atom_data_of_arithmetic_data h).pairingReadOff

theorem source_atom_data_of_arithmetic_data_term_read_off_apply
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h :
      PrimePowerArithmetic.SourceFinitePrimeArithmeticData W f g n) :
    W.finitePrimeTerm n (W.convolutionStar f g) =
      ArithmeticFunction.vonMangoldt n *
        (source_atom_data_of_arithmetic_data h).sourcePrimePowerPairing :=
  (source_atom_data_of_arithmetic_data h).termReadOff

theorem source_atom_data_of_arithmetic_data_prime_power_index
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h :
      PrimePowerArithmetic.SourceFinitePrimeArithmeticData W f g n) :
    IsPrimePow n :=
  PrimePowerArithmetic.source_prime_power_index_of_arithmetic_data h

theorem source_atom_data_of_arithmetic_data_one_lt
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h :
      PrimePowerArithmetic.SourceFinitePrimeArithmeticData W f g n) :
    1 < n :=
  PrimePowerArithmetic.source_prime_power_index_one_lt_of_arithmetic_data h

theorem source_atom_data_of_arithmetic_data_pairing_eq_model_pairing
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h :
      PrimePowerArithmetic.SourceFinitePrimeArithmeticData W f g n) :
    (source_atom_data_of_arithmetic_data h).sourcePrimePowerPairing =
      h.sourcePairing.model.sourceTPairing :=
  (source_atom_data_of_arithmetic_data h).sourcePrimePowerPairing_eq_sourcePairing

theorem source_atom_data_of_arithmetic_data_pairing_read_off_model_pairing
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h :
      PrimePowerArithmetic.SourceFinitePrimeArithmeticData W f g n) :
    W.primePowerPairing n f g =
      h.sourcePairing.model.sourceTPairing :=
  h.sourcePairing.pairingReadOff

theorem source_atom_data_of_arithmetic_data_term_normalized
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h :
      PrimePowerArithmetic.SourceFinitePrimeArithmeticData W f g n) :
    W.finitePrimeTerm n (W.convolutionStar f g) =
      W.vonMangoldtWeight n * W.primePowerPairing n f g :=
  by
    rw [h.termReadOff, h.weightReadOff, h.pairingReadOff]

theorem source_atom_data_of_arithmetic_data_term_formula_source_evaluator
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h :
      PrimePowerArithmetic.SourceFinitePrimeArithmeticData W f g n) :
    W.finitePrimeTerm n (W.convolutionStar f g) =
      PrimePowerArithmetic.SourceFinitePrimeEvaluatorAtom W f g n h :=
  PrimePowerArithmetic.source_finite_prime_term_formula_source_evaluator h

theorem source_weight_read_off
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h : SourceFinitePrimeAtomData W f g n) :
    W.vonMangoldtWeight n = ArithmeticFunction.vonMangoldt n :=
  h.weightReadOff

theorem source_prime_power_index_of_atom_data
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h : SourceFinitePrimeAtomData W f g n) :
    IsPrimePow n :=
  h.sourcePrimePowerIndex

theorem source_prime_power_index_one_lt_of_atom_data
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h : SourceFinitePrimeAtomData W f g n) :
    1 < n :=
  IsPrimePow.one_lt
    (source_prime_power_index_of_atom_data h)

theorem source_prime_power_index_of_term_at_index
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h : SourcePrimePowerTermAtIndex W f g n) :
    IsPrimePow n :=
  h.sourcePrimePowerIndex

theorem source_prime_power_index_one_lt_of_term_at_index
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h : SourcePrimePowerTermAtIndex W f g n) :
    1 < n :=
  IsPrimePow.one_lt
    (source_prime_power_index_of_term_at_index h)

theorem source_pairing_read_off
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h : SourceFinitePrimeAtomData W f g n) :
    W.primePowerPairing n f g = h.sourcePrimePowerPairing :=
  h.pairingReadOff

def source_pairing_data_of_atom_data
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h : SourceFinitePrimeAtomData W f g n) :
    PrimePowerPairing.SourcePrimePowerPairingData W f g n :=
  h.sourcePairing

theorem source_prime_power_pairing_eq_source_pairing
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h : SourceFinitePrimeAtomData W f g n) :
    h.sourcePrimePowerPairing = h.sourcePairing.model.sourceTPairing :=
  h.sourcePrimePowerPairing_eq_sourcePairing

theorem source_pairing_read_off_from_pairing_data
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h : SourceFinitePrimeAtomData W f g n) :
    W.primePowerPairing n f g =
      h.sourcePairing.model.sourceTPairing := by
  rw [h.pairingReadOff, h.sourcePrimePowerPairing_eq_sourcePairing]

theorem source_pairing_formula_source_evaluator
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h : SourceFinitePrimeAtomData W f g n) :
    W.primePowerPairing n f g =
      (1 / Real.sqrt (n : ℝ)) *
        (h.sourcePairing.model.sourceEvaluation.sourceEvaluator.valueAt
            (W.convolutionStar f g) (n : ℝ) +
          h.sourcePairing.model.sourceEvaluation.sourceEvaluator.valueAt
            (W.convolutionStar f g) ((n : ℝ)⁻¹)) :=
  PrimePowerPairing.source_prime_power_pairing_formula_source_evaluator
    h.sourcePairing

theorem source_atom_visible_in_pairing_source_test
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h : SourceFinitePrimeAtomData W f g n) :
    h.sourcePairing.model.sourceEvaluation.sourceTest.sourceAtomVisible n :=
  (PrimePowerEvaluation.source_test_visibility_iff_route_visibility
    h.sourcePairing.model.sourceEvaluation).1 h.sourceAtomVisible

theorem source_atom_visible_in_pairing_source_test_of_arithmetic_data
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h : PrimePowerArithmetic.SourceFinitePrimeArithmeticData W f g n) :
    (let atom := source_atom_data_of_arithmetic_data h;
      atom.sourcePairing.model.sourceEvaluation.sourceTest.sourceAtomVisible n) :=
  PrimePowerArithmetic.source_atom_visible_in_pairing_source_test h

theorem source_finite_prime_term_read_off
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h : SourceFinitePrimeAtomData W f g n) :
    W.finitePrimeTerm n (W.convolutionStar f g) =
      ArithmeticFunction.vonMangoldt n * h.sourcePrimePowerPairing :=
  h.termReadOff

theorem finite_prime_term_normalization_of_atom_data
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h : SourceFinitePrimeAtomData W f g n) :
    W.finitePrimeTerm n (W.convolutionStar f g) =
      W.vonMangoldtWeight n * W.primePowerPairing n f g :=
  (source_prime_power_term_of_atom_data h).normalized

theorem source_prime_power_term_of_atom_data_normalized
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h : SourceFinitePrimeAtomData W f g n) :
    (source_prime_power_term_of_atom_data h).normalized =
      finite_prime_term_normalization_of_atom_data h :=
  rfl

theorem finite_prime_term_formula_of_source_arithmetic_data
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h : PrimePowerArithmetic.SourceFinitePrimeArithmeticData W f g n) :
    W.finitePrimeTerm n (W.convolutionStar f g) =
      PrimePowerArithmetic.SourceFinitePrimeEvaluatorAtom W f g n h :=
  PrimePowerArithmetic.source_finite_prime_term_formula_source_evaluator h

structure SourcePrimePowerTermNormalization
    (W : WeilFormSymbols) (f g : TestFunction) where
  atIndex : ∀ n : ℕ, SourcePrimePowerTermAtIndex W f g n

structure SourceFinitePrimeAtomNormalization
    (W : WeilFormSymbols) (f g : TestFunction) where
  atIndex : ∀ n : ℕ, SourceFinitePrimeAtomData W f g n

def source_terms_of_atom_normalization
    {W : WeilFormSymbols} {f g : TestFunction}
    (h : SourceFinitePrimeAtomNormalization W f g) :
    SourcePrimePowerTermNormalization W f g where
  atIndex := fun n => source_prime_power_term_of_atom_data (h.atIndex n)

theorem source_terms_of_atom_normalization_at_index
    {W : WeilFormSymbols} {f g : TestFunction}
    (h : SourceFinitePrimeAtomNormalization W f g) (n : ℕ) :
    (source_terms_of_atom_normalization h).atIndex n =
      source_prime_power_term_of_atom_data (h.atIndex n) :=
  rfl

theorem source_terms_of_atom_normalization_index
    {W : WeilFormSymbols} {f g : TestFunction}
    (h : SourceFinitePrimeAtomNormalization W f g) (n : ℕ) :
    ((source_terms_of_atom_normalization h).atIndex n).sourcePrimePowerIndex =
      (h.atIndex n).sourcePrimePowerIndex :=
  rfl

theorem source_terms_of_atom_normalization_visible
    {W : WeilFormSymbols} {f g : TestFunction}
    (h : SourceFinitePrimeAtomNormalization W f g) (n : ℕ) :
    ((source_terms_of_atom_normalization h).atIndex n).sourceAtomVisible =
      (h.atIndex n).sourceAtomVisible :=
  rfl

theorem source_terms_of_atom_normalization_normalized
    {W : WeilFormSymbols} {f g : TestFunction}
    (h : SourceFinitePrimeAtomNormalization W f g) (n : ℕ) :
    W.finitePrimeTerm n (W.convolutionStar f g) =
      W.vonMangoldtWeight n * W.primePowerPairing n f g :=
  ((source_terms_of_atom_normalization h).atIndex n).normalized

theorem source_terms_of_atom_normalization_prime_power_index
    {W : WeilFormSymbols} {f g : TestFunction}
    (h : SourceFinitePrimeAtomNormalization W f g) (n : ℕ) :
    IsPrimePow n :=
  source_prime_power_index_of_term_at_index
    ((source_terms_of_atom_normalization h).atIndex n)

theorem source_terms_of_atom_normalization_one_lt
    {W : WeilFormSymbols} {f g : TestFunction}
    (h : SourceFinitePrimeAtomNormalization W f g) (n : ℕ) :
    1 < n :=
  source_prime_power_index_one_lt_of_term_at_index
    ((source_terms_of_atom_normalization h).atIndex n)

noncomputable def source_atoms_of_arithmetic_normalization
    {W : WeilFormSymbols} {f g : TestFunction}
    (h : PrimePowerArithmetic.SourceFinitePrimeArithmeticNormalization W f g) :
    SourceFinitePrimeAtomNormalization W f g where
  atIndex := fun n => source_atom_data_of_arithmetic_data (h.atIndex n)

theorem source_atoms_of_arithmetic_normalization_at_index
    {W : WeilFormSymbols} {f g : TestFunction}
    (h : PrimePowerArithmetic.SourceFinitePrimeArithmeticNormalization W f g)
    (n : ℕ) :
    (source_atoms_of_arithmetic_normalization h).atIndex n =
      source_atom_data_of_arithmetic_data (h.atIndex n) :=
  rfl

theorem source_atoms_of_arithmetic_normalization_index
    {W : WeilFormSymbols} {f g : TestFunction}
    (h : PrimePowerArithmetic.SourceFinitePrimeArithmeticNormalization W f g)
    (n : ℕ) :
    ((source_atoms_of_arithmetic_normalization h).atIndex n).sourcePrimePowerIndex =
      (h.atIndex n).sourcePrimePowerIndex :=
  rfl

theorem source_atoms_of_arithmetic_normalization_visible
    {W : WeilFormSymbols} {f g : TestFunction}
    (h : PrimePowerArithmetic.SourceFinitePrimeArithmeticNormalization W f g)
    (n : ℕ) :
    ((source_atoms_of_arithmetic_normalization h).atIndex n).sourceAtomVisible =
      (h.atIndex n).sourceAtomVisible :=
  rfl

theorem source_atoms_of_arithmetic_normalization_pairing_data
    {W : WeilFormSymbols} {f g : TestFunction}
    (h : PrimePowerArithmetic.SourceFinitePrimeArithmeticNormalization W f g)
    (n : ℕ) :
    ((source_atoms_of_arithmetic_normalization h).atIndex n).sourcePairing =
      (h.atIndex n).sourcePairing :=
  rfl

theorem source_atoms_of_arithmetic_normalization_pairing_value
    {W : WeilFormSymbols} {f g : TestFunction}
    (h : PrimePowerArithmetic.SourceFinitePrimeArithmeticNormalization W f g)
    (n : ℕ) :
    ((source_atoms_of_arithmetic_normalization h).atIndex n).sourcePrimePowerPairing =
      (h.atIndex n).sourcePrimePowerPairing :=
  rfl

theorem source_atoms_of_arithmetic_normalization_weight_read_off
    {W : WeilFormSymbols} {f g : TestFunction}
    (h : PrimePowerArithmetic.SourceFinitePrimeArithmeticNormalization W f g)
    (n : ℕ) :
    W.vonMangoldtWeight n = ArithmeticFunction.vonMangoldt n :=
  ((source_atoms_of_arithmetic_normalization h).atIndex n).weightReadOff

theorem source_atoms_of_arithmetic_normalization_pairing_read_off
    {W : WeilFormSymbols} {f g : TestFunction}
    (h : PrimePowerArithmetic.SourceFinitePrimeArithmeticNormalization W f g)
    (n : ℕ) :
    W.primePowerPairing n f g =
      ((source_atoms_of_arithmetic_normalization h).atIndex n).sourcePrimePowerPairing :=
  ((source_atoms_of_arithmetic_normalization h).atIndex n).pairingReadOff

theorem source_atoms_of_arithmetic_normalization_term_read_off
    {W : WeilFormSymbols} {f g : TestFunction}
    (h : PrimePowerArithmetic.SourceFinitePrimeArithmeticNormalization W f g)
    (n : ℕ) :
    W.finitePrimeTerm n (W.convolutionStar f g) =
      ArithmeticFunction.vonMangoldt n *
        ((source_atoms_of_arithmetic_normalization h).atIndex n).sourcePrimePowerPairing :=
  ((source_atoms_of_arithmetic_normalization h).atIndex n).termReadOff

theorem source_atoms_of_arithmetic_normalization_pairing_eq_model_pairing
    {W : WeilFormSymbols} {f g : TestFunction}
    (h : PrimePowerArithmetic.SourceFinitePrimeArithmeticNormalization W f g)
    (n : ℕ) :
    ((source_atoms_of_arithmetic_normalization h).atIndex n).sourcePrimePowerPairing =
      (h.atIndex n).sourcePairing.model.sourceTPairing :=
  ((source_atoms_of_arithmetic_normalization h).atIndex n).sourcePrimePowerPairing_eq_sourcePairing

theorem source_atoms_of_arithmetic_normalization_prime_power_index
    {W : WeilFormSymbols} {f g : TestFunction}
    (h : PrimePowerArithmetic.SourceFinitePrimeArithmeticNormalization W f g)
    (n : ℕ) :
    IsPrimePow n :=
  source_prime_power_index_of_atom_data
    ((source_atoms_of_arithmetic_normalization h).atIndex n)

theorem source_atoms_of_arithmetic_normalization_one_lt
    {W : WeilFormSymbols} {f g : TestFunction}
    (h : PrimePowerArithmetic.SourceFinitePrimeArithmeticNormalization W f g)
    (n : ℕ) :
    1 < n :=
  source_prime_power_index_one_lt_of_atom_data
    ((source_atoms_of_arithmetic_normalization h).atIndex n)

theorem source_atoms_of_arithmetic_normalization_term_normalized
    {W : WeilFormSymbols} {f g : TestFunction}
    (h : PrimePowerArithmetic.SourceFinitePrimeArithmeticNormalization W f g)
    (n : ℕ) :
    W.finitePrimeTerm n (W.convolutionStar f g) =
      W.vonMangoldtWeight n * W.primePowerPairing n f g :=
  finite_prime_term_normalization_of_atom_data
    ((source_atoms_of_arithmetic_normalization h).atIndex n)

theorem source_terms_of_arithmetic_normalization_at_index
    {W : WeilFormSymbols} {f g : TestFunction}
    (h : PrimePowerArithmetic.SourceFinitePrimeArithmeticNormalization W f g)
    (n : ℕ) :
    (source_terms_of_atom_normalization
        (source_atoms_of_arithmetic_normalization h)).atIndex n =
      source_prime_power_term_of_atom_data
        (source_atom_data_of_arithmetic_data (h.atIndex n)) :=
  rfl

theorem source_terms_of_arithmetic_normalization_normalized
    {W : WeilFormSymbols} {f g : TestFunction}
    (h : PrimePowerArithmetic.SourceFinitePrimeArithmeticNormalization W f g)
    (n : ℕ) :
    W.finitePrimeTerm n (W.convolutionStar f g) =
      W.vonMangoldtWeight n * W.primePowerPairing n f g :=
  ((source_terms_of_atom_normalization
      (source_atoms_of_arithmetic_normalization h)).atIndex n).normalized

theorem finite_prime_term_normalization_of_source_arithmetic
    {W : WeilFormSymbols} {f g : TestFunction}
    (h : PrimePowerArithmetic.SourceFinitePrimeArithmeticNormalization W f g) :
    WeilFormSymbols.FinitePrimeTermNormalizationStatement W f g :=
  by
    intro n
    exact finite_prime_term_normalization_of_atom_data
      ((source_atoms_of_arithmetic_normalization h).atIndex n)

theorem finite_prime_term_normalization_of_source_atoms
    {W : WeilFormSymbols} {f g : TestFunction}
    (h : SourceFinitePrimeAtomNormalization W f g) :
    WeilFormSymbols.FinitePrimeTermNormalizationStatement W f g := by
  intro n
  exact finite_prime_term_normalization_of_atom_data (h.atIndex n)

theorem finite_prime_term_normalization_of_source_terms
    {W : WeilFormSymbols} {f g : TestFunction}
    (h : SourcePrimePowerTermNormalization W f g) :
    WeilFormSymbols.FinitePrimeTermNormalizationStatement W f g := by
  intro n
  exact (h.atIndex n).normalized

end PrimePowerTerm
end CCM25Concrete
end Source
end ConnesWeilRH
