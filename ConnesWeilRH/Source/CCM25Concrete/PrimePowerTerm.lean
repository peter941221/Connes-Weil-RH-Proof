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
  sourcePrimePowerIndex : PrimePowerArithmetic.SourcePrimePowerIndex n
  sourceAtomVisible :
    W.finitePrimeAtomVisible n (W.convolutionStar f g)
  sourceVonMangoldtWeight : ℝ
  sourcePairing :
    PrimePowerPairing.SourcePrimePowerPairingData W f g n
  sourcePrimePowerPairing : ℝ
  sourcePrimePowerPairing_eq_sourcePairing :
    sourcePrimePowerPairing = sourcePairing.model.sourceTPairing
  weightReadOff :
    W.vonMangoldtWeight n = sourceVonMangoldtWeight
  pairingReadOff :
    W.primePowerPairing n f g = sourcePrimePowerPairing
  termReadOff :
    W.finitePrimeTerm n (W.convolutionStar f g) =
      sourceVonMangoldtWeight * sourcePrimePowerPairing

structure SourcePrimePowerTermAtIndex
    (W : WeilFormSymbols) (f g : TestFunction) (n : ℕ) where
  sourcePrimePowerIndex : PrimePowerArithmetic.SourcePrimePowerIndex n
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

noncomputable def source_atom_data_of_arithmetic_data
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h :
      PrimePowerArithmetic.SourceFinitePrimeArithmeticData W f g n) :
    SourceFinitePrimeAtomData W f g n where
  sourcePrimePowerIndex :=
    h.sourcePrimePowerIndex
  sourceAtomVisible := h.sourceAtomVisible
  sourceVonMangoldtWeight :=
    PrimePowerArithmetic.SourceVonMangoldtWeight n
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

theorem source_weight_read_off
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h : SourceFinitePrimeAtomData W f g n) :
    W.vonMangoldtWeight n = h.sourceVonMangoldtWeight :=
  h.weightReadOff

theorem source_prime_power_index_of_atom_data
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h : SourceFinitePrimeAtomData W f g n) :
    PrimePowerArithmetic.SourcePrimePowerIndex n :=
  h.sourcePrimePowerIndex

theorem source_prime_power_index_one_lt_of_atom_data
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h : SourceFinitePrimeAtomData W f g n) :
    1 < n :=
  PrimePowerArithmetic.source_prime_power_index_one_lt
    (source_prime_power_index_of_atom_data h)

theorem source_prime_power_index_of_term_at_index
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h : SourcePrimePowerTermAtIndex W f g n) :
    PrimePowerArithmetic.SourcePrimePowerIndex n :=
  h.sourcePrimePowerIndex

theorem source_prime_power_index_one_lt_of_term_at_index
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h : SourcePrimePowerTermAtIndex W f g n) :
    1 < n :=
  PrimePowerArithmetic.source_prime_power_index_one_lt
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

theorem source_finite_prime_term_read_off
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h : SourceFinitePrimeAtomData W f g n) :
    W.finitePrimeTerm n (W.convolutionStar f g) =
      h.sourceVonMangoldtWeight * h.sourcePrimePowerPairing :=
  h.termReadOff

theorem finite_prime_term_normalization_of_atom_data
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h : SourceFinitePrimeAtomData W f g n) :
    W.finitePrimeTerm n (W.convolutionStar f g) =
      W.vonMangoldtWeight n * W.primePowerPairing n f g :=
  (source_prime_power_term_of_atom_data h).normalized

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

noncomputable def source_atoms_of_arithmetic_normalization
    {W : WeilFormSymbols} {f g : TestFunction}
    (h : PrimePowerArithmetic.SourceFinitePrimeArithmeticNormalization W f g) :
    SourceFinitePrimeAtomNormalization W f g where
  atIndex := fun n => source_atom_data_of_arithmetic_data (h.atIndex n)

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
