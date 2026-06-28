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
  sourcePrimePowerIndex : Prop
  sourceAtomVisible :
    W.finitePrimeAtomVisible n (W.convolutionStar f g)
  sourceVonMangoldtWeight : ℝ
  sourcePrimePowerPairing : ℝ
  weightReadOff :
    W.vonMangoldtWeight n = sourceVonMangoldtWeight
  pairingReadOff :
    W.primePowerPairing n f g = sourcePrimePowerPairing
  termReadOff :
    W.finitePrimeTerm n (W.convolutionStar f g) =
      sourceVonMangoldtWeight * sourcePrimePowerPairing

structure SourcePrimePowerTermAtIndex
    (W : WeilFormSymbols) (f g : TestFunction) (n : ℕ) where
  sourcePrimePowerIndex : Prop
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
    PrimePowerArithmetic.SourcePrimePowerIndex n
  sourceAtomVisible := h.sourceAtomVisible
  sourceVonMangoldtWeight :=
    PrimePowerArithmetic.SourceVonMangoldtWeight n
  sourcePrimePowerPairing := h.sourcePrimePowerPairing
  weightReadOff := h.weightReadOff
  pairingReadOff := h.pairingReadOff
  termReadOff := h.termReadOff

theorem source_weight_read_off
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h : SourceFinitePrimeAtomData W f g n) :
    W.vonMangoldtWeight n = h.sourceVonMangoldtWeight :=
  h.weightReadOff

theorem source_pairing_read_off
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h : SourceFinitePrimeAtomData W f g n) :
    W.primePowerPairing n f g = h.sourcePrimePowerPairing :=
  h.pairingReadOff

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
