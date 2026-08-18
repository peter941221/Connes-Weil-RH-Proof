import ConnesWeilRH.Dev.C1HealthyYoshidaUnscaledOrbit

/-!
# C1HealthyYoshidaSpectralPrefix - finite spectral-prefix sign ledger

This module sums the exact orbit sign information for one selected Yoshida
owner over an arbitrary finite source-zero prefix.  It deliberately requires
the caller to prove which prefix points are controlled; the later closed-ball
geometry must not be hidden behind a support-width heuristic.
-/

namespace ConnesWeilRH
namespace Source
namespace C1HealthyYoshidaSpectralPrefix

open CC20YoshidaConvolution
open CC20YoshidaConvolution.CompactLogTest
open CC20YoshidaNearZeros
open CCM25Concrete.CompactLogConvolution
open CCM25Concrete.UnscaledYoshidaSelectedOwner
open C1HealthyYoshidaUnscaledOrbit
open scoped BigOperators

/-- A finite source-zero prefix has real spectral sum at most the negative
analytic multiplicity of the selected off-line anchor when every non-orbit
point in that prefix is killed by the same selected square. -/
theorem finiteSpectralPrefix_re_le_neg_xiMultiplicity_of_orbit_control
    (base correction : CompactLogTest) (n : Nat)
    (rho : sourceNontrivialZeroSet) (hoff : rho.1.re ≠ 1 / 2)
    (htargets :
      ∀ w : FiniteMellinNode (sourceFunctionalEquationOrbit rho.1),
        laplaceAt ((convolutionIterate base n).convolution correction) w.1 =
          negativeSourceOrbitValue rho.1 w)
    (S : Finset sourceNontrivialZeroSet) (hrho : rho ∈ S)
    (houtside : ∀ z : sourceNontrivialZeroSet, z ∈ S →
      z.1 ∉ sourceFunctionalEquationOrbit rho.1 →
        laplaceAt (selectedOwner base correction n).convolutionSquare
          (z.1 - 1 / 2) = 0) :
    (∑ z ∈ S,
      C1SpectralWeil.spectralTerm
        (selectedOwner base correction n).convolutionSquare z).re ≤
      -(C1SpectralWeil.xiMultiplicity rho : Real) := by
  classical
  have hanchor :=
    spectralTerm_selectedOwner_eq_neg_xiMultiplicity_of_raw_hermitian_values
      base correction n rho
      (by
        calc
          laplaceAt ((convolutionIterate base n).convolution correction) rho.1 =
              negativeSourceOrbitValue rho.1
                ⟨rho.1, mem_sourceFunctionalEquationOrbit_rho rho.1⟩ :=
            htargets ⟨rho.1, mem_sourceFunctionalEquationOrbit_rho rho.1⟩
          _ = 1 := negativeSourceOrbitValue_rho rho.1)
      (by
        calc
          laplaceAt ((convolutionIterate base n).convolution correction)
              (1 - star rho.1) = negativeSourceOrbitValue rho.1
                ⟨1 - star rho.1,
                  mem_sourceFunctionalEquationOrbit_companion rho.1⟩ :=
            htargets ⟨1 - star rho.1,
              mem_sourceFunctionalEquationOrbit_companion rho.1⟩
          _ = -1 := negativeSourceOrbitValue_companion rho.1 hoff)
  have hother (z : sourceNontrivialZeroSet) (hz : z ∈ S.erase rho) :
      (C1SpectralWeil.spectralTerm
        (selectedOwner base correction n).convolutionSquare z).re ≤ 0 := by
    by_cases horbit : z.1 ∈ sourceFunctionalEquationOrbit rho.1
    · rcases spectralTerm_selectedOwner_eq_zero_or_neg_xiMultiplicity_of_mem_orbit
        base correction n rho.1 hoff htargets z horbit with hzero | hneg
      · rw [hzero]
        norm_num
      · rw [hneg]
        simpa using neg_nonpos.mpr
          (Nat.cast_nonneg (C1SpectralWeil.xiMultiplicity z))
    · have hzero := houtside z (Finset.mem_of_mem_erase hz) horbit
      unfold C1SpectralWeil.spectralTerm C1SpectralWeil.centeredXiCoordinate
      rw [hzero]
      norm_num
  have hrest :
      ∑ z ∈ S.erase rho,
        (C1SpectralWeil.spectralTerm
          (selectedOwner base correction n).convolutionSquare z).re ≤ 0 := by
    exact Finset.sum_nonpos fun z hz => hother z hz
  have hsplit := Finset.sum_erase_add
    (s := S)
    (f := fun z : sourceNontrivialZeroSet =>
      C1SpectralWeil.spectralTerm
        (selectedOwner base correction n).convolutionSquare z)
    (a := rho) hrho
  have hrestRe :
      (∑ z ∈ S.erase rho,
        C1SpectralWeil.spectralTerm
          (selectedOwner base correction n).convolutionSquare z).re =
        ∑ z ∈ S.erase rho,
          (C1SpectralWeil.spectralTerm
            (selectedOwner base correction n).convolutionSquare z).re := by
    simp
  calc
    (∑ z ∈ S,
      C1SpectralWeil.spectralTerm
        (selectedOwner base correction n).convolutionSquare z).re =
        ((∑ z ∈ S.erase rho,
          C1SpectralWeil.spectralTerm
            (selectedOwner base correction n).convolutionSquare z) +
          C1SpectralWeil.spectralTerm
            (selectedOwner base correction n).convolutionSquare rho).re := by
          rw [hsplit]
    _ = (∑ z ∈ S.erase rho,
          (C1SpectralWeil.spectralTerm
            (selectedOwner base correction n).convolutionSquare z).re) -
          (C1SpectralWeil.xiMultiplicity rho : Real) := by
          rw [Complex.add_re, hrestRe, hanchor]
          norm_num
          ring
    _ ≤ -(C1SpectralWeil.xiMultiplicity rho : Real) := by linarith

end C1HealthyYoshidaSpectralPrefix
end Source
end ConnesWeilRH
