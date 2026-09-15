/-
Copyright (c) 2026 Connes-WeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1G8P1MetricChannels
import ConnesWeilRH.Source.CC20Concrete.HilbertSchmidtIdeal
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSBandTrace
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSTransportBounds

/-!
# Finite boundary outputs reduce the G8 boundary root energy

The visible-boundary coframe is a finite Schur--polar sum, indexed by the
visible primes. This file proves that square-summability of the selected-root
image of each actual boundary output implies the aggregate G8 boundary
energy. It leaves those per-output analytic estimates explicit.
-/

namespace ConnesWeilRH
namespace Dev

open Source.CC20Concrete
open Source.CC20Concrete.PositiveTrace
open Source.CCM25Concrete
open Source.CCM25Concrete.CCM24FiniteSProjectionTrace
open Source.CCM25Concrete.CCM24FiniteSGramResponse
open Source.CCM25Concrete.CCM24FiniteSBandTrace
open Source.CCM25Concrete.CCM24FiniteSSchurPolarTelescoping
open Source.CCM25Concrete.CCM24FiniteSTransportBounds
open Source.C1G8P1MetricChannels
open scoped InnerProduct InnerProductSpace

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-- A finite sum of operators is Hilbert--Schmidt on a named basis whenever
each summand is. -/
theorem summable_normSq_list_sum_of_each
    {ι H G : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    (basis : HilbertBasis ι ℂ H) (maps : List (H →L[ℂ] G))
    (hmap : ∀ map ∈ maps, Summable fun i => ‖map (basis i)‖ ^ 2) :
    Summable fun i => ‖maps.sum (basis i)‖ ^ 2 := by
  induction maps with
  | nil => simp
  | cons head tail ih =>
      have hhead : Summable fun i => ‖head (basis i)‖ ^ 2 :=
        hmap head (by simp)
      have htail : ∀ map ∈ tail,
          Summable fun i => ‖map (basis i)‖ ^ 2 := by
        intro map hmem
        exact hmap map (by simp [hmem])
      have htailSum : Summable fun i => ‖tail.sum (basis i)‖ ^ 2 :=
        ih htail
      have hadd := PositiveTrace.summable_normSq_add basis head tail.sum
        hhead htailSum
      simpa only [List.sum_cons, ContinuousLinearMap.add_apply] using hadd

/-- The selected-root image of a finite sum of boundary outputs is the sum
of their selected-root images. -/
theorem rootConvolution_comp_list_sum_eq_list_sum_comp
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (root : finiteSCarrier →L[ℂ] finiteSCarrier)
    (maps : List (H →L[ℂ] finiteSCarrier)) :
    root ∘L maps.sum =
      (maps.map fun output => root ∘L output).sum := by
  induction maps with
  | nil =>
      apply ContinuousLinearMap.ext
      intro x
      simp
  | cons head tail ih =>
      apply ContinuousLinearMap.ext
      intro x
      change root (head x + tail.sum x) =
        root (head x) + (List.map (fun output => root ∘L output) tail).sum x
      calc
        root (head x + tail.sum x) = root (head x) + root (tail.sum x) :=
          map_add root _ _
        _ = root (head x) +
            (List.map (fun output => root ∘L output) tail).sum x := by
          congr 1
          have hpoint := congrArg (fun T => T x) ih
          simpa only [ContinuousLinearMap.comp_apply] using hpoint

/-- If each actual visible-prime boundary output has square-summable columns
after the same selected root convolution, then the aggregate G8 boundary
coframe satisfies the exact `hBoundary` energy condition. -/
theorem g8MetricVisibleBoundary_root_energy_summable_of_each_output
    {ρ : Type*}
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda))
    (houtput : ∀ output ∈ finiteEulerMetricCoframeBoundaryMaps lambda family,
      Summable fun i : ρ =>
        ‖(rootConvolution owner ∘L output) (sourceBasis i)‖ ^ 2) :
    Summable fun i : ρ =>
      ‖(rootConvolution owner ∘L
          g8MetricVisibleBoundaryCoframe lambda family) (sourceBasis i)‖ ^ 2 := by
  let outputs := finiteEulerMetricCoframeBoundaryMaps lambda family
  let rootedOutputs := outputs.map fun output => rootConvolution owner ∘L output
  have hrooted :
      rootConvolution owner ∘L g8MetricVisibleBoundaryCoframe lambda family =
        (finiteEulerUpperFactor family.visiblePrimes : ℂ) • rootedOutputs.sum := by
    apply ContinuousLinearMap.ext
    intro x
    rw [g8MetricVisibleBoundaryCoframe]
    change rootConvolution owner
        ((finiteEulerUpperFactor family.visiblePrimes : ℂ) • outputs.sum x) = _
    rw [map_smul, ← rootConvolution_comp_list_sum_eq_list_sum_comp]
    rfl
  have hrootedOutputs : Summable fun i : ρ => ‖rootedOutputs.sum (sourceBasis i)‖ ^ 2 := by
    apply summable_normSq_list_sum_of_each sourceBasis rootedOutputs
    intro output hmem
    rcases List.mem_map.mp hmem with ⟨boundary, hboundary, rfl⟩
    exact houtput boundary hboundary
  have hscaled : Summable fun i : ρ =>
      ‖((finiteEulerUpperFactor family.visiblePrimes : ℂ) • rootedOutputs.sum)
          (sourceBasis i)‖ ^ 2 := by
    apply (hrootedOutputs.mul_left
      (‖(finiteEulerUpperFactor family.visiblePrimes : ℂ)‖ ^ 2)).congr
    intro i
    rw [ContinuousLinearMap.smul_apply, norm_smul]
    ring
  simpa only [hrooted] using hscaled

end Dev
end ConnesWeilRH
