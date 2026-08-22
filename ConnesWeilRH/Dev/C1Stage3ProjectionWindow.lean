/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1PositiveTraceWindowProducer
import ConnesWeilRH.Dev.C1PositiveTraceCutoffAdapter
import ConnesWeilRH.Dev.C1Stage3ProjectionKernel
import ConnesWeilRH.Source.CC20Concrete.HilbertSchmidtIdeal

/-!
# C1 Stage-3 projection kernel on a finite-window owner

This module wires the already-proved finite-window Hilbert--Schmidt factor to
the active Stage-3 positive kernel.  For a bounded factor `C` and a positive
kernel `K`, the relevant operator is

```text
  C† ∘ K ∘ C
```

The two legs are kept as one `BasisHilbertSchmidtPairData` owner: the left leg
is `C`, while the right leg is `K ∘ C`.  This is the correct trace-class
representation of the sandwich and does not assume that `K` is a projection
or that a square root has already been constructed.  Positivity comes from
`ContinuousLinearMap.IsPositive.adjoint_conj`; trace-class legality comes from
the Hilbert--Schmidt ideal under bounded postcomposition.

The concrete instance below uses `fullBoundaryPositiveOperator`, whose input
and output are both the fixed carrier `cc20GlobalLogCrossingL2`.  It therefore
provides the missing finite-window-to-kernel wiring for
`stage3ProjectionKernel`, while deliberately making no claim about the
same-owner `qw` readback or a cutoff remainder limit.
-/

namespace ConnesWeilRH
namespace Source
namespace Dev
namespace C1Stage3ProjectionWindow

open CC20Concrete
open CC20Concrete.CompactRootHalfLinePair
open CC20Concrete.PositiveTrace
open C1PositiveTraceCutoffAdapter
open C1PositiveTraceWindowProducer
open C1Stage3ProjectionKernel
open CCM25Concrete.CompactLogConvolution
open MeasureTheory

noncomputable section

abbrev projectionCarrier := cc20GlobalLogCrossingL2

/-! ### Generic bounded-factor wiring -/

/-- A Hilbert--Schmidt factor `C` with a bounded kernel `K` gives one
same-owner pair for the sandwich `C† K C`.  The right leg remains
Hilbert--Schmidt by bounded postcomposition. -/
noncomputable def kernelSandwichPairData
    {ν : Type*}
    (basis : HilbertBasis ν ℂ projectionCarrier)
    (C K : projectionCarrier →L[ℂ] projectionCarrier)
    (hC : Summable fun i => ‖C (basis i)‖ ^ 2) :
    BasisHilbertSchmidtPairData (G := projectionCarrier) basis where
  left := C
  right := K ∘L C
  left_summable_normSq := hC
  right_summable_normSq :=
    PositiveTrace.summable_normSq_postcomp basis C K hC

theorem kernelSandwichPairData_traceProduct_eq
    {ν : Type*}
    (basis : HilbertBasis ν ℂ projectionCarrier)
    (C K : projectionCarrier →L[ℂ] projectionCarrier)
    (hC : Summable fun i => ‖C (basis i)‖ ^ 2) :
    (kernelSandwichPairData basis C K hC).traceProduct =
      C.adjoint ∘L K ∘L C := by
  simp only [kernelSandwichPairData,
    BasisHilbertSchmidtPairData.traceProduct]

theorem kernelSandwichPairData_traceProduct_isTraceClassAlong
    {ν : Type*}
    (basis : HilbertBasis ν ℂ projectionCarrier)
    (C K : projectionCarrier →L[ℂ] projectionCarrier)
    (hC : Summable fun i => ‖C (basis i)‖ ^ 2) :
    IsTraceClassAlong basis
      (kernelSandwichPairData basis C K hC).traceProduct := by
  exact BasisHilbertSchmidtPairData.traceProduct_isTraceClassAlong _

theorem kernelSandwichPairData_traceProduct_isPositive
    {ν : Type*}
    (basis : HilbertBasis ν ℂ projectionCarrier)
    (C K : projectionCarrier →L[ℂ] projectionCarrier)
    (hC : Summable fun i => ‖C (basis i)‖ ^ 2)
    (hK : K.IsPositive) :
    (kernelSandwichPairData basis C K hC).traceProduct.IsPositive := by
  rw [kernelSandwichPairData_traceProduct_eq basis C K hC]
  exact ContinuousLinearMap.IsPositive.adjoint_conj hK C

/-- A positive trace-class diagonal has nonnegative real trace.  Keeping this
lemma generic makes the order argument explicit instead of relying on the
self-pair special case (`K` need not be an idempotent projection). -/
theorem ordinaryTraceAlong_re_nonnegative_of_positive
    {ν : Type*}
    (basis : HilbertBasis ν ℂ projectionCarrier)
    (T : projectionCarrier →L[ℂ] projectionCarrier)
    (hT : T.IsPositive)
    (htrace : IsTraceClassAlong basis T) :
    0 ≤ (ordinaryTraceAlong basis T).re := by
  rw [ordinaryTraceAlong]
  rw [Complex.re_tsum htrace]
  exact tsum_nonneg (fun i => hT.re_inner_nonneg_right (basis i))

/-! ### Concrete finite-window instance -/

/-- The finite-window factor with the active Stage-3 kernel inserted between
its two legs.  `fullBasis` and `outputBasis` are local Hilbert-basis witnesses
used only to establish the Hilbert--Schmidt column sum; the trace itself stays
on the caller-owned `globalBasis`. -/
noncomputable def fullBoundaryProjectionPairData
    (g : CompactLogTest) (a c : ℝ)
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime)
    {iota kappa ν : Type*}
    (fullBasis : HilbertBasis iota ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryFullInputInterval a c))))
    (outputBasis : HilbertBasis kappa ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (globalBasis : HilbertBasis ν ℂ projectionCarrier) :
    BasisHilbertSchmidtPairData (G := projectionCarrier) globalBasis :=
  kernelSandwichPairData globalBasis
    (fullBoundaryPositiveOperator g a c)
    (stage3ProjectionKernel lambda S)
    (fullBoundaryPositiveOperator_basis_normSq_summable
      g a c fullBasis outputBasis globalBasis)

theorem fullBoundaryProjectionPairData_traceProduct_eq
    (g : CompactLogTest) (a c : ℝ)
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime)
    {iota kappa ν : Type*}
    (fullBasis : HilbertBasis iota ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryFullInputInterval a c))))
    (outputBasis : HilbertBasis kappa ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (globalBasis : HilbertBasis ν ℂ projectionCarrier) :
    (fullBoundaryProjectionPairData g a c lambda S fullBasis outputBasis
        globalBasis).traceProduct =
    (fullBoundaryPositiveOperator g a c).adjoint ∘L
        stage3ProjectionKernel lambda S ∘L
          fullBoundaryPositiveOperator g a c := by
  simpa only [fullBoundaryProjectionPairData] using
    (kernelSandwichPairData_traceProduct_eq
      (basis := globalBasis)
      (C := fullBoundaryPositiveOperator g a c)
      (K := stage3ProjectionKernel lambda S)
      (hC := fullBoundaryPositiveOperator_basis_normSq_summable
        g a c fullBasis outputBasis globalBasis))

theorem fullBoundaryProjectionPairData_traceProduct_isTraceClassAlong
    (g : CompactLogTest) (a c : ℝ)
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime)
    {iota kappa ν : Type*}
    (fullBasis : HilbertBasis iota ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryFullInputInterval a c))))
    (outputBasis : HilbertBasis kappa ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (globalBasis : HilbertBasis ν ℂ projectionCarrier) :
    IsTraceClassAlong globalBasis
      (fullBoundaryProjectionPairData g a c lambda S fullBasis outputBasis
        globalBasis).traceProduct := by
  simpa only [fullBoundaryProjectionPairData] using
    (kernelSandwichPairData_traceProduct_isTraceClassAlong
      (basis := globalBasis)
      (C := fullBoundaryPositiveOperator g a c)
      (K := stage3ProjectionKernel lambda S)
      (hC := fullBoundaryPositiveOperator_basis_normSq_summable
        g a c fullBasis outputBasis globalBasis))

theorem fullBoundaryProjectionPairData_traceProduct_isPositive
    (g : CompactLogTest) (a c : ℝ)
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime)
    {iota kappa ν : Type*}
    (fullBasis : HilbertBasis iota ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryFullInputInterval a c))))
    (outputBasis : HilbertBasis kappa ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (globalBasis : HilbertBasis ν ℂ projectionCarrier) :
    (fullBoundaryProjectionPairData g a c lambda S fullBasis outputBasis
        globalBasis).traceProduct.IsPositive := by
  simpa only [fullBoundaryProjectionPairData] using
    (kernelSandwichPairData_traceProduct_isPositive
      (basis := globalBasis)
      (C := fullBoundaryPositiveOperator g a c)
      (K := stage3ProjectionKernel lambda S)
      (hC := fullBoundaryPositiveOperator_basis_normSq_summable
        g a c fullBasis outputBasis globalBasis)
      (stage3ProjectionKernel_isPositive lambda S))

theorem fullBoundaryProjectionPairData_trace_re_nonnegative
    (g : CompactLogTest) (a c : ℝ)
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime)
    {iota kappa ν : Type*}
    (fullBasis : HilbertBasis iota ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryFullInputInterval a c))))
    (outputBasis : HilbertBasis kappa ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (globalBasis : HilbertBasis ν ℂ projectionCarrier) :
    0 ≤ (ordinaryTraceAlong globalBasis
      (fullBoundaryProjectionPairData g a c lambda S fullBasis outputBasis
        globalBasis).traceProduct).re := by
  exact ordinaryTraceAlong_re_nonnegative_of_positive
    globalBasis _
    (fullBoundaryProjectionPairData_traceProduct_isPositive
      g a c lambda S fullBasis outputBasis globalBasis)
    (fullBoundaryProjectionPairData_traceProduct_isTraceClassAlong
      g a c lambda S fullBasis outputBasis globalBasis)

/-! ### The named expanding cutoff sequence -/

/-- The concrete `n`th cutoff owner.  This is the same fixed-carrier sequence
used by the existing cutoff adapter, with the active positive kernel inserted
between the two finite-window legs. -/
noncomputable def cutoffProjectionPairData
    {ν : Type*}
    (g : CompactLogTest) (lambda : CCM24SoninScale)
    (S : List CCM24VisiblePrime)
    (globalBasis : HilbertBasis ν ℂ projectionCarrier) (n : Nat) :
    BasisHilbertSchmidtPairData (G := projectionCarrier) globalBasis :=
  fullBoundaryProjectionPairData g
    (cutoffLower g n) (cutoffUpper g n) lambda S
    (cutoffFullBasis g n) (cutoffOutputBasis g n) globalBasis

theorem cutoffProjectionPairData_traceProduct_eq
    {ν : Type*}
    (g : CompactLogTest) (lambda : CCM24SoninScale)
    (S : List CCM24VisiblePrime)
    (globalBasis : HilbertBasis ν ℂ projectionCarrier) (n : Nat) :
    (cutoffProjectionPairData g lambda S globalBasis n).traceProduct =
      (fullBoundaryPositiveOperator (g := g)
        (cutoffLower g n) (cutoffUpper g n)).adjoint ∘L
          stage3ProjectionKernel lambda S ∘L
            fullBoundaryPositiveOperator (g := g)
              (cutoffLower g n) (cutoffUpper g n) := by
  exact fullBoundaryProjectionPairData_traceProduct_eq
    g (cutoffLower g n) (cutoffUpper g n) lambda S
    (cutoffFullBasis g n) (cutoffOutputBasis g n) globalBasis

theorem cutoffProjectionPairData_traceProduct_isTraceClassAlong
    {ν : Type*}
    (g : CompactLogTest) (lambda : CCM24SoninScale)
    (S : List CCM24VisiblePrime)
    (globalBasis : HilbertBasis ν ℂ projectionCarrier) (n : Nat) :
    IsTraceClassAlong globalBasis
      (cutoffProjectionPairData g lambda S globalBasis n).traceProduct := by
  exact fullBoundaryProjectionPairData_traceProduct_isTraceClassAlong
    g (cutoffLower g n) (cutoffUpper g n) lambda S
    (cutoffFullBasis g n) (cutoffOutputBasis g n) globalBasis

theorem cutoffProjectionPairData_traceProduct_isPositive
    {ν : Type*}
    (g : CompactLogTest) (lambda : CCM24SoninScale)
    (S : List CCM24VisiblePrime)
    (globalBasis : HilbertBasis ν ℂ projectionCarrier) (n : Nat) :
    (cutoffProjectionPairData g lambda S globalBasis n).traceProduct.IsPositive := by
  exact fullBoundaryProjectionPairData_traceProduct_isPositive
    g (cutoffLower g n) (cutoffUpper g n) lambda S
    (cutoffFullBasis g n) (cutoffOutputBasis g n) globalBasis

theorem cutoffProjectionPairData_trace_re_nonnegative
    {ν : Type*}
    (g : CompactLogTest) (lambda : CCM24SoninScale)
    (S : List CCM24VisiblePrime)
    (globalBasis : HilbertBasis ν ℂ projectionCarrier) (n : Nat) :
    0 ≤ (ordinaryTraceAlong globalBasis
      (cutoffProjectionPairData g lambda S globalBasis n).traceProduct).re := by
  exact fullBoundaryProjectionPairData_trace_re_nonnegative
    g (cutoffLower g n) (cutoffUpper g n) lambda S
    (cutoffFullBasis g n) (cutoffOutputBasis g n) globalBasis

end
end C1Stage3ProjectionWindow
end Dev
end Source
end ConnesWeilRH
