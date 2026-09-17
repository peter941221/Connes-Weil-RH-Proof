# 1577 — the 1576 decision card's option (i) is a phantom: B3's radial OUT leg is already unconditional; and (ii) is capped, because B4's second premise sits inside the stop that (i)'s own record filed

Date: 2026-09-17.

Status: SOURCE AUDIT + TYPED VERDICT. Zero Lean, zero digits, zero rig. This
record discharges the owner decision card filed at the end of
[1576](1576_typed_stop_and_AO_level_repricing.md) §4-§5 for the options it can
decide from committed material, and corrects a wording conflict between that
card and [map 042](../map/042_g8_diagonal_leg_operator_bridge_audit.md).
RH not claimed.

```text
  OWNER DECISION CARD as received (1576 section 5):
    (i)   B3 paper-verify then brick (cheap, closes one diagonal leg)
    (ii)  hradial strip screening (new paper computation)
    (iii) rho5 combined-row face (independent of this wave)
    (iv)  map 011 track W face (the 1417 category-change line)

  VERDICT OF THIS RECORD (evidence in sections 1-3):
    (i)   PHANTOM - already landed unconditionally; do not fund. Closed here.
    (ii)  CAPPED  - buys at most half of B4; its exit hypothesis cannot close
          anything while hgap stays inside the 1576 stop. Deferred, not funded.
    (iii) STRANDED-RISK - valid work, but its value is conditional on (star);
          option held, not exercised.
    (iv)  SELECTED by the owner as this wave; executed in
          [1578](1578_w0_archimedean_symbol_pinned_and_window_class_correction.md).
```

## 1. What 1576 §4.1 asked for, and what the committed file actually contains

1576 §4.1 lists "B3 composite window (support-combinatorial; prereg 1503 §4,
'cheap')" as a survivor, asks for "one cheap pointwise support-propagation
lemma ... and then a Lean brick", and 1576 §5 restates B3 as "upgraded from
'cheap' to 'explicit window in hand'".

Map 042 says something stronger, and the source settles it. The B3 radial OUT
leg is proven for both physical boundary columns with **no analytic premise at
all** - the wide-radial support is discharged internally at the canonical
shift:

```lean
-- ConnesWeilRH/Dev/C1G8R3CompositeBoundaryEnergy.lean:1147-1161
theorem suffixEulerFrameAmbientLossColumn_compositeRadialLeg_sourceBasis_normSq_summable
    (owner : SelectedWeilSquareOwner) (lambda : CCM24SoninScale)
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime)
    (N : sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda)
    {ρ : Type*} (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda)) :
    Summable fun i : ρ =>
      ‖(((ContinuousLinearMap.id ℂ Carrier - radialSupportProjection lambda) ∘L
          rootConvolution owner ∘L
            suffixEulerFrameAmbientLossColumn lambda p S) ∘L N)
        (sourceBasis i)‖ ^ 2 := by
  have hlogp : 0 ≤ Real.log (p : ℝ) := ...
  exact compositeRadialLeg_sourceColumn_normSq_summable owner lambda
    (Real.log p) hlogp (suffixEulerFrameAmbientLossColumn lambda p S) N
    sourceBasis (suffixEulerFrameAmbientLossColumn_wideRadialSupport lambda p S)
```

The hypothesis list is `owner, lambda, p, S, N, sourceBasis` - data only. The
generic reducer `compositeRadialLeg_sourceColumn_normSq_summable` *takes* a
support premise, but this instantiation supplies it from
`..._wideRadialSupport` (`:477-534`), so the conclusion carries no premise. The
matching `boundaryDagger` twin is at `:1182-1200`, and both have
postcomposition-by-arbitrary-bounded-row forms (`:1163-1180` and following).

Checks run against committed material, all pass:

```text
  sorry in C1G8R3CompositeBoundaryEnergy.lean                    : 0
  support premise present in the CONCLUSION of either physical
    column theorem                                             : no
  generality in the suffix S and in bounded pre/post-composition : yes
  any consumer awaiting a composite/Lambda_max window object     : NONE
    (grep for shiftSet / Lambda_max / compositeWindow over
     ConnesWeilRH/ returns no match; the only lambdaMax hits are
     the unrelated C1CC20OperatorGap eigenvalue frames)
  map 042's own words (record 1558 entry)                        : "WO-B is
    therefore reduced to its coupled inner metric/projection channel
    (B4/Hardy side still open)"
  map 042's own words (record 1561 entry)                        : "Both
    physical boundary coordinates now have radial OUT B3; the
    Hardy-conjugated B4 input and the survivor IN/S3 estimate
    remain open"
```

Why the phantom arose, mechanically: 1575 computed the total leftward support
leak of the four-factor ambient chain,

```text
  Lambda(p::S) = log prod_{q in p::S} q
```

and 1576 §4.1 read that ledger as evidence that B3's window had to be widened
to a multi-factor union. But the *landed* B3 columns are one-step objects -
`suffixEulerFrameAmbientLossColumn lambda p S =
(primeEulerAmbientLossFactor p)† ∘L (suffixEulerFrameSchurStep lambda p S).oldFrame`
(`CCM24FiniteSCompletedJuliaAmbientDefectFactorization.lean:229-235`) whose only
support mover is the single adjoint transport at `p`. That is why the shift
`Real.log p` closes them and why no `Lambda_max` is needed. The ledger's real
consumer is the composite chain inside B4, where `M_p` occurs in full.

**Typed verdict.** Option (i) is a phantom brick: it would prove nothing that
`:1147-1200` does not already prove. It is closed here rather than funded.
Re-attribution: 1575's `Lambda(p::S)` belongs to B4's `hradial` strip leg
(`[tau - Lambda, tau)`), which is where 1575 §3.3 already placed it; 1576 §4.1
attaching it to B3 is superseded.

This is the second occurrence of the same failure mode (record 1415: "brick 4 is
a phantom, `gate2ExplicitFormula` already landed"). The generalization is
recorded as law F26 in the project law register: **a decision-card option is a
spend claim,
and the F8 pre-spend sweep applies to it before it reaches the owner, not only
to fresh mathematical cards.**

## 2. Why option (ii) is capped: B4's remaining premises, read from source

The B4 consumer requires **two** square-sums simultaneously:

```lean
-- ConnesWeilRH/Dev/C1G8R3BoundaryOutputFactorizationBridge.lean:509-527
theorem sourceSoninHardySubId_sourceBasis_normSq_summable_of_radial_fourierDefects
    ...
    (hradial : Summable fun i : ρ => ‖(D ∘L
        ((ContinuousLinearMap.id ℂ finiteSCarrier -
          radialSupportProjection lambda) ∘L M) ∘L
        sourceInclusion lambda ∘L N) (sourceBasis i)‖ ^ 2)
    (hgap : Summable fun i : ρ => ‖(D ∘L
        (radialSupportProjection lambda ∘L
          (ContinuousLinearMap.id ℂ finiteSCarrier -
            sourceFourierSupportProjection lambda) ∘L
          radialSupportProjection lambda ∘L M) ∘L
        sourceInclusion lambda ∘L N) (sourceBasis i)‖ ^ 2) :
    Summable fun i : ρ => ‖(D ∘L (radialSupportProjection lambda ∘L
        sourceFourierSupportProjection lambda ∘L radialSupportProjection lambda
        ∘L M - M) ∘L sourceInclusion lambda ∘L N) (sourceBasis i)‖ ^ 2
```

The split is by class, and it is decisive:

```text
   hradial : contains only (id - radialSupportProjection), i.e. the SUPPORT
             side. 1575 confines it to the strip [tau - Lambda, tau). Alive,
             unpriced.
   hgap    : contains sourceFourierSupportProjection, i.e. the FOURIER side.
             This is the 1536 Fourier-gap normal form, whose column 1576
             quotes verbatim inside its own typed stop:
               "the B4 gap column D E H (I-E) H E M J"
             and 1572 established Q = H E H, so hgap and (star) are ONE family.

   hradial closed  +  hgap stopped   ==>   B4 stays OPEN
```

So a successful hradial screening buys one of two premises of a leg whose other
premise has just been declared route-dead, and buys nothing at all for (★)
itself. Under law F15 (price campaigns from exit hypotheses) its exit
hypothesis closes no obligation, so it is **deferred, not funded**: it should be
re-opened only bound to an admitted route for `hgap`, i.e. together with a
map-010 new-lever-class admission for (★).

## 3. What this record does not do

- It proves nothing new in Lean and spends no build; the theorems it cites were
  accepted in the 1555-1561 rounds.
- It does not close WO-B: B4 remains OPEN, and map 042's WO-B status is
  unchanged.
- It does not touch (★), S3, rho4, rho5, the source/ambient transport, R4, or
  RH. Nothing is claimed in either direction about any gate.
- It does not negate 1576's stop; it consumes it (section 2's cap follows from
  the stop's own scope sentence).
- The 1576 §4.1/§5 wording that offered option (i) as a survivor is superseded
  by this record; 1576 is annotated in place rather than rewritten, so the
  pre-registration trail stays intact.
