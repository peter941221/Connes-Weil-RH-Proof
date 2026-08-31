# 1073 - DESIGN RECORD: the D-weighted re-route of the F1' capstone

Date: 2026-08-31. Follows 1067 (GROWTH -> ROUTE B: the UNWEIGHTED
S2-FK-HS contract FAILS for {2,3,5} in the model) and 1068 (OUTCOME A:
every D-weighted quantity O(1) and decreasing over four octaves).  This
record fixes the production route for the F1' capstone premise.  It changes
no Lean object; both candidate corollaries are already committed and
axiom-clean.  RH is not claimed anywhere.

## 0. The judgment being formalized

The F1' capstone premise `targetProlateRemainderDetectorWeightedTraceLegality`
was to be produced from the SINGLE unweighted contract S2-FK-HS
(`targetProlateRemainderFactorSummable`) via the record-1066 corollary.
Record 1067 measured that contract directly in the record-1063 rig and it
FAILS (fk_hs_sq 16.20 -> 34.27 over four octaves, ~xi^0.36, increments
increasing - no saturation bend; source anchor flat).  Record 1068 then
measured the D-WEIGHTED quantities on the same code path and they are O(1)
and monotone DECREASING while their unweighted controls grow +112%.
Consequence: the capstone premise must be produced through the TWO-CONTRACT
active-order corollary instead.  This is ROUTE B made concrete.

## 1. The swap, exactly

```text
  BEFORE (dead production plan, 1066):
    targetProlateRemainderFactorSummable          (S2-FK-HS, MEASURED FALSE)
        |  targetProlateRemainderDetectorWeightedTraceLegality_
        |  of_remainderFactorSummable
        v                                              (SingleContract:124)
    targetProlateRemainderDetectorWeightedTraceLegality

  AFTER (the re-route; all names committed, leaf =
  C1ProlateResponseTraceLegalityUnitScale.lean):
    P1: targetProlateDetectorRightSmoothingFactorSummable    (S1')
        owner family globalBasis                    (leaf:177 def, :374)
    P2: targetProlateDetectorRootCommutatorTraceLegality      (S2)
        owner family globalBasis                    (leaf:234 def, :375)
        |  targetProlateRemainderDetectorWeightedTraceLegality_
        |  of_rightSmoothing_and_rootCommutator     (leaf:370-381)
        v
    targetProlateRemainderDetectorWeightedTraceLegality   (SAME conclusion)
        |  projectionResponse_isTraceClassAlong_at_unit
        v                                              (leaf:565-582)
    IsTraceClassAlong globalBasis (projectionResponse ...)  [capstone]
```

The capstone's conclusion type is UNCHANGED; its `hprolateTarget` premise
merely acquires a different production route.  The Gate-2 readback premise
`hresponse` consumes the same statement, so the swap is
consumer-compatible with zero downstream edits.

## 2. The two producer obligations

```text
  P1 (S1', right-sandwich HS): Summable |F_K oL C (globalBasis i)|^2.
     Measured: 1068 l_hs_sq 0.2086 -> 0.1688 at {2,3,5}, k=1 (O(1), DECREASING).
     Named difficulty (owner transfer): the probes used a Gaussian Schwartz
     stand-in for the convolution root; the producer is owed for the ACTUAL
     selected root, per-owner (1063 principle: any Schwartz beats the
     ~xi^0.4 raw mass).  Route shape: basis-independent by construction -
     1068 find (a) - the leaf's globalBasis is UNIVERSALLY quantified
     (leaf:118-123/:177-182/:234-239), so a named-basis-only estimate cannot
     produce it; the trace-norm / pairData HS-legs path (leaf:243-265/
     :301-320) is the produceable shape.

  P2 (S2, root commutator): trace legality of
     cc20Commutator C K_S = -(four-branch ledger E/Q/R), consumed via
     targetProlateDetectorRootCommutatorTraceLegality_of_threeBranchPairData
     (leaf:301-318) from ONE BasisHilbertSchmidtPairData whose traceProduct
     is the whole signed ledger (no per-branch trace-classness required).
     Measured: 1068 l_tr1 1.3462 -> 1.2850 (O(1), decreasing); in the
     xi-character basis the diagonal of C^dagger[C, K_S] is ALGEBRAICALLY
     ZERO - the danger lives only off that basis, which is exactly why the
     pair owner (not a diagonal-series owner) is the right shape.
     Named difficulty: the quasi-periodic twist mu_S / conj(mu_S) in the
     target multiplier (the raw-F1 killer) must be absorbed by the
     smoothing adaptation; classical commutator-smoothing is the template.
```

## 3. What does NOT change

- The 1066 single-contract leaf stays in the tree untouched (nothing
  deleted); its iff theorem remains the termwise bridge that IDENTIFIES
  S2-FK-HS with the retired raw-F1 series - that identification is what
  makes the 1067 measurement decide the route.  It simply stops being the
  production plan.
- F2 (compression legs), the capstone, and all consumers are untouched.
- GATE 1 mainline untouched; RH unclaimed.

## 4. Landing plan for the re-route itself

One new Dev leaf (+ paired audit) when P1/P2 contracts are supplied:
consume `..._of_rightSmoothing_and_rootCommutator` with the two producers
as explicit named analytic contracts (the 1065/1066 pattern), and record
the old production plan as inactive for the capstone (the 7d negative-guard
convention).  Until then this record is the route's source of truth.

## 5. Honesty ledger

- P1/P2 are analytic obligations, NOT settled by the 1068 measurements;
  the measurements license the ROUTE (the quantities are O(1)), not the
  theorems.
- The 1068 rig is a finite-dimensional model with a Gaussian stand-in root;
  the transfer to the actual owner is part of P1's obligation, not a
  formality.
- The D-weighted legality is a DIFFERENT statement from the retired raw
  F1/IsTraceClassAlong K_S; nothing in this record claims the unweighted
  statement.
