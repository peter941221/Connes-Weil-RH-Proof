# Proof 778: Hardy--Prolate Completed Gram

## Result

Proof 778 puts the Fourier and prolate pieces of Proof 777's completed source
band into one exact Gram identity on the literal common-log carrier.

Write

```text
E = radialSupportProjection
F = I - E
H = archimedeanHardyTitchmarshOperator
Q = sourceFourierSupportProjection = H E H
R = sourceSoninProjection
B = E - R
K = sourceProlateRemainder = (Q B)* (Q B).
```

The new Hardy leakage factor is

```text
A = F H E.
```

Lean proves

```text
A* A = E (I-Q) E = B-K,                              (778.1)
B = A* A + (Q B)* (Q B).                              (778.2)
```

Thus Proof 777's completed causal bracket has the exact form

```text
E T_S (I-E) + T_S [A* A + (Q B)* (Q B)],             (778.3)
```

and the literal target is

```text
Target_S
 = D_S* {E T_S (I-E) + T_S[A* A + (Q B)* (Q B)]}
   C_root* C_root J.                                 (778.4)
```

## What It Is

The Fourier/prolate part is no longer only the algebraic expression
`E-EQE+K`.  It is a single completed positive Gram with two physical legs:

```text
source band B
     |
     +-- Hardy boundary leg:  F H E
     |
     +-- prolate leg:         Q B
```

Equation `(778.2)` follows from the actual source facts
`Q=H E H` and `K=(Q B)* (Q B)`.  The first leg is the real-line
Hardy/Fourier half-line crossing, while the second is the CC20 prolate square
root.

## Why It Helps

Proof 777 ruled out proving Gate 3U from abstract two-projection algebra,
even with a rapidly summable prolate spectrum.  Equation `(778.2)` inserts
the missing actual Hardy--Titchmarsh geometry before the compact root acts.
It gives a concrete common object for a future Wiener--Hopf or Toeplitz-kernel
estimate:

```text
compact root
     -> completed Hardy/prolate Gram
     -> same-object signed trace
     -> support-polynomial Gate 3U estimate
```

The arrow from the Gram to the signed trace estimate is still open.  In
particular, `(778.2)` must not be split into two trace norms or two
Hilbert--Schmidt budgets: that would discard the scalar cancellation protected
by Proof 260 and is not a Gate 3U proof.

## Lean Declarations

```text
sourceHardyFourierLeakageFactor_adjoint_comp_self_eq_fourierComplement
sourceHardyProlateCompletedGram_eq_sourceBandProjection
finiteEulerCausalHardyProlateCompletedSoninComplement_eq_causalCompleted
finiteEulerTargetCommutatorResponse_eq_causalHardyProlateRootCorner
```

Source:

```text
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSGatePhysicalHardyProlateGram.lean
```

Audit:

```text
ConnesWeilRH/Dev/
  CCM24FiniteSGatePhysicalHardyProlateGramAudit.lean
```

## Scope

Proof 778 establishes an operator identity only.  It does not prove the
compact-root trace estimate, Gate 3U, the finite-S sign, Burnol's identity,
or `_root_.RiemannHypothesis`.
