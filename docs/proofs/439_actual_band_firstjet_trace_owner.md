# Proof 439: actual band first-jet trace owner

Date: 2026-07-20

Status: axiom-clean Lean construction of a trace-legal `A^*B` owner for the
correctly oriented source-band first jet, together with a bound uniform in the
visible finite-prime family.

The result is good but limited.  It controls the actual paired first jet by a
fixed physical Hilbert--Schmidt energy.  It does not prove a separate
commutator trace is zero, supply the required polynomial compact-root bound,
control the nonlinear endpoint remainder, close Gate 3U, or prove RH.

## 1. Verdict

```text
+------------------------------------------------------+----------------------+
| statement                                            | judgment             |
+------------------------------------------------------+----------------------+
| actual source-band paired response has correct order | Lean proved          |
| response rewrites through the fixed commutator       | Lean proved          |
| two genuine Hilbert--Schmidt pairs own the trace     | Lean proved          |
| ordinary trace is legal on the named global basis    | Lean proved          |
| bound has no finite-prime family on its right side   | Lean proved          |
| residual commutator trace vanishes separately        | not claimed          |
| fixed physical energy has route polynomial bound     | open                 |
| nonlinear endpoint remainder bound                   | open                 |
| Gate 3U / finite-S sign / Burnol / RH                | open                 |
+------------------------------------------------------+----------------------+
```

## 2. What the owner represents

On the actual common-log carrier put

```text
R =sourceSoninProjection,
B =sourceBandProjection,
W =selected detector,
N =normalizedFiniteEulerInverse.                         (AT.1)
```

Proof 438 showed that the correctly oriented paired response is

```text
J_actual=R W B N R+R N^* B W R.                         (AT.2)
```

The common-support splitting gives

```text
R^2=R,       BR=0,       RB=0.                          (AT.3)
```

Therefore `(AT.2)` has the exact fixed-commutator form

```text
J_actual
 =-R[W,R]B N R+R N^* B[W,R]R.                          (AT.4)
```

This is an operator identity before any trace is taken.  In particular, it
does not use

```text
Tr([R,W K_S])=0.                                        (AT.5)
```

Equation `(AT.5)` is still unauthorized on the infinite carrier.

## 3. How trace legality is constructed

The existing physical boundary pair `fixedPhysicalPairData` has genuine
Hilbert--Schmidt legs and trace product

```text
[W,R].                                                  (AT.6)
```

Proof 439 applies two bounded sandwiches to that same pair:

```text
forward trace product =-R[W,R]B N R,
reverse trace product = R N^* B[W,R]R.                  (AT.7)
```

The two pairs are assembled with `l2Sum` before the ordinary trace is taken:

```text
fixed physical pair
        |
        +-- bounded sandwich + sign ---> forward branch
        |
        +-- bounded sandwich ----------> reverse branch
                                              |
                         l2Sum <--------------+
                           |
                           v
                 trace product = J_actual.              (AT.8)
```

Thus `sourceActualBandFiniteEulerPairedResponse_isTraceClassAlong` derives
trace legality from explicit square-summable columns.  No whole-line trace
cycle and no stored trace-class premise is introduced.

## 4. Why the estimate is family-uniform

The actual source operators satisfy

```text
norm(R)<=1,       norm(B)<=1,
norm(N)<=1,       norm(N^*)<=1.                          (AT.9)
```

Hence all four exposed sandwich maps are contractions.  If

```text
E_left =sum_i norm(fixedPair.left(e_i))^2,
E_right=sum_i norm(fixedPair.right(e_i))^2,              (AT.10)
```

then each copied column energy is bounded by its source energy.  The `L2`
sum has at most twice each energy, while the generic trace consumer gives the
factor `1/2`.  Lean therefore proves

```text
abs Tr(J_actual)<=E_left+E_right.                         (AT.11)
```

The right side of `(AT.11)` depends on the fixed physical boundary pair but
contains no `family`.  This is the precise uniformity proved here.

It is not yet the Gate 3U estimate.  The additive physical energy has not
been bounded by the required homogeneous polynomial in compact-root support
and Sobolev seminorms.  Applying absolute values to its internal branches
would also discard the signed cancellation protected by Proofs 260 and 436.

## 5. Relationship to the Proof 438 anomaly ledger

Proof 438 decomposed the difference between the old and actual orientations
through a compressed-skew commutator.  Proof 439 does not prove that the
residual commutator in that decomposition has zero trace.  Instead it builds
a separate legal owner for the complete actual response `(AT.2)`.

```text
Proof 438 route                         Proof 439 route

orientation difference                 actual orientation itself
        |                                       |
residual commutator                     two bounded sandwiches
        |                                       |
trace cycle still guarded               legal A^*B trace owner.            (AT.12)
```

This distinction matters: constructing the trace of the desired operator is
not the same theorem as proving that a different commutator has trace zero.

## 6. Lean ownership and axioms

The source and focused audit are

```text
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSActualBandFirstJetTrace.lean

ConnesWeilRH/Dev/
  CCM24FiniteSActualBandFirstJetTraceAudit.lean.          (AT.13)
```

The central declarations are

```text
actualBandCommutatorPairedResponse_eq_detector
actualBandCommutatorPairData
actualBandCommutatorPairData_traceProduct_eq
actualBandCommutatorPairData_isTraceClassAlong
actualBandCommutatorPairData_ordinaryTrace_norm_le_sourceEnergy
sourceActualBandFiniteEulerPairData_traceProduct_eq
sourceActualBandFiniteEulerPairedResponse_isTraceClassAlong
sourceActualBandFiniteEuler_ordinaryTrace_norm_le_fixedPhysicalEnergy.
```

The generic ring identity uses exactly

```text
[propext].                                                (AT.14)
```

The Hilbert-space pair data and actual-carrier results use exactly

```text
[propext, Classical.choice, Quot.sound].                  (AT.15)
```

No project axiom, `sorry`, `admit`, `sorryAx`, or stored trace premise is
introduced.

## 7. Verification

The isolated Ubuntu 24.04 ext4 acceptance batch passes:

```text
+------------------------------------------------------+-------+--------+
| target                                               | jobs  | result |
+------------------------------------------------------+-------+--------+
| actual band first-jet focused axiom audit            |  3262 | PASS   |
| CCM25Concrete aggregate                              |  3712 | PASS   |
| full repository                                      |  3793 | PASS   |
+------------------------------------------------------+-------+--------+
```

The audit contains `12` `#check` commands and `12` matching `#print axioms`
commands.  The new source and audit contain no proof placeholder or line
longer than 100 characters.  The source introduces no warning; aggregate and
full builds replay only pre-existing warnings from other modules.

## 8. Remaining bottom

```text
correctly oriented first-jet operator                 CLOSED
explicit Hilbert--Schmidt trace owner                 CLOSED
visible-family uniform fixed-energy bound             CLOSED
homogeneous polynomial bound for that energy          OPEN
bridge to the complete nonlinear endpoint             OPEN
uniform quadratic-remainder bound                     OPEN
Gate 3U / finite-S sign                               OPEN
Burnol identity                                       OPEN
_root_.RiemannHypothesis                              OPEN
```

The next useful theorem must keep the physical detector bracket recombined
and bound either its fixed energy or the complete nonlinear remainder by a
canonical Euler energy before taking the first branchwise absolute value.
