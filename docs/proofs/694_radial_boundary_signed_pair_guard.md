# Proof 694: Radial boundary signed-pair guard

Date: 2026-07-31

Status: exact producer guard. This proof does not construct the missing
full-carrier signed pair and does not close Gate 3U.

## Result

+-------------------------------+--------------------------------------------+
| object                        | exact readback                             |
+-------------------------------+--------------------------------------------+
| bare boundary channel         | C = (I - E) U_(log p) P_S                 |
| Cauchy defect                 | D = C† C                                   |
| equal-leg Cauchy pair         | traceProduct = D                           |
| signed boundary owner         | traceProduct = C                           |
| extra identity for reuse      | D = C, equivalently C† C = C               |
| consequence of that identity  | C is self-adjoint                          |
+-------------------------------+--------------------------------------------+

The definitions of C and D are in:

ConnesWeilRH/Source/CCM25Concrete/CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorFrameLossRadialBoundarySplit.lean

ConnesWeilRH/Source/CCM25Concrete/CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorFrameLossRadialBoundaryCauchyDefect.lean

The positive pair producer is:

ConnesWeilRH/Source/CCM25Concrete/CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorFrameLossRadialBoundaryCauchyPairProducer.lean

## Exact Lean guard

The new source module is:

ConnesWeilRH/Source/CCM25Concrete/CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorFrameLossRadialBoundarySignedPairGuard.lean

For a named Hilbert basis and the crossing-energy premise, Lean proves:

~~~
equal-leg traceProduct = C
  <-> CauchyDefect = C
~~~

It also proves:

~~~
equal-leg traceProduct = C
  -> C† C = C
  -> IsSelfAdjoint C
~~~

The last implication uses the source theorem that C† C is positive, hence
self-adjoint. It does not assume that the bare boundary channel is
self-adjoint.

The import-facing audit is:

ConnesWeilRH/Dev/CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorFrameLossRadialBoundarySignedPairGuardAudit.lean

The audit reports exactly:

~~~
[propext, Classical.choice, Quot.sound]
~~~

## Why the source column is not enough

The existing radial column bridge proves only the source restriction:

~~~
C * newSuffixFrame
  = readout * finitePrimeEulerRadialGeometricBoundaryColumn
~~~

The full-carrier extension then gives a bounded readout through
newSuffixFrame†, but it does not give two Hilbert--Schmidt legs for C.
The relevant source contracts are in:

...RadialBoundaryColumnBridge.lean

...RadialBoundaryColumnFullCarrierExtension.lean

Thus the following implication is not available:

~~~
finite radial-column factorization
  -> BasisHilbertSchmidtPairData with traceProduct = C
~~~

The positive-energy criterion from Proof 692 and the equal-leg pair from
Proof 693 remain valid, but both own C† C. They do not own the signed
boundary channel C.

## Route decision

Do not feed the positive Cauchy pair into
RadialSignedPhysicalOwnerPairData.boundaryData without a new theorem proving
C† C = C. The common-root owner in
...RadialPhysicalOwnerCommonRootPairData.lean requires the stronger
readback:

~~~
boundaryData.traceProduct = radialSoninBoundaryCrossing p S
~~~

The remaining Gate 3U route must therefore keep the complete physical
branches inside a signed scalar pairing until compact-support cancellation
has acted. This is the same ownership rule recorded in:

docs/proofs/273_signed_paired_stopping_guard.md

The finite-S sign, the arithmetic same-object trace identity, Burnol's
identity, and _root_.RiemannHypothesis remain open.

## Verification

Commands run in the Ubuntu-24.04 WSL2 ext4 verification copy:

~~~
lake build ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorFrameLossRadialBoundarySignedPairGuard
lake build ConnesWeilRH.Dev.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorFrameLossRadialBoundarySignedPairGuardAudit
~~~

Results:

+--------------------------------------+-------+--------+
| target                               | jobs  | result |
+--------------------------------------+-------+--------+
| signed-pair guard source             | 3484  | PASS   |
| signed-pair guard audit              | 3485  | PASS   |
+--------------------------------------+-------+--------+

No sorry, admit, or user axiom was added.
