# Proof 374: detector-variance Lean owner

Date: 2026-07-18

Status: generic ring-level Lean ownership for the exact algebra introduced by
Proofs 370--372.  The module formalizes detector variance, the two-corner
single-root factorization of a positive detector, and the two-support prolate
renewal.  It is imported by the `CCM25Concrete` aggregate and has a focused
axiom audit.

This is an algebraic foundation, not the open endpoint root-commutator bound
from Proof 373.  Gate 3U, the finite-`S` sign, Burnol's identity, and RH remain
open.

## 1. Result

```text
+------------------------------------------------+---------------------------+
| layer                                          | judgment                  |
+------------------------------------------------+---------------------------+
| detector crossing covariance                  | Lean owner               |
| frame multiplicative defect                   | Lean owner               |
| positive detector root corners                | Lean owner               |
| two-support prolate renewal                    | Lean owner               |
| aggregate import                              | added                    |
| endpoint root uniformity                      | not encoded / open      |
| Gate 3U / finite-S sign / Burnol / RH           | open / open / open / open|
+------------------------------------------------+---------------------------+
```

## 2. Source module

The new module is

```text
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSDetectorVariance.lean                 (LV.1)
```

It works over an arbitrary noncommutative ring.  Adjoint-oriented operators
are supplied as explicit elements, so the theorems own only algebra and do
not smuggle in analytic assumptions.

## 3. Owned theorems

The module proves

```text
detectorCrossingAdjoint_mul_detectorCrossing_eq_variance,
frameVariance_eq_complement_defect,
positiveDetectorCrossing_eq_rootCorners,
rootCrossing_mul_one_sub_prolate_eq_boundary.       (LV.2)
```

Their mathematical readbacks are respectively

```text
D*D=compressed variance,
frame variance=off-range defect covariance,
(I-P)C*C P=two single-root corner products,
R C P(I-PQP)=outer boundary-second boundary.        (LV.3)
```

## 4. Deliberate theorem boundary

The module does not contain a structure field or premise asserting

```text
sup_j norm([C_g,P_j])_2^2<=polynomial.              (LV.4)
```

Equation `(LV.4)` is Proof 373's actual analytic producer.  Encoding it as an
assumption would not advance Gate 3U.

## 5. Verification

The unified five-batch verification ran in the WSL2 ext4 mirror:

```text
flock -w 1800 /tmp/connes-weil-rh-lake.lock \
  lake build \
    ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSDetectorVariance \
    ConnesWeilRH.Dev.CCM24FiniteSDetectorVarianceAudit

flock -w 1800 /tmp/connes-weil-rh-lake.lock \
  lake build ConnesWeilRH.Source.CCM25Concrete
```

The focused owner and audit build passed with `576` jobs.  All four audited
theorems report exactly `[propext]`.  The `CCM25Concrete` aggregate passed
with `3661` jobs.  These results replace the pre-build expectation that the
generic ring algebra would need no axioms.

## 6. Route judgment

```text
+------------------------------------------------+---------------------------+
| layer                                          | judgment                  |
+------------------------------------------------+---------------------------+
| Proofs 370--372 algebra                        | Lean-owned               |
| analytic Schatten/trace legality               | remains external        |
| endpoint root theorem `(MR.6)`                 | open, active producer   |
| Proof 373 consumer                            | ready                    |
| Gate 3U / finite-S sign / Burnol / RH           | open / open / open / open|
+------------------------------------------------+---------------------------+
```
