# Proof 749: Gate Physical Normalized Anomaly Trace

## Result

The result is a useful correction, but it does not close Gate 3U.  Proof 749
gives both summands from Proof 748 genuine fixed-family Hilbert--Schmidt
trace-ideal owners and computes their ordinary traces exactly.

Let

```text
b_S=Tr_source(sourceBandGramResponse_S).
```

Lean proves

```text
Tr_source(SymmetricResponse_S)
  =-1/2 (b_S+conj(b_S)),

Tr_source(Anom_S)
  = 1/2 (b_S-conj(b_S)).                              (AT.1)
```

Thus the anomaly trace is the pure-imaginary source/ambient boundary
correction.  It is not automatically zero.

```text
+------------------------------------------+----------------------------------+
| layer                                    | result                           |
+------------------------------------------+----------------------------------+
| normalized right numerator              | one completed S2 x S2 owner     |
| bounded inverse-Gram cycle               | legal through the same pair     |
| symmetric response trace legality       | closed for every fixed family   |
| anomaly trace legality                   | closed for every fixed family   |
| symmetric scalar                        | Hermitian part of source trace   |
| anomaly scalar                          | anti-Hermitian part of source    |
| unconditional anomaly cancellation      | not proved                      |
| source/ambient endpoint trace identity  | exact missing premise            |
| Gate 3U / finite-S sign / RH             | open                             |
+------------------------------------------+----------------------------------+
```

## 1. What It Is

Retain Proof 748's notation

```text
Ghat_S=c_S^(-2)G_S,
Ahat_S=c_S^2 G_S^(-1),

Lhat_S=c_S^(-2)(K_S-G_S X),
Rhat_S=c_S^(-2)(K_S-X G_S),

Sym_S=(Lhat_S+Rhat_S)/2,
Anom_S=Ahat_S(Lhat_S-Rhat_S)/2.                       (AT.2)
```

The four-branch physical pair from Proof 429 already owns

```text
sourceBandGramResponse_S
  =-(K_S-X G_S)G_S^(-1).                              (AT.3)
```

Closing its right source leg with `Ghat_S` cancels the inverse Gram and the
lower-factor gauge:

```text
sourceBandGramResponse_S Ghat_S=-Rhat_S.              (AT.4)
```

After the final minus sign is retained inside the pair's right leg, the new
pair has trace product exactly `Rhat_S`.  Swapping its two Hilbert--Schmidt
legs gives `Rhat_S^dagger=Lhat_S`.

The construction is

```text
 completed four-branch pair
          |
          | right bounded closure by Ghat_S
          v
 trace product = -Rhat_S
          |
          | right-leg scalar -1
          v
 trace product = Rhat_S
          |
          | swap the two S2 legs
          v
 trace product = Lhat_S.                              (AT.5)
```

This is stronger than weak diagonal-series summability.  Each numerator has
an explicit `A^dagger B` owner with both factors square summable in the named
source basis.

## 2. Why The Cycle Is Legal

For any pair-owned trace product `Q=U^dagger V` and any bounded operator `A`,
Proof 749 forms two bounded sandwiches:

```text
left pair:   (U A^dagger)^dagger V = A Q,
right pair:  U^dagger(V A)         = Q A.             (AT.6)
```

Cycling each pair to its common Hilbert--Schmidt target gives the same target
operator `V A U^dagger`.  Therefore

```text
Tr(A Q)=Tr(Q A)
```

without invoking cyclicity for arbitrary bounded products.

Applying `(AT.6)` to `Q=Rhat_S` and `A=Ahat_S` gives

```text
Tr(Ahat_S Rhat_S)=Tr(Rhat_S Ahat_S).
```

The right side is the original right-ordered source Gram response.  The left
boundary satisfies

```text
Ahat_S Lhat_S=Target_S,
Target_S=(sourceGramResponse_S)^dagger.
```

Ordinary trace of an adjoint is the complex conjugate trace.  Additivity is
now legal because both dressed numerator terms have explicit pair owners.
This yields `(AT.1)`.

## 3. Why The Anomaly Does Not Disappear

Equation `(AT.1)` gives the exact criterion

```text
Tr(Anom_S)=0
  <-> b_S=conj(b_S).                                  (AT.7)
```

In plain language, the anomaly vanishes exactly when the right-ordered
source-band trace is real.

The ambient endpoint operator

```text
rootSandwichedBandResponse_S
```

is self-adjoint, so its ordinary diagonal trace is real.  That fact does not
by itself prove `(AT.7)`: the source and ambient traces live on different
carriers and are related by rectangular factor cycles with boundary terms.

The logical gap is

```text
source completed trace b_S
          |
          | missing infinite source/ambient cycle
          | including escaping boundary control
          v
ambient self-adjoint endpoint trace
          |
          v
real scalar.                                          (AT.8)
```

Proofs 456 and 461 perform exact finite-prefix cycles.  Proof 456 retains both
rectangular product defects.  Proof 461 cancels an internally balanced source
prefix against a complementary target prefix.  Neither theorem takes the
limit required to identify `b_S` with the ordinary ambient endpoint trace.

Proof 749 therefore includes only the valid conditional theorem:

```text
Tr_source(sourceBandGramResponse_S)
  =Tr_ambient(rootSandwichedBandResponse_S)

  -> Tr_source(Anom_S)=0.                              (AT.9)
```

The premise in `(AT.9)` is not claimed.

## 4. Correction To The Old Proof 299 Claim

Proof 299 proposed that Hermitian endpoint reality kills the diagonal
first-jet anomaly.  Proof 749 isolates the exact missing step in that claim.
The proposed conclusion is valid after `(AT.9)`, but the current completed
Hilbert--Schmidt cycles do not prove `(AT.9)`.

Consequently, none of the following is licensed:

```text
ambient endpoint is self-adjoint
  -> source trace is real;

finite rectangular traces cycle
  -> their infinite ordinary traces cycle;

numerator is a commutator
  -> its inverse-Gram-dressed trace is zero.           (AT.10)
```

The second failure is the same escaping-boundary mechanism guarded by Proofs
424, 429, and 438.

## 5. Lean Ownership

The source module is

```text
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSGatePhysicalNormalizedAnomalyTrace.lean
```

The import-facing audit is

```text
ConnesWeilRH/Dev/
  CCM24FiniteSGatePhysicalNormalizedAnomalyTraceAudit.lean
```

The principal declarations are

```text
finiteEulerNormalizedRightBoundaryPairData_traceProduct_eq
finiteEulerNormalizedSymmetricBoundaryResponse_isTraceClassAlong
finiteEulerNormalizedGramSimilarityAnomaly_isTraceClassAlong
ordinaryTraceAlong_normalizedSymmetricBoundaryResponse_eq
ordinaryTraceAlong_normalizedGramSimilarityAnomaly_eq
ordinaryTraceAlong_normalizedGramSimilarityAnomaly_eq_zero_iff
ordinaryTraceAlong_normalizedGramSimilarityAnomaly_eq_zero_of_endpointCycle
```

The accepted Ubuntu 24.04 WSL2 ext4 builds were

```text
+----------------------------------+-------+--------+
| target                           | jobs  | result |
+----------------------------------+-------+--------+
| focused source + axiom audit     |  3393 | PASS   |
| CCM25Concrete aggregate + audit  |  4018 | PASS   |
| full repository                  |  4098 | PASS   |
+----------------------------------+-------+--------+
```

All ten audited theorems use exactly
`[propext, Classical.choice, Quot.sound]`.

Static checks found no `sorry`, `admit`, user axiom, heartbeat increase,
recursion-limit increase, unsafe declaration, new module warning, line over
100 characters, or trailing whitespace in the new source and audit.

The final matching Windows/WSL SHA-256 values are

```text
source     3bb299bb73a89948a9e5a0c58c162bb7cba9d39039a07d902582032a460a0ffc
audit      0f1f85b364dd38b81e9618d2ad9235f82dd01c4abc7e53421d49444b6504a207
aggregate  ea4d11807593bf368889dfefc7eb0fba173585c06ade333a45d14d24127fd119
```

## 6. Remaining Bottom

Proof 749 closes fixed-family trace legality for the separated symmetric and
anomaly terms.  It does not license separate uniform estimates: a triangle
inequality could still destroy the compact-support cancellation in the full
target.

The next valid step must do one of the following while preserving the same
physical owner:

```text
1. prove the source/ambient endpoint trace identity with its escaping
   rectangular boundary controlled, thereby killing Anom_S; or

2. identify the nonzero boundary correction in the complete
   outer/second-support/prolate scalar and estimate it together with the
   symmetric response.                                (AT.11)
```

Even if line 1 succeeds, the family-uniform estimate for the symmetric graded
response remains open.  Gate 3U, the finite-S sign, the arithmetic same-object
identity, Burnol's identity, and `_root_.RiemannHypothesis` remain open.
