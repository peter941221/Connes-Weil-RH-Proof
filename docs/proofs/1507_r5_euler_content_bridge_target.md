# 1507 — ρ5 Euler-content bridge: exact target and current obstruction

**Status: OPEN, target formalized at the interface level.** This record
separates the arithmetic theorem already available from the missing
identification of the G8 endpoint aggregate. It does not turn the ρ5 iff
normal form into an Euler formula.

The compiled G8 endpoint limit is the source trace of

```text
J† C† G C J
```

where `C` is the selected global root convolution and `G` is the fixed
adjoint-shear Gram. Record 1504 proves that the same-owner readback reaches
`qw` exactly when the real part of this aggregate equals `qw`.

Independently, `CCM24FiniteSEndpointArithmeticLimit` proves that the
arithmetic operator has ordinary trace equal to the finite visible
prime-power sum, and that the completed residual is the route trace minus
that sum. This is the available Euler consumer.

The missing theorem is therefore an object-level bridge of the following
shape, with all terms defined from the selected owner and finite family:

```text
realTrace(J† C† G C J)
  = finitePrimeTermSum(family) + residualLimit
```

followed by the proof that `residualLimit` is exactly the archimedean/P2
part in the definition of `qw`. Neither equality follows from positivity,
trace convergence, or the formal ρ5 iff. In particular, the existing
identity

```text
sourceCompression(G) = metricCoframe† detector metricCoframe
```

does not rewrite the inserted vectors `C (J u)` as source vectors; applying
it there would be a type error and would silently erase the Euler content.

The rho5 gate is consequently not closed by this record. The next valid
brick must prove the displayed object-level bridge (or a stronger explicit
P2 decomposition) from the committed arithmetic ledger, without taking
`qw` or its sign as input.

## 2026-09-16 object audit: the available arithmetic response is a different
## root sandwich

The committed arithmetic endpoint ledger is not an unlabelled version of the
G8 aggregate. Its root response is

```text
rootSandwichedBandResponse = C * soninBandDifference * C†
```

and its finite-prefix theorem rewrites that response as the arithmetic
operator plus the completed root-cycle residual. The G8 endpoint aggregate is

```text
J† * C† * G * C * J
```

with the adjoint-shear Gram `G`. The order of `C` and `C†`, the source
compression by `J`, and the middle operator (`G` versus
`soninBandDifference`) are all different. The physical-endpoint ledger adds
further internal-forward and complement channels before it reaches the G8
cutoff object. Therefore the existing arithmetic prefix theorem cannot be
instantiated by rewriting names; a bridge must either prove these correction
channels cancel in the selected limit or introduce the correctly corrected
G8 arithmetic response. This is a structural audit result, not a numerical
no-go and not a claim that no bridge can exist.

## 2026-09-16 type check: the tempting metric root sandwich is ill-typed

A candidate shortcut would replace the actual aggregate by a root sandwich
of the source-compressed metric Gram. That would require composing

```text
(J† G J)  : sourceSoninCarrier -> sourceSoninCarrier
C J       : sourceSoninCarrier -> finiteSCarrier
```

on the same side. The composition is impossible: `J† G J` consumes a source
vector, while `C J` produces an ambient vector. Lean rejects this candidate
at the composition boundary. This confirms that the `C(Ju)` obstruction is a
genuine carrier mismatch, not a missing simp lemma. A valid `rho5` bridge must
keep `C` and `C†` on the ambient carrier and compare the resulting scalar
trace by a new finite-level identity.

## 2026-09-16 corrected ambient normal form

The type-correct aggregate can be named before attempting the arithmetic
comparison. Define

```text
A_G8 = C† * G * C : finiteSCarrier -> finiteSCarrier.
```

Then the endpoint source operator is definitionally its source compression:

```text
J† * A_G8 * J = J† * C† * G * C * J.
```

This is now formal in `C1G8R5AggregateExpansion`. It isolates the actual
bridge target: compare the ambient operator `A_G8` (and only then compress by
`J`) with the finite arithmetic response. The declaration does not identify
`A_G8` with `rootSandwichedBandResponse`; that equality, or an explicit
correction decomposition, remains the open rho5 producer.

The same module now proves `A_G8.IsPositive` and positivity of its source
compression. This is an internal Gram fact only: it supplies no trace
convergence and no equality with the arithmetic operator.

## 2026-09-16 explicit correction normal form

The ambient difference is now named without any assumption that it vanishes:

```text
Delta_G8 = A_G8 - rootSandwichedBandResponse.
```

Lean proves the exact decomposition

```text
A_G8 = rootSandwichedBandResponse + Delta_G8
J† A_G8 J = J† (rootSandwichedBandResponse + Delta_G8) J.
```

Thus the unresolved finite-level bridge is concretely the trace contribution
of `Delta_G8`, together with the source/ambient trace transport. Any future
claim that the correction disappears must provide its own operator or trace
estimate; the definition is not a stored conclusion.

## 2026-09-16 finite-prefix arithmetic-plus-correction ledger

The correction is now integrated with the existing endpoint arithmetic ledger.
For every ambient Hilbert basis and finite prefix N, Lean proves the exact
identity

```text
trace(prefix A_G8)
 = trace(prefix arithmeticOperator)
 + actualBandEndpointCompletedResidualTrace
 + trace(prefix Delta_G8).
```

The completed residual is the previously committed same-object residual plus
finite root-cycle defect. Separately, `Delta_G8` is proved self-adjoint, using
positivity of `A_G8` and self-adjointness of the root response. This makes its
finite-prefix trace real, but gives no sign or decay. The remaining rho5 work
is therefore an actual estimate for this correction and the source/ambient
transport.

The ambient aggregate also has a formally checked four-channel expansion:
`C† W C + C† N W C + C† W N† C + C† N W N† C`, where `N` is the
finite oblique shear and `W` the detector. This is an operator identity before
source compression, so the correction estimate can be split into the two cross
channels, the leakage square, and the difference between the base channel and
the arithmetic response.

Because `Delta_G8` is self-adjoint, its finite-prefix matrix is Hermitian and
its matrix trace has zero imaginary part. This is now a formal Lean theorem.
The result only removes a complex-valued bookkeeping nuisance; it supplies no
bound, positivity, or convergence of the correction trace.

## 2026-09-17 exact supplier ledger for the B object (record 1563)

The paper object is now fixed at the ambient carrier before any source
compression.  Write

```text
J = sourceInclusion lambda
C = rootConvolution owner
W = detectorOperator owner
N = finiteEulerPulledObliqueShear lambda family
G = (I + N†) W (I + N)
A_G8 = C† G C
R = C (soninBandDifference lambda family) C†
Delta_G8 = A_G8 - R.
```

The exact endpoint object is

```text
J† A_G8 J = J† C† G C J
```

and its four-channel expansion is

```text
J† C† W C J
+ J† C† N W C J
+ J† C† W N† C J
+ J† C† N W N† C J.
```

For every ambient basis prefix `(basis,N)`, the exact trace ledger is

```text
tr_prefix(A_G8)
 = tr_prefix(arithmeticOperator)
 + tr_prefix(sameObjectResidual)
 + tr_prefix(actualBandEndpointRootCycleDefect)
 + tr_prefix(Delta_G8).
```

The four summands have distinct suppliers:

| term | supplier | status |
| --- | --- | --- |
| `tr_prefix(arithmeticOperator)` | `SelectedCrossingOperatorBridge.ordinaryTraceAlong_eulerLogWeightedGlobalPairTraceOperatorSum_eq_finitePrimeTerm_pow_sum`; under its support and basis-data premises this is the finite sum of `owner.finitePrimeTerm (p^m)` | formal arithmetic theorem, full trace transport still conditional |
| `tr_prefix(sameObjectResidual)` | `CCM24FiniteSProjectionTrace.sameObjectResidual`; exact three-part split is `sameObjectResidual_eq_threePartLedger`, namely `(W prolateDifference - arithmeticOperator) - W compressionDifference` | formal residual definition, no sign/decay |
| `tr_prefix(actualBandEndpointRootCycleDefect)` | `CCM24FiniteSEndpointArithmeticLedger.actualBandEndpointRootCycleDefect`; supplied by the finite prefix cycle boundary identity | formal finite-prefix error, no limit estimate |
| `tr_prefix(Delta_G8)` | `C1G8R5AggregateExpansion.g8AmbientArithmeticCorrection`; this is the difference between the actual G8 ambient sandwich and `R` | formal correction, self-adjoint only; no vanishing or sign |

Thus the current formal object has **four** trace-level rows, but only two
independent analytic producer packages remain: (i) the total survivor plus
visible-boundary diagonal energy, and (ii) one rho5 bridge controlling the
arithmetic/residual/correction transport.  The apparent extra rows are
bookkeeping suppliers, not separate RH proofs.

The obstruction in record 1507 is therefore resolved at the object level:
`C (J u)` is kept on the ambient carrier, `A_G8` is formed there, and only
then is `J† A_G8 J` taken.  No source-compression identity is applied to
`C (J u)`.  What remains open is precisely an equality or estimate for
`Delta_G8` together with the residual/cycle trace transport; positivity of
`A_G8` does not provide that equality.

This is a formal interface audit, not an arithmetic identification and not
an RH claim.

## 2026-09-17 active arithmetic supplier theorem (record 1564)

`C1G8R5AggregateExpansion.ordinaryTraceAlong_g8ArithmeticOperator_eq_finitePrimeTerm_sum`
now exports the arithmetic row directly on the active G8 module.  Given the
same support inclusion and `GlobalPrimePowerTraceBasisData` premises as the
selected crossing theorem, it identifies the ordinary trace of
`arithmeticOperator owner family` with
`sum pm in family.terms, owner.finitePrimeTerm (pm.1 ^ pm.2)`.  The paired audit
prints the standard three axioms only.  This closes the naming/interface gap
for the finite prime-power supplier; it does not estimate the residual,
root-cycle, or `Delta_G8` rows.

## 2026-09-17 finite-prefix four-channel trace theorem (record 1565)

The active G8 leaf now exports
`trace_basisPrefixMatrix_g8AmbientRootAggregate_eq_fourChannel_sum`.  For
every ambient Hilbert basis prefix it rewrites the trace of `A_G8` as the
sum of the base channel, the two adjoint cross channels, and the leakage
square, with `J` retained only in the final source compression theorem.  The
proof is the checked operator expansion followed by finite matrix additivity;
it introduces no trace-cycle, positivity, or limiting premise.  Audit build
1576 is green with the standard axiom set and no `sorryAx`.
