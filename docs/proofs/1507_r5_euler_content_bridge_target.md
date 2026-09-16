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
