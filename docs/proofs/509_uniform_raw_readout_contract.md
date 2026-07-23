# Proof 509: family-uniform completed-Julia raw readout contract

## Result

Proof 509 packages the quantifier that Gate 3U actually needs after Proof 508:
one nonnegative bound must dominate the complete signed mismatch for every
visible prime and every finite suffix. It proves that this domination family
is equivalent to a family of genuine bounded physical Douglas readouts, then
transports each readout through the unconditional polar correction.

It does not manufacture the missing analytic domination. The family field is
still the source-specific producer obligation. Consequently the finite-S
sign, Burnol identity, and an unconditional proof of RH remain open.

```text
+-----------------------------------------------------------+------------------+
| item                                                      | status           |
+-----------------------------------------------------------+------------------+
| common-bound physical domination contract                | packaged         |
| domination -> family of Douglas readouts                  | proved           |
| family readouts -> domination                             | proved           |
| exact uniform-family equivalence                          | proved           |
| raw correction factorization for every suffix              | proved           |
| common raw readout norm bound                             | proved           |
| common raw adjoint pointwise bound                        | proved           |
| source-specific analytic domination producer              | still open       |
| Gate 3U / finite-S sign                                   | still open       |
| Burnol identity / RH                                      | still open       |
+-----------------------------------------------------------+------------------+
```

## Contract

For a fixed selected owner, Sonin scale, and real bound `C`, the uniform
domination data contains

```text
0 <= C
forall p S,
  ||mismatch(p,S)^dagger x||^2
    <= C^2 (||ambientLoss(p,S,x)||^2
            + ||movingBoundary(p,S)^dagger x||^2).
```

The two physical energies remain summed. Splitting them into separate
primewise estimates would change the statement and discard the cancellation
required by Gate 3U.

The corresponding readout family contains, for each `(p,S)`, the Douglas
factor `M_(p,S)` with

```text
||M_(p,S)|| <= C
M_(p,S) * physicalAnalysis(p,S) = mismatch(p,S)^dagger.
```

Proof 507 already proves the single-suffix equivalence. Proof 509 only adds
the universal quantifier and preserves the same bound.

## Raw consequence

Proof 508 supplies the unconditional polar readout `P_S`, whose norm is at
most the selected detector norm. Subtracting the supplied mismatch readout
gives

```text
R_(p,S) = P_S - M_(p,S)
R_(p,S) * physicalAnalysis(p,S) = rawIntertwining(p,S)^dagger
||R_(p,S)|| <= ||detector|| + C.
```

Therefore every member of a valid family satisfies the same pointwise bound

```text
||rawIntertwining(p,S)^dagger x||
  <= (||detector|| + C) ||physicalAnalysis(p,S,x)||.
```

This is a raw Douglas/readout interface, not a Gate 3U trace estimate. A
future source producer must still prove the domination field without adding a
user axiom, `sorry`, or an absolute-value split of the signed response.

## Lean owner and audit

```text
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSCompletedJuliaUniformRawReadout.lean
ConnesWeilRH/Dev/
  CCM24FiniteSCompletedJuliaUniformRawReadoutAudit.lean
```

The audited declarations use only Mathlib's ordinary foundational axioms:
`[propext, Classical.choice, Quot.sound]`. No Gate 3U, finite-S sign, Burnol,
or RH theorem is claimed by this module.
