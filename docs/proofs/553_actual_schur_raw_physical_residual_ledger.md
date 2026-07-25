# Proof 553: actual Schur/raw-physical residual ledger

Result: the actual-versus-Schur bookkeeping is closed, but Gate 3U is still
open.

The source module is
`ConnesWeilRH/Source/CCM25Concrete/CCM24FiniteSCompletedJuliaRawPhysicalResidualLedger.lean`.
Its focused import audit is
`ConnesWeilRH/Dev/CCM24FiniteSCompletedJuliaRawPhysicalResidualLedgerAudit.lean`.

## What is proved

The module defines one common four-term raw physical row for arbitrary forward
and endpoint coframes:

```text
rawPhysicalFourTermRowOfCoframes
```

The repository's actual row is exactly this definition instantiated with the
actual forward and endpoint coframes:

```text
suffixActualBandRawPhysicalFourTermRow
  = rawPhysicalFourTermRowOfCoframes actualForwardS actualEndpointS
      actualEndpointPS actualForwardPS
```

For any proposed Schur coframes, the residual is defined as the complete
signed row difference:

```text
rawPhysicalCoframeResidualRow
  = rawPhysicalFourTermRowOfCoframes actual coframes
    - rawPhysicalFourTermRowOfCoframes Schur coframes
```

Lean proves the exact identity:

```text
actual raw physical row
  = Schur four-term row
    + physical coframe residual row
```

The specialized theorem is
`suffixActualBandRawPhysicalFourTermRow_eq_schur_add_residual`.

For a literal suffix, the source-forward coframe is also split exactly:

```text
actual forward coframe
  = source-forward Schur coframe
    + signed physical transport residual
```

The endpoint coframe uses the same residual and the named metric coframe.
The theorem
`suffixActualBandRawPhysicalFourTermRow_eq_namedSchur_add_residual`
instantiates the row ledger with these named source-forward Schur coframes.

The component-row handoff is also exact but conditional. If the Schur row and
the residual row each factor through the same ambient-loss and moving-boundary
analysis columns, then their coordinate rows add to an actual component-row
factorization:

```text
Schur factorization + residual factorization
  -> actual component-row factorization
```

This is the role of
`componentRows_add_of_schur_and_residual`.

## Boundary

The residual is not set to zero, bounded, or identified with a previously
proved post-Q remainder. The Schur telescope therefore remains a consumer
component only. A genuine Gate 3U producer must still supply the source
factorizations and a uniform signed bound for the actual residual ledger.

Keep all four terms signed until that producer is available. Estimating the
Schur row and residual independently would discard the cancellation that the
physical readout is meant to preserve.

The finite-S sign, Burnol identity, and `_root_.RiemannHypothesis` remain open.

## Verification

All commands were run in the Ubuntu-24.04 WSL2 ext4 verification mirror:

```text
lake build ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalResidualLedger
Build completed successfully (3332 jobs).

lake build ConnesWeilRH.Dev.CCM24FiniteSCompletedJuliaRawPhysicalResidualLedgerAudit
Build completed successfully (3333 jobs).

lake build ConnesWeilRH.Source.CCM25Concrete
Build completed successfully (3823 jobs).

lake build
Build completed successfully (3904 jobs).
```

The focused audit uses `#check`, `#print`, and `#print axioms`. The seven
audited principal equalities report exactly:

```text
[propext, Classical.choice, Quot.sound]
```

The new source and audit contain no `sorry`, `admit`, or user `axiom`/
`constant` declaration. Existing repository lint warnings are unchanged; the
WSL localhost-proxy notice is external to the Lean build.
