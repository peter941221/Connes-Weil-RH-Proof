# Proof 520: source-forward actual Schur transport

## Result

The source-owned actual Schur cascade now has a separate source-forward
product.  For each finite visible-prime suffix, Lean defines the ambient
transport and the source transition in the chronological order forced by the
actual step equation

```text
T_p * F_(p::S) = F_S * U_(p,S).
```

The resulting products satisfy the exact terminal-frame intertwining

```text
forwardAmbient(S) * newFrame(S)
  = emptyFrame * forwardTransition(S).
```

The source-forward ambient product is contractive, and its adjoint composed
with the empty terminal polar frame is also contractive.  These are genuine
operator-norm statements on the named finite-S and source Sonin carriers.

## Directionality guard

Proof 519's endpoint-facing telescope follows the adjoint of the transition
product and keeps the actual step orientation visible.  The present product
is intentionally different from that endpoint-facing order:

```text
forwardAmbient(p :: S) = forwardAmbient(S) * T_(p,S),
forwardTransition(p :: S) = forwardTransition(S) * U_(p,S).
```

This order is what permits induction to consume the actual identity at the
current source step.  It must not be silently identified with the reverse
Julia-survivor product or with the metric transport product.

## Lean owners

```text
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSActualSchurForwardTransport.lean
ConnesWeilRH/Dev/
  CCM24FiniteSActualSchurForwardTransportAudit.lean
ConnesWeilRH/Source/CCM25Concrete.lean
```

## Verification contract

The direct source check and focused audit are run in the Ubuntu 24.04 WSL2
ext4 mirror.  The aggregate and full-repository builds must be run only after
the Windows source snapshot, audit, and aggregate import are byte-identical
to that mirror.

The audited declarations must use exactly
`[propext, Classical.choice, Quot.sound]`.  The source and audit must contain
no `sorry`, `admit`, or user axiom declaration.

This proof closes only source-forward product bookkeeping and contraction.  It
does not identify the forward dual coframe with the physical endpoint, prove
the missing actual/metric coherence residual is zero, establish the Gate 3U
uniform signed bound, prove the finite-S sign, supply Burnol's identity, or
prove `_root_.RiemannHypothesis`.
