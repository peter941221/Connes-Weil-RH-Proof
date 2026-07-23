# Proof 519: actual Schur cascade telescope

## Result

The source-owned actual Schur cascade now has an axiom-clean exact telescope.
For a step family `stepData`, Lean defines the ordered ambient and source
products, identifies the actual Julia survivor with the adjoint of the source
transition product, and expands the adjoint ambient product on the terminal
polar frame into a survivor term plus actual endpoint-facing boundary outputs.

The central identity is:

```text
actualAmbient(S)† * terminalFrame(S)
  = emptyFrame * actualTransition(S)†
    + sum actualBoundaryOutputs(S).
```

The source-owned endpoint is then defined with the same upper Euler scalar and
inverse-Gram square-root coordinate as the metric endpoint.  The existing
physical endpoint is related to it by an explicit residual:

```text
physicalEndpoint
  = actualSchurEndpoint + actualSchurEndpointResidual.
```

This is exact bookkeeping.  The residual is not proved to vanish.

## Directionality guard

The metric rectangular step has the orientation

```text
T† * oldFrame = newFrame * transition† + metricBoundaryDagger.
```

The actual source step instead stores

```text
T * newFrame = oldFrame * transition.
```

Therefore the metric theorem cannot be reused as if the two frame orientations
were definitionally equal.  Proof 519 defines the honest endpoint-facing
complement

```text
actualBoundaryDagger = T† * newFrame - oldFrame * transition†
```

and records its decomposition as the metric boundary dagger plus an explicit
coherence residual.  No physical common-boundary readout is inferred from this
identity.

## Lean owners

```text
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSActualSchurTelescoping.lean
ConnesWeilRH/Dev/
  CCM24FiniteSActualSchurTelescopingAudit.lean
ConnesWeilRH/Source/CCM25Concrete.lean
```

## Verification

Ubuntu 24.04 WSL2, isolated ext4 mirror, under the repository Lake lock:

```text
+------------------------------------------+-------+--------+
| target                                   | jobs  | result |
+------------------------------------------+-------+--------+
| direct source Lean check                 |   n/a | PASS   |
| focused axiom audit                      |   n/a | PASS   |
| CCM25Concrete aggregate                  |  3792 | PASS   |
| full repository                          |  3873 | PASS   |
+------------------------------------------+-------+--------+
```

The audited declarations use exactly
`[propext, Classical.choice, Quot.sound]`.  The source and audit contain no
`sorry`, `admit`, or user axiom declaration.  Existing repository linter
warnings and the WSL localhost-proxy notice are unchanged.

The finite-S sign, Gate 3U, the physical endpoint/readout coherence, Burnol's
identity, and `_root_.RiemannHypothesis` remain open.

Windows and WSL2 SHA-256 values match byte-for-byte:

```text
33D2380696C77A32F2621CC7002E665A0B116EF1755F95EF49C79B6401DEDF65
  CCM24FiniteSActualSchurTelescoping.lean
2F5DD7BEDCCE561F34F6E9DF56C480034896A2659F1E5FD2B40F4775A607DF3A
  CCM24FiniteSActualSchurTelescopingAudit.lean
5E6610631CDF08E507ECAF51CA9719483CD88A77F70A8FD0F85B6CA377850207
  CCM25Concrete.lean
```
