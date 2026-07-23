# Proof 525: actual Schur-cascade graph physical readback

## Result

Proof 524 applies the normalized physical Euler transport to one concrete
graph frame.  Proof 525 identifies the projected part of that transport with
the actual one-step `suffixActualSchurFrameStep` used by the Schur cascade.

For the concrete input attached to `(p,S)`, Lean proves

```text
step.transport
  = normalizedPrimeEulerFrameTransport(p)
      * canonicalProjectedGraphFrame(p,S).
```

Consequently the unprojected physical graph response has the exact same-object
split

```text
normalizedPrimeEulerFrameTransport(p) * canonicalFullGraphFrame(p,S)
  = step.transport + physicalGraphSupportResidual(p,S).
```

Equivalently, the difference between the physical full-graph response and the
actual Schur step is exactly the physical support residual, and its norm is
bounded by the concrete graph-support-defect norm.

This is a cascade/carrier identification, not a family-uniform estimate.  It
does not identify the residual with the complete post-Q mismatch, construct a
uniform Julia co-defect factor, close Gate 3U, prove the finite-S sign, supply
Burnol's identity, or prove `_root_.RiemannHypothesis`.

## Lean owners

```text
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSActualSchurGraphPhysicalCascadeReadback.lean
ConnesWeilRH/Dev/
  CCM24FiniteSActualSchurGraphPhysicalCascadeReadbackAudit.lean
ConnesWeilRH/Source/CCM25Concrete.lean
```

## Verification

The Windows source snapshot was copied to a fresh Ubuntu 24.04 WSL2 ext4
mirror.  All Lake commands used the repository lock.

```text
+------------------------------------------+-------+--------+
| target                                   | jobs  | result |
+------------------------------------------+-------+--------+
| owning module                            | 3283  | PASS   |
| focused import-facing axiom audit        | 3799  | PASS   |
| full repository                          | 3879  | PASS   |
+------------------------------------------+-------+--------+
```

The focused audit reports only `[propext, Classical.choice, Quot.sound]` for
all four new declarations.  No `sorry`, `admit`, or user axiom was added.  The
existing repository linter warnings and the WSL localhost-proxy notice are
unchanged external noise.
