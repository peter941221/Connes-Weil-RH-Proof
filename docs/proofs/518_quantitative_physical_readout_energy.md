# Proof 518: quantitative physical readout energy

## Result

The raw rectangular Schur boundary energy consumer now preserves the actual
operator norm of its physical readout.  For `C >= 0` and
`||readout|| <= C`, Lean proves

```text
sum_i ||readout (boundaryColumn (input e_i))||^2
  <= C^2 * sum_i ||input e_i||^2.
```

The source-facing combined physical right-energy theorem has the same form.
Its physical endpoint identity is unchanged and remains an explicit premise;
only the norm-one requirement has been generalized to an honest quantitative
bound.  The previous contraction theorem is still the `C = 1` use case.

## Why this matters

The complete Julia history is contractive, but a source-specific readout into
the common boundary carrier need not be contractive.  Squaring an unproved
norm-one assumption would understate the Gate 3U energy.  The new theorem
keeps the exact constant visible so a later producer can supply either a
uniform contraction or a larger, correctly propagated bound.

This does not construct the nonempty-family physical readout.  The existing
metric telescope still uses `normalizedPrimeEulerFrameTransport`, while the
physical cascade uses the parameterized `normalizedSchurFrame`; they are not
identified by definition.  The finite-S sign, Gate 3U, Burnol's identity, and
`_root_.RiemannHypothesis` remain open.

## Lean owners

```text
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSCombinedPhysicalEnergyGate.lean
ConnesWeilRH/Dev/
  CCM24FiniteSCombinedPhysicalEnergyGateAudit.lean
```

## Verification

Ubuntu 24.04 WSL2, isolated ext4 mirror, under the repository Lake lock:

```text
+------------------------------------------+-------+--------+
| target                                   | jobs  | result |
+------------------------------------------+-------+--------+
| direct source Lean check                 |   n/a | PASS   |
| focused axiom audit                      |  3296 | PASS   |
| CCM25Concrete aggregate                  |  3791 | PASS   |
| full repository                          |  3872 | PASS   |
+------------------------------------------+-------+--------+
```

The six audited declarations use exactly
`[propext, Classical.choice, Quot.sound]`.  The source and audit contain no
`sorry`, `admit`, or user axiom declaration.  Existing repository linter
warnings are unchanged.

Windows and WSL SHA-256 values match:

```text
B0C60F903AFD1D2EE5C3359BB521D6944B07EA43F10345D88C8DEEE62B5DA330
  CCM24FiniteSCombinedPhysicalEnergyGate.lean
313E15F39ED63F767BC02F51F660AD4F11A5211CD35BA6B8BB27905277586AC2
  CCM24FiniteSCombinedPhysicalEnergyGateAudit.lean
```
