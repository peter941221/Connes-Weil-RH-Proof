# Proof 523: concrete normalized graph-support readback

## Result

Proof 522 named the complementary graph-support defect for an abstract
projected colligation.  This module transports that exact ledger to the
actual `PrimeEulerProjectedJuliaInput` used by the finite-S Schur cascade.

For a concrete input, define the upper graph-action operator and its defect by

```text
canonicalGraphActionUpper(data)
  = (eulerGraphAction graphCosine graphSineCanonical).1

canonicalGraphSupportDefect(data)
  = (1 - projection) * graphCosine.
```

Lean proves the unnormalized split

```text
canonicalGraphActionUpper(data)
  = schurFrame(graphCosine) + canonicalGraphSupportDefect(data).
```

The old projection deletes the defect exactly:

```text
projection * canonicalGraphSupportDefect(data) = 0

projection * canonicalGraphActionUpper(data)
  = schurFrame(graphCosine).
```

After the actual prime normalization, the source-facing identity is

```text
normalizedCanonicalGraphActionUpper(data)
  = normalizedSchurFrame(data)
    + normalizedCanonicalGraphSupportDefect(data).
```

This is a concrete carrier alignment result.  It does not estimate or
annihilate the defect, identify it with the physical post-Q remainder, prove
the family-uniform Douglas producer, close Gate 3U, prove the finite-S sign,
provide Burnol's identity, or prove `_root_.RiemannHypothesis`.

## Lean owners

```text
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSActualSchurGraphSupportDefectReadback.lean
ConnesWeilRH/Dev/
  CCM24FiniteSActualSchurGraphSupportDefectReadbackAudit.lean
ConnesWeilRH/Source/CCM25Concrete.lean
```

The source and audit contain no `sorry`, `admit`, or user axiom declaration.
The audited declarations are expected to use only the repository baseline
`[propext, Classical.choice, Quot.sound]`.

## Verification

Ubuntu 24.04 WSL2 verification completed after copying the Windows source of
truth to the ext4 mirror:

```text
+------------------------------------------+-------+--------+
| target                                   | jobs  | result |
+------------------------------------------+-------+--------+
| focused axiom audit                      | n/a   | PASS   |
| CCM25Concrete aggregate                  | 3796  | PASS   |
| full repository                          | 3877  | PASS   |
+------------------------------------------+-------+--------+
```

The existing repository linter warnings and the WSL localhost-proxy notice
remain external to this proof.  The three Lean files were byte-identical
between Windows and WSL2:

```text
EDBB4712E0702DC42DEA71D68297BAAD6A02078B0B3D7F0BFF1F2E7447AD3D70
  ConnesWeilRH/Source/CCM25Concrete.lean
9F832EBFE5CEEC74155BC3D4784D3EF41BA92B1928164EF4725265E563173090
  ConnesWeilRH/Source/CCM25Concrete/CCM24FiniteSActualSchurGraphSupportDefectReadback.lean
91F6D90563EF1F63CCE06F7DA6013A9576E4900122EACE145F92257126B9AA17
  ConnesWeilRH/Dev/CCM24FiniteSActualSchurGraphSupportDefectReadbackAudit.lean
```

The finite-S sign, physical post-Q remainder identification, family-uniform
Douglas producer, Gate 3U, Burnol's identity, and
`_root_.RiemannHypothesis` remain open.
