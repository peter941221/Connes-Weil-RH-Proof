# 1513 — Exact source-input energy reduction for S3

Date: 2026-09-17.

**Status:** formal, compiled in `C1G8R3GateAmbientNormalForm.lean` with its
paired audit leaf.  The theorem
`ConnesWeilRH.Dev.sourceGate_squareSum_iff_sourceInputEnergy` states, for
every selected owner, Sonin scale, and named source Hilbert basis,

```text
Summable (fun i => || J† C J (e_i) ||^2)
  iff
Summable (fun i => || C J (e_i) ||^2).
```

The proof is exact.  For each source basis vector, the full output splits
orthogonally into its Sonin component and its complement:

```text
|| C J e_i ||^2 = || J† C J e_i ||^2 + || (I - P) C J e_i ||^2.
```

The complement series is already supplied by
`selectedRoot_sourceSoninLeakage_sourceBasis_normSq_summable`.  The two
directions then follow from summable addition and nonnegative domination.

This is a route reduction, not an estimate: S3 still requires proving the
full detector energy on the included source carrier.  The ambient no-go
results in record 1512 remain active and are not used as a substitute.

**Acceptance:** `1612_gate_source_energy.log` has a successful footer, zero
`error:` lines, zero `sorryAx`, and the audit prints only
`[propext, Classical.choice, Quot.sound]`.
