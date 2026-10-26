# Route-B envelope-to-pin bridge (record 3113)

Status: completed consumer adapter. This record does not prove the envelope
inequalities, `hgate24`, the spectral prefix bound, SourceRH, or RH.

The theorem
`fourPointContradictionRowBPoweredSeed_of_lowRungEnvelopePins3113` replaces
the three direct powered-seed cardinal-sum pin hypotheses by three quantified
upper bounds on the low-rung envelope from record 3112:

```text
envelope(targets, 1)                 <= wired Q
|t/(2*pi)|^4 * envelope(targets, 1)  <= wired C4
|t/(2*pi)|^2 * envelope(nodes, y)    <= wired C2
```

The proof applies the analytic envelope pointwise, multiplies by the
nonnegative frequency weights for the C4/C2 lanes, and feeds the resulting
three cardinal pins into the existing powered-seed same-owner contradiction.
The gate and prefix hypotheses remain visible and unchanged.

Verification used Linux ext4 with direct Lean source compilation and explicit
`.olean` output for the audit import. The theorem has exactly
`[propext, Classical.choice, Quot.sound]` and no `sorryAx`.

The next numerical/formal target is now sharply scoped: prove the three
envelope inequalities over the complete strip and full frequency line. Until
that replay is kernel-checked, this bridge is only a transport theorem.

Scope correction (3115): the conditional theorem is valid, but its
four-rung C2 envelope premise cannot close on the fixed 56-node correction
owner. Record 2729 already establishes the residual degree 17 obstruction.
The correct continuation uses a higher-order exterior arm together with
the low-rung compact-interval bound. It does not attempt to discharge the
impossible full-line four-rung envelope premise.
