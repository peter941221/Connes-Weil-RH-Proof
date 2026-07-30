# Proof 633: single-channel radial recovery

## Result

Proof 633 gives the renewed Bone 1 denominator a canonical readout onto the
earlier raw antiresonant channel.  In the physical operator order, Lean proves

```text
T_p^dagger L_p^dagger N_p^dagger = rho_p L_p^dagger.
```

Therefore

```text
Recovery_p = rho_p^(-1) T_p^dagger,
||Recovery_p|| <= 8,

Recovery_p (L_p^dagger N_p^dagger newFrame_(p,S))
  = L_p^dagger newFrame_(p,S).
```

Every genuine radial boundary block is now an exact readout of the renewed
column.  After summing the geometric recurrence before estimating, the
complete radial readout has the family-uniform bound

```text
||renewedAntiresonantRadialGeometricReadout|| <= 256.
```

## Derivation

No factors are exchanged.  The proof left-multiplies Proof 630's renewal
deviation by the forward transport and uses

```text
T_p^dagger N_p^dagger = rho_p I,
T_p^dagger - I = -sqrt(q_p) L_p^dagger.
```

Cancelling the nonzero `sqrt(q_p)` gives the ordered recovery identity.  The
existing raw radial readout costs `32`; composing it with the norm-`8`
recovery gives `32 * 8 = 256`.

```text
 renewed column B = L^dagger N^dagger frame
                    |
                    v  rho^(-1) T^dagger, norm <= 8
 raw column     L^dagger frame
                    |
                    v  geometric radial readout, norm <= 32
 complete radial boundary
```

## Boundary

This closes the denominator handoff for the radial boundary channel only.
It does not identify the complete second-support and prolate
reverse-intertwining defect with that radial boundary.  Estimating those
remaining branches separately would lose the signed covariance required by
Bone 1.

## Lean owners

```text
ConnesWeilRH/Source/CCM25Concrete/
  ...AntiresonantInteriorSingleChannelRadialRecovery.lean
ConnesWeilRH/Dev/
  ...AntiresonantInteriorSingleChannelRadialRecoveryAudit.lean
```

## Verification

```text
+--------------------------------------+-------+--------+
| target                               | jobs  | result |
+--------------------------------------+-------+--------+
| radial-recovery source               |  3402 | PASS   |
| focused eight-declaration audit      |     - | PASS   |
| CCM25Concrete aggregate              |  3909 | PASS   |
| full repository                      |  3990 | PASS   |
+--------------------------------------+-------+--------+
```

All eight audited declarations use exactly
`[propext, Classical.choice, Quot.sound]`.
