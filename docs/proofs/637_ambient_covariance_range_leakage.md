# Proof 637: ambient covariance range leakage

## Result

Proof 635 gave the sufficient ambient factorization

```text
Cov_(p,S) = L_p H_(p,S).
```

Proof 637 shows why this condition is stronger than the single-channel Bone 1
factor.  Given a single-channel factor `H`, define

```text
P_S       = newFrame_S newFrame_S^dagger,
Residual  = (I-P_S) N_p L_p H,
Leakage   = rho_p^-1 F_p Residual.
```

Lean proves

```text
Cov_(p,S) = L_p H - Leakage,

Leakage = 0  <->  Residual = 0,

Cov_(p,S) = L_p H  <->  Residual = 0.
```

The single-channel factor does not supply the extra range premise
`Residual=0`.

## Packed boundary identity

The leakage adjoint is the second coordinate of the canonical packed
physical factor:

```text
Leakage^dagger
  = -BoundaryRow_p(H) (I-P_S) F_p^dagger.
```

The existing bounds on the boundary row, range complement, and forward
transport give

```text
||Leakage|| <= 16 ||H||.
```

This bound records the cost of the intact moving-range channel.  It does not
make the channel vanish.

```text
 single-channel factor H
          |
          +--------------------------+
          |                          |
          v                          v
       L_p H             (I-P_S) N_p L_p H
          |                          |
          |                          v
          |               rho_p^-1 F_p residual
          |                          |
          +----------- minus --------+
                         |
                         v
                    Cov_(p,S)
```

## Boundary

The zero right-boundary leakage in the actual Schur step concerns the frame
intertwining input.  It does not imply `Residual=0` for the output of an
arbitrary Bone 1 factor.

Proof 635's ambient divisibility target remains sufficient and is not
equivalent to Bone 1.  Any ambient proof must retain `Leakage` or prove the
range residual vanishes.  The exact Bone 1 bottom remains Proof 636's
right-co-defect inequality.

## Verification

```text
+--------------------------------------+-------+--------+
| target                               | jobs  | result |
+--------------------------------------+-------+--------+
| ambient covariance range leakage     |  3401 | PASS   |
| focused seven-declaration audit      |     - | PASS   |
| CCM25Concrete aggregate              |  3911 | PASS   |
| full repository                      |  3992 | PASS   |
+--------------------------------------+-------+--------+
```

All seven audited declarations use exactly
`[propext, Classical.choice, Quot.sound]`.

## Lean owners

```text
ConnesWeilRH/Source/CCM25Concrete/
  ...AntiresonantInteriorAmbientCovarianceLeakage.lean
ConnesWeilRH/Dev/
  ...AntiresonantInteriorAmbientCovarianceLeakageAudit.lean
```
