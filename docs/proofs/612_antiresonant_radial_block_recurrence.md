# Proof 612: antiresonant radial block recurrence

## Result

Let `E` be the genuine radial support projection, let `U` be translation by
`log(p)`, and set

```text
V = E U E,
C = (I - E) U E.
```

Proof 612 defines bounded readouts recursively by

```text
B_0     = I - E,
B_(n+1) = C V^n E - B_n.
```

For every radial vector `u`, meaning `E u = u`, Lean proves

```text
B_n (I + U) u = C V^n u.
```

After dividing by the nonzero ambient-loss scale, the same identity reads
each block from the actual new-frame ambient-loss column.

## Cost

The recurrence has only linear operator-norm cost:

```text
||B_n|| <= n + 1.
```

This is important because the genuine Euler coefficient later contributes a
geometric factor `q_p^(n+1)`, which can pay for linear growth.

## Structure

```text
actual ambient-loss column
          |
          +--> B_0 --> C
          +--> B_1 --> C V
          +--> B_2 --> C V^2
          +--> ...
```

The construction works on the radial range. It does not invert `I + U` on
the whole global-log carrier, where the antiresonant approximate-kernel
obstruction remains valid.

## Boundary of the result

Proof 612 does not show that the complete signed numerator is a summable
combination of these blocks. It does not construct the Bone 1 factor, close
Gate 3U, prove the finite-S sign, supply Burnol's identity, or prove RH.

## Verification

```text
focused source build: 3376 jobs, PASS
import-facing audit:  3377 jobs, PASS
audited declarations: 15
axioms: [propext, Classical.choice, Quot.sound]
```
