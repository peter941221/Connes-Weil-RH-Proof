# 3278 Route A rational Taylor weight generator

## Purpose

The diagnostic exponent is too large for a direct Taylor pin on the whole
window.  Range reduction changes the problem to a small argument:

```text
          y = sigma * center
                    |
                    v
             x = y / 60, |x| <= 1
                    |
                    v
       Taylor interval for exp(x)
                    |
                    v
       raise the interval to the 60th power
                    |
                    v
                 exp(y)
```

`C1RouteARationalWeightTaylor3278.lean` formalizes this bridge.  The
rational interval power is proved by induction using interval multiplication,
and `ratTaylorExp60_mem3278` applies `expTwoSided2676` followed by
`Real.exp_nat_mul`.

## Verification

The focused WSL2 ext4 build checks `lean-toolchain` and Lean `4.30.0`, then
builds the audit file.  The audited declarations report only:

```text
[propext, Classical.choice, Quot.sound]
```

This is a generic generator, not a completed numeric weight certificate.  The
remaining work is to choose rational Taylor endpoints and prove their literal
inequalities for each cell, then combine those weight intervals with the
phase, bump, and coefficient family rectangles.
