# Proof 660: non-polar cofactor collapse

## Result

Let

```text
I_(p,S) = T_(p,S) M_S - M_(p::S) T_(p,S)
```

be the one-sided polar/raw mismatch intertwinement. Proof 659's non-polar
cofactor initially contains two forward/reverse Schur factors. Proof 660 uses
both exact scalar pairings to collapse it to

```text
C_nonpolar_(p,S) = -I_(p,S)^* R_(p,S)^*.
```

The scalar-normalized forward transition recovers the mismatch:

```text
C_nonpolar_(p,S) (rho_p^(-1) T_(p,S))^* = -I_(p,S)^*.
```

Since the reverse transition is contractive and the normalized forward
transition has norm at most `8`, Lean obtains

```text
||C_nonpolar_(p,S)|| <= ||I_(p,S)||
                     <= 8 ||C_nonpolar_(p,S)||.
```

Extension through the actual new-frame adjoint preserves the cofactor norm
exactly.

## Bone 1A Reduction

The mismatch is the polar boundary minus the recombined raw quadratic row:

```text
I_(p,S) = PolarBoundary_(p,S) - RawIntertwining_(p,S).
```

Proof 660 proves the polar boundary bound

```text
||s_p^(-1) PolarBoundary_(p,S)|| <= 6 ||detector||.
```

Combining it with Proof 659's `48` bound yields the fixed conversions

```text
raw bound B
  -> complete Bone 1A bound 54 ||detector|| + B,

complete Bone 1A bound B
  -> raw bound 390 ||detector|| + 8 B.
```

Therefore Lean proves

```text
exists a route-uniform scaled complete-target bound
  <->
exists a route-uniform scaled raw-intertwining bound.
```

## Boundary

This is an exact reduction, not the missing bound. The active Bone 1A source
theorem is now one route-uniform estimate for the recombined raw quadratic
intertwining defect. Full Bone 1 additionally retains Proof 656's paired
two-step coboundary factor channel. Gate 3U, the finite-S sign, Burnol's
identity, and RH remain open.

```text
+--------------------------------------------------+----------+
| layer                                            | status   |
+--------------------------------------------------+----------+
| non-polar cofactor collapse                      | proved   |
| mismatch/non-polar norm equivalence, cost 8      | proved   |
| ambient extension norm equality                  | proved   |
| polar boundary scaled bound, constant 6          | proved   |
| complete/raw Bone 1A existence equivalence       | proved   |
| route-uniform scaled raw-row estimate             | open     |
| Proof 656 route-uniform two-step factors          | open     |
| Gate 3U / sign / Burnol / RH                     | open     |
+--------------------------------------------------+----------+
```

## Lean Owners

```text
ConnesWeilRH/Source/CCM25Concrete/
  ...AntiresonantInteriorNonpolarCofactorCollapse.lean
ConnesWeilRH/Dev/
  ...AntiresonantInteriorNonpolarCofactorCollapseAudit.lean
```

Verification in the Ubuntu-24.04 WSL2 ext4 mirror used the shared Lake lock:

```text
+--------------------------------------+-------+--------+
| target                               | jobs  | result |
+--------------------------------------+-------+--------+
| Proof 660 source                     |  3445 | PASS   |
| Proof 660 focused audit              |  3446 | PASS   |
| CCM25Concrete aggregate              |  3935 | PASS   |
| full repository                      |  4016 | PASS   |
+--------------------------------------+-------+--------+
```

All twenty audited Proof 660 theorems use exactly
`[propext, Classical.choice, Quot.sound]`. No `sorry`, `admit`, or user axiom
was added.
