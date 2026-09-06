# 1176 — Hermitian finite Bombieri matrix

Date: 2026-09-06

## Result

The finite Bombieri section-7 algebra now has the missing star layer:

```text
bombieriK_star, bombieriK_neg
          |
          v
bombieriKstar_star (real x,y,t)
          |
          v
bombieriH_star (real x,y,t)
          |
          v
bombieriHMatrix_isHermitian (Fin n → Real, repeated ordinates allowed)
```

The proofs are exact complex identities.  The diagonal case of the matrix
theorem uses entry self-conjugacy; the off-diagonal case combines that fact
with the already certified symmetry of `H`.

## Evidence

The focused official build for the three leaves and their audits completed in
1920 jobs with no `error:` lines.  Every new audit declaration prints exactly
`[propext, Classical.choice, Quot.sound]`; the log contains no `sorryAx`.

## Boundary

This closes only a finite Hermitian-structure prerequisite for the Bombieri
Line-B/C lane.  It does not prove positivity of the detector-specific P2
quadratic form, the same-owner identity `qw = λ · mass`, or RH.  The per-zero
finite certificate and the owner bridge remain explicit OPEN obligations.
