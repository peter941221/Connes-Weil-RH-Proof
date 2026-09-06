# 1178 — Finite Bombieri quadratic-form positivity

Date: 2026-09-06

## Result

The new leaf `C1BombieriFiniteQuadraticBridge` proves the exact ownership
identity

```text
star w ⬝ᵥ (H(Γ;t) *ᵥ w) = bombieriKstarGram t Γ z,
w = (1/4 + γ²) z.
```

The existing 8.11–Wirtinger certificate then gives, for `0 < t`, a real number
`S ≥ 0` whose cast is this finite quadratic form.  No eigenvector assumption,
distinctness assumption, or numerical input is used.

## Boundary

This proves positivity only for the finite Bombieri matrix owner.  It is not a
proof that `qw g ≥ 0` on the healthy `CompactLog` owner, and it does not supply
the same-owner equality `qw = λ · mass` or the per-zero finite certificate.

## Evidence

The official focused build of the leaf and audit completed in 2683 jobs with no
`error:` lines or `sorryAx`; both new declarations audit to
`[propext, Classical.choice, Quot.sound]`.
