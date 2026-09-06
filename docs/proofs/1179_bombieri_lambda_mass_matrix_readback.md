# 1179 — Bombieri `lambda * mass` matrix readback

Date: 2026-09-06

## Result

For a finite Bombieri eigen-relation
`w = Λ • (H(Γ;t) *ᵥ w)` and reciprocal identity `λΛ = 1`, the theorem
`lambda_mass_eq_bombieriHMatrix_quadraticForm` proves

```text
(λ : ℂ) · ofReal(mass) = star(w) ⬝ᵥ (H(Γ;t) *ᵥ w).
```

Combined with record 1178, the right-hand side is a certified nonnegative
real-cast finite quadratic form for positive `t`.

## Boundary

This is still finite-owner algebra.  It does not prove the same-owner
identification `qw g = λ · mass`, construct detector-specific finite data, or
close P2/RH.

## Evidence

The focused official build completed in 2684 jobs with no `error:` lines or
`sorryAx`; all three declarations in the audit use only
`[propext, Classical.choice, Quot.sound]`.
