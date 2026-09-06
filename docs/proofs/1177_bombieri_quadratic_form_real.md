# 1177 — Reality of the finite Bombieri quadratic form

Date: 2026-09-06

## Result

For every finite ordinate map `gamma : Fin n → Real`, nonzero real `t`, and
complex vector `z`, the new theorem
`bombieriHMatrix_quadraticForm_im_zero` proves

```text
im (star z ⬝ᵥ (H(Γ;t) *ᵥ z)) = 0.
```

It is the standard Hermitian quadratic-form consequence of the formally proved
`bombieriHMatrix_isHermitian`; no distinctness assumption is used, so repeated
ordinates remain legal.

## Boundary

The theorem supplies only reality.  It does not prove that the quadratic form
is nonnegative, does not identify it with `qw g`, and does not construct the
per-zero finite certificate required by the P2 producer.

## Evidence

The focused Gamma/Audit build completed in 2357 jobs with no `error:` lines or
`sorryAx`; the audit output uses only
`[propext, Classical.choice, Quot.sound]`.
