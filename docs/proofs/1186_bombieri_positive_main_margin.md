# 1186 — Strict positivity of the Bombieri finite main term

## Status

**FORMAL support lemma; no P2 closure.**

For a nonzero Bombieri weighted eigenvector with `t > 0` and reciprocal
eigenvalue relation, `bombieriHMatrix_quadraticForm_pos_of_eigen` proves

```text
0 < Re <w, H(Γ;t) w>.
```

The proof combines the existing strict positivity of `bombieriWMass`, the
strict positivity of the reciprocal eigenvalue, and the exact
`lambda_mass_eq_KstarGram`/Hermitian-form readback.  This creates the positive
margin needed to dominate a sufficiently small same-owner spectral tail.

The theorem does not choose a cutoff and does not prove the required
Bombieri-to-`qw` residual identity.  Those remain the two analytic producer
obligations for P2.

## Acceptance

Focused batch `p2-positive-margin-r2.log` completed successfully (3665 jobs),
with no `error:` or `sorryAx`; the audit reports only
`[propext, Classical.choice, Quot.sound]`.
