# Proof 477: finite-family-uniform fixed physical energy

## Result

The result is good: it removes the visible finite prime family from the first
absolute trace bound on Proof 476's complete operator. It does not yet close
Gate 3U or RH because the remaining fixed physical energy still needs an
explicit support--Sobolev polynomial bound.

Write

```text
B   = source quotient-band projection,
R   = source Sonin projection,
A_S = normalized finite-Euler inverse,
D   = the fixed complete three-branch Hilbert--Schmidt pair.
```

Proof 476 gives the exact same-object factorization

```text
completeCorner_S
  = (D bounded on the left by B and on the right by R A_S B).traceProduct.
```

All three maps are contractions:

```text
norm(B)       <= 1,
norm(R)       <= 1,
norm(A_S)     <= 1,
norm(R A_S B) <= 1.
```

Hilbert--Schmidt Cauchy--Schwarz is applied only after the complete physical
pair has been formed. Lean therefore proves

```text
abs(trace(completeCorner_S))
  <= sqrt(sum_i norm(D.left e_i)^2)
     * sqrt(sum_i norm(D.right e_i)^2).
```

The right side contains no `FinitePrimePowerFamily`. In particular, this
bound uses the legal `sum_i sum_omega` ordering from Proof 476 and never
exchanges the basis and renewal sums.

```text
 +---------------- finite-S dependence ----------------+
 |                                                     |
 |  D --left B--> complete pair <--right R A_S B-- D  |
 |       |                         |                   |
 |       +------ contraction ------+                   |
 |                    |                                |
 +--------------------v--------------------------------+
          fixed left energy * fixed right energy
```

## Boundary

Proof 477 does not assert that the fixed energy is already bounded by the
canonical support-radius polynomial. The remaining analytic task is now
finite-family-free: combine the compact outer and reflected kernel bounds
with a quantitative bound for the fixed prolate Hilbert--Schmidt factor,
without replacing the exact operator identity by a renewal total-variation
estimate.

No trace/renewal exchange, atomwise trace sum, finite-S sign, negative-owner
integration, Burnol identity, or `_root_.RiemannHypothesis` is proved here.
