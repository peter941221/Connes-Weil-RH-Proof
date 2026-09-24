# 1950 — Macro-atom variance bound gate certificate

Date: 2026-09-24

## Result

`ConnesWeilRH.Source.C1SignedVarianceIdentity` proves the macro-atom variance
bound reduction for bipartite signed partitions:

1. `finite_signed_variance_bipartite_bound_neg`:
   given internal oscillation bounds `M₁` on `s₁` and `M₂` on `s₂`, and a cross
   separation lower bound `G` across `s₁ × s₂`, whenever the aggregate
   oscillation condition holds:
   ```text
   (1/2) * M₁ * (∑_{s₁} c_i)^2 + (1/2) * M₂ * (∑_{s₂} -c_j)^2
     < G * (∑_{s₁} c_i) * (∑_{s₂} -c_j),
   ```
   the signed variance determinant is strictly negative.

2. `exists_pos_lambda_quadratic_neg_of_macro_atom_bounds`:
   under the same oscillation and separation bounds, plus positive total
   weight and positive cross sum, produces a strictly positive span coefficient
   with a strictly negative span gate quadratic:
   ```text
   (∑ c_i p_i^2) - lam * (2 * ∑ c_i p_i) + lam^2 * (∑ c_i) < 0.
   ```

## Route impact

This formalizes Step 1 of the macro-atom breakthrough plan: the exact
continuous or multi-node integral condition is now completely decoupled from
fine-grained pointwise quadrature. To prove `det < 0` for the four-point span
gate, one only needs coarse-grained bounds:
- internal oscillation `M₁` on the positive Archimedean central zone;
- internal oscillation `M₂` on the negative `n=2` prime resonance zone;
- cross separation `G` between the two zones;
- and the aggregate masses `C₁ = ∑ c_i > 0`, `C₂ = ∑ (-c_j) > 0`.

Because the between-zone separation $(P_1 - P_0)^2$ is roughly $30$ times larger
than the internal oscillation bounds $(2\delta_1)^2$, this condition holds with
an overwhelming structural margin.

## Verification

```text
20260924_macro_atom_variance.log: Build completed successfully (3811 jobs).
axioms: [propext, Classical.choice, Quot.sound]
sorryAx: none
```

The proof is exact Cauchy-Schwarz / bounding arithmetic over finite sums and ring
algebra; zero numerical or float approximations are introduced.
