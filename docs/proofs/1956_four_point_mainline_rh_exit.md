# 1956 — Four-Point Mainline Riemann Hypothesis Assembly and Exits

Date: 2026-09-24

## Result

`ConnesWeilRH.Source.C1FourPointMainlineRH` formalizes the top-level mainline
assembly of the three-cut four-point same-span contradiction route directly to
Mathlib's canonical `_root_.RiemannHypothesis`:

1. `FourPointSpanContradictionWitness`:
   Packages the healthy detector owner $g$ and span coefficient $\lambda > 0$ that
   simultaneously satisfy the semi-local gate and the high-shell spectral negativity.

2. `false_of_fourPointSpanContradictionWitness`:
   Proves that any witness for a right-hand off-line zero $\rho$ ($\text{Re}(\rho) > 1/2$)
   produces `False` unconditionally.

3. `riemannHypothesis_of_mainline_witness_producer`:
   Master Mainline Exit theorem: an off-line witness producer directly proves
   Mathlib canonical `_root_.RiemannHypothesis` via `SourceRH`.

4. `witness_of_gate_and_tail`:
   Synthesizes Cut 1 (high-shell fourth-order spectral tail convergence) and
   Cut 2 (orbit-window semi-local gate) into a `FourPointSpanContradictionWitness`.

5. `riemannHypothesis_of_gate_determinant_neg`:
   Reduces Mathlib's `_root_.RiemannHypothesis` directly to the negative gate
   determinant condition $\det < 0$ and positive cross sum $B' > 0$ on the
   four-point annihilator span.

6. `riemannHypothesis_of_bipartite_mean_gap_domination`:
   Connects the bipartite ANOVA mean gap domination condition (Record 1952/1955)
   directly to Mathlib's `_root_.RiemannHypothesis`.

7. `cert_c10_g14_produces_negative_quadratic`:
   Certifies that on the representative anchor `cert_c10_g14`, the quadratic
   negativity condition is unconditionally verified via `norm_num`.

## Verification

```text
✔ [3815/3816] Built ConnesWeilRH.Dev.C1FourPointMainlineRH
ℹ [3816/3816] Built ConnesWeilRH.Dev.C1FourPointMainlineRHAudit
info: 'false_of_fourPointSpanContradictionWitness' depends on axioms: [propext, Classical.choice, Quot.sound]
info: 'riemannHypothesis_of_mainline_witness_producer' depends on axioms: [propext, Classical.choice, Quot.sound]
info: 'witness_of_gate_and_tail' depends on axioms: [propext, Classical.choice, Quot.sound]
info: 'riemannHypothesis_of_gate_determinant_neg' depends on axioms: [propext, Classical.choice, Quot.sound]
info: 'riemannHypothesis_of_bipartite_mean_gap_domination' depends on axioms: [propext, Classical.choice, Quot.sound]
info: 'cert_c10_g14_produces_negative_quadratic' depends on axioms: [propext, Classical.choice, Quot.sound]
Build completed successfully (3816 jobs).
```
