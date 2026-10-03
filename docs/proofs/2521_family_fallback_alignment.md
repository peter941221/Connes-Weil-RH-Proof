# Record 2521 — align the production fallback with its actual price

The 2516 non-safe branch was `ownerWeightedCurvatureL1_2480 sigma R`:
one global `exp(|sigma| R)` multiplied the sum of the three derivative
budgets. The 2517 script instead priced the sum of family-weighted budgets,
using `exp(|sigma| r_i)` inside that sum. Consequently the 2517 number was
not a price of the expression in the 2516 theorem, and the 2519 payload
could not discharge its old fallback premise. Neither old conditional
theorem asserted that this premise had been proved.

`C1RouteAExpFamilyFallback2521.lean` supplies the priced rule for the same
fixed 2463 midpoint-coefficient function. It reuses the existing 2488
family derivative theorem, including the support boundary and exterior
zero-extension proof, then sums the family bounds. The safe range remains
196..443 and uses the unchanged 2514 exponential upper. The other 392 cells
now use `ownerFamilyL1SumCurvature2488`. The new pointwise bound is attached
to the full 640-cell strip consumer and to a table comparison theorem.
The 2516 definition and 2519 payload are preserved as historical objects.

The control in `scripts/routea_fallback_reprice_2521.py` reproduces the full
2517 JSON in the same run without overwriting it, checks the 640 rational
2519 entries at both signs, and binds all 30 input families to the actual
2460 Lean literals. It separately evaluates the old global fallback and
the family fallback through the scalar exponential expression. Its evidence
is `results/2521_fallback_reprice.json`; numeric prices remain external.

This repairs a bound on the same owner, not the owner's coefficients,
support, gate lambda, or visible-prime set. It makes no producer or RH claim.
The next record proves the replacement fallback table entries in Lean.

Reproduction from an up-to-date Linux build mirror:

```sh
python3 scripts/routea_fallback_reprice_2521.py
lake build ConnesWeilRH.Dev.C1RouteAExpFamilyFallback2521Audit
```

Use the repository resource runner for execution. No 2271 inventory-bound
source was changed; the 2267 replay and its manifest are not reissued.
