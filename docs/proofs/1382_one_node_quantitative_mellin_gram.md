# 1382 — One-node quantitative Mellin Gram lower bound

Date: 2026-09-13.

Status: FORMAL. This is the first finite-Gram subcase of N2beta component 2.
It does not prove a multi-node inverse, a smooth near-optimal interpolant, an
N1c margin, spectral nonnegativity, or RH.

## Formal owner and theorem

Leaf: `ConnesWeilRH/Dev/C1QuantitativeMellinGram.lean` with paired Audit.
It imports the axiom-clean L2 export of 1381 and remains on the genuine
`CompactLogTest` owner.

For a support window `(a,b)` and one Laplace node `s`, define the exact
diagonal Gram weight as the window integral of the exponential square weight.
For a prescribed value `y`, the required cost is `norm(y)^2 / weight`.

The theorem `oneNodeRequiredCost_le_compactLogL2sq` proves that every actual
compact-log test supported in that window and satisfying `laplaceAt f s = y`
has at least this squared L2 cost. Positivity of the exact weight remains an
explicit analytic premise.

`oneNode_noGo_of_budget_lt_requiredCost` turns a strict comparison between an
independently supplied budget and this lower bound into `False` for the SAME
test, support, node, and prescribed value. Its predicate wrapper
`oneNode_noGo_of_regime` prevents a regime assertion from being used without
the actual owner-side support/value/weight proofs.

The exact symbolic critical-line specialization is also formal:

```text
node real part = 0  ->  diagonal Gram weight = b - a
a < b               ->  diagonal Gram weight > 0
```

It uses no floating-point scan or sampled zeta zero.

## Evidence

Focused WSL runner logs: `1382_quantitative_gram_try3.log` and
`009_gram_quadratic_try14.log` (repository build-log naming; kept in the
Linux-side verification environment).

Acceptance: `Build completed successfully (3477 jobs)`, zero `error:` lines.
The paired audit prints all seven declarations with exactly
`[propext, Classical.choice, Quot.sound]` and no `sorryAx`.

## Boundary and next consumer

This result supplies a necessary-cost and exact no-go primitive. It cannot
produce an affordable correction because it has no multi-node Gram optimum or
upper construction. The next N2beta brick is therefore the finite-node
representer/Gram minimum-cost theorem, including a non-singular versus
rank-deficient split. Any later exact regime certificate must compare that
same multi-node lower cost with the N1c budget on the same assembled detector.

The configuration boundary is now FORMAL in the same leaf. A
`FiniteMellinInterpolationConfig` stores only a deduplicated `Finset` node
owner, window endpoints, target values, and base factors. The exact correction
target division is proved only under an explicit nonzero base-factor proof;
a zero base factor with nonzero target has a scoped no-correction theorem.
Thus later Gram/taper work cannot silently divide by a vanishing full-product
factor or merge incompatible constraints.

The finite-node Gram skeleton is also FORMAL: `finiteMellinGram` is
`Matrix.gram` of an explicitly supplied complex Hilbert representer family,
and `finiteMellinGram_isHermitian` proves its Hermitian law. The new
`finiteMellinGram_quadratic_eq_inner` identifies every complex Gram quadratic
expression with the inner product of the matching representer combination
with itself; `finiteMellinGram_quadratic_re_nonneg` proves its real part is
nonnegative. `finiteMellinGram_quadratic_re_pos_of_linearIndependent` proves
strict positivity for every nonzero coefficient under an explicit linear
independence proof. WSL try16 built 3547 jobs with zero errors; all fifteen
audit prints have exactly the standard three axioms and zero `sorryAx`.

The attempted ordered-matrix `PosDef` and `PosSemidef` shortcuts were rejected
because their API requires an ordered scalar and does not model complex
quadratic-form positivity. Strict positivity is now derived correctly from
linear independence. The next brick must prove that property for the actual
windowed Mellin representers and treat a nontrivial kernel as the
rank-deficient branch; it must not coerce the complex Gram matrix into an
invalid real-order claim.

For that rank-deficient branch, `FiniteMellinKernelCompatible` records the
precise necessary target condition: every right-kernel vector of the finite
Gram matrix must have zero conjugate-dot-product with the target vector.
Try19 is green (3547 jobs, zero errors, zero `sorryAx`). This does not supply
a pseudoinverse or solve the compatibility condition for an orbit.

The finite normal-equation predicate `FiniteMellinGramSolvable` is now also
formal. Its theorem `FiniteMellinGramSolvable.kernelCompatible` proves that a
solution forces the stated compatibility condition, using the actual
two-coefficient Gram inner-product identity. Try23 is green (3547 jobs, zero
errors, zero `sorryAx`). It does not establish the converse pseudoinverse
construction or an orbit-specific solve.

## Abstract minimum-norm core (try30, FORMAL)

Three theorems over an arbitrary supplied complex Hilbert representer family
`representer : cfg.Node → E` close the abstract lower-bound half of the
minimum-cost statement:

- `finiteMellinGram_mulVec_apply`: each normal-equation row of the Gram
  matrix is exactly the corresponding moment of the synthesized vector,
  `(finiteMellinGram cfg representer mulVec coeff) i =
  ⟪representer i, finiteMellinSynthesis representer coeff⟫`. The proof is a
  `trans` chain of `Finset.sum_congr` steps because `rw` higher-order
  matching is capture-sensitive when the synthesis sum's binder shadows the
  free node variable.
- `finiteMellinSynthesis_momentMatches_of_isSolution`: any coefficient vector
  solving the normal equations makes the synthesized vector realize every
  prescribed target value exactly.
- `norm_sq_finiteMellinSynthesis_le`: the abstract Pythagoras bound — if a
  vector matches all moments and the coefficients solve the normal equations,
  then the synthesized vector's squared norm is at most that vector's. The
  cross inner product collapses to the real squared norm `(‖s‖ : ℂ)^2`
  through `RCLike.ofReal_pow`/`RCLike.ofReal_re`, and `norm_sub_sq (𝕜 := ℂ)`
  plus `linarith` finishes.

So within the abstract class, a solved Gram synthesis is a certified
minimum-cost moment-matching vector: its cost lower-bounds and simultaneously
attains the class optimum. Combined with
`finiteMellinGram_quadratic_re_pos_of_linearIndependent`, this is the full
abstract content of the ladder's "minimum L2 cost" item.

Evidence: `009_gram_minnorm_try30.log` — `Build completed successfully
(3547 jobs)`, zero `error:` lines, zero `sorryAx`, zero Dev warnings; all 24
`#print axioms` outputs are exactly `[propext, Classical.choice,
Quot.sound]`.

Scope caveat: this is abstract finite-Hilbert machinery over a supplied
representer family. It does not instantiate the windowed Mellin representers
on the `CompactLogTest` owner, does not prove their linear independence or
resolve the rank-deficient branch for an actual orbit, constructs no inverse
or pseudoinverse, and claims no feasibility. The next brick is that
instantiation — the lightest candidate path routes each nodal dual bound
through the 1381 window Cauchy–Schwarz brick and avoids the `Lp`
a.e.-quotient API.

## Concrete window Mellin representers (component 2c core, FORMAL)

That instantiation now exists in the paired leaf
`ConnesWeilRH/Dev/C1WindowMellinGram.lean` with
`ConnesWeilRH/Dev/C1WindowMellinGramAudit.lean`. For a window `(a,b)` and a
finite node family `nodes : ι → ℂ`, the representer of node `s` is
`x ↦ exp(conj(s) · x)` and the concrete Gram entry is the window integral

```text
windowExpGram a b s t = ∫ x in a..b, exp((s + conj t) * x) ∂volume
```

of the pairing exponent. The leaf proves, on the genuine `CompactLogTest`
owner and with no `Lp`/`MemLp` API:

- the Hermitian law `star (windowExpGram a b s t) = windowExpGram a b t s`;
- the `laplaceAt` window-restriction identity (indicator trim under
  `a < b` and `Function.support f.test ⊆ Ioo a b`);
- the concrete quadratic identity: the cast window integral of
  `‖∑ i, coeff i * exp(conj(node i) · x)‖²` is exactly the plain-bilinear
  Gram quadratic `star coeff ⬝ᵥ (windowExpGramMatrix a b nodes).mulVec
  coeff` — the owner-side instance of `finiteMellinGram_quadratic_eq_inner`;
- the dual bound `‖∑ i, star(coeff i) * laplaceAt f (node i)‖² ≤
  (that real window integral) * compactLogL2sq f`, assembled through the
  1381 raw-interval Cauchy–Schwarz brick;
- the deliverable cost comparison `windowExpGram_cost_le_compactLogL2sq`:
  whenever `laplaceAt f (node i) = y i` for all `i` and the coefficient
  vector solves the normal system `G · coeff = y`, then
  `(star coeff ⬝ᵥ y).re ≤ compactLogL2sq f` — the concrete shadow of the
  abstract minimum-norm theorem above;
- both closed forms of a window Gram entry: under the explicit
  nonzero-frequency premise the exact quotient
  `(exp((s+conj t)·b) - exp((s+conj t)·a)) / (s + conj t)` (fundamental
  theorem via `integral_eq_sub_of_hasDerivAt`), and under the zero-frequency
  premise the window width `b - a` — the critical-line diagonal.

Evidence: `009_window_gram_build1.log` — `Build completed successfully
(3548 jobs)`, zero `error:` lines, zero `sorryAx`, zero Dev warnings; all
14 audit prints are exactly `[propext, Classical.choice, Quot.sound]`.

Scope: this states no linear independence or rank fact for the exponential
family, constructs no inverse or pseudoinverse, asserts no existence of a
solved system for any actual orbit, and registers no numeric margin. The 2c
tail — Vandermonde-style independence of the exponentials for distinct nodes
(or the rank-deficient branch), the configuration-specialized application
feeding one assembled detector's solved system through this comparison, and
the abstract/concrete identification — remains before component 3 may
consume any number. The N1c joint-feasibility interface (1379) can now
quote a machine-checked concrete lower cost.
