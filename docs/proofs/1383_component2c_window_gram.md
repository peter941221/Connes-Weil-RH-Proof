# 1383 — Component 2c core: concrete window Mellin Gram and the solved-system cost

Date: 2026-09-13 (record written retrospectively; the leaf went green and was
committed on 2026-09-13 without a record file — this closes that documentation
gap, see [009](../map/009_n2beta_core_bone_completion_contract.md) item 1).

Status: FORMAL. This is the core half of N2beta component 2c in the 009
contract ladder item 1 (finite Hilbert interpolation on the selected support
window). It does not prove representer independence, Gram invertibility, a
feasibility certificate, or any numeric margin — those are the 2c tail
([1384](1384_component2c_independence.md)).

## What 2c core had to deliver

Record [1382](1382_one_node_quantitative_mellin_gram.md) proved the abstract
minimum-norm statement over an arbitrary supplied complex-Hilbert representer
family, and the one-node diagonal subcase. The missing half was the CONCRETE
owner-side instantiation: on a support window `(a, b)`, the evaluation
representer for the Laplace node `s` must be identified on the genuine
`CompactLogTest` register, the window Gram entry must be computed in closed
form, and the abstract minimum-cost statement must be converted into a cost
lower bound for actual `CompactLogTest` interpolants.

The representer identification comes from the register's own evaluation law
with the positive-character convention (`CC20YoshidaConvolution.lean:35-71`):

```text
laplaceAt f s = ∫ x in a..b, exp (s * x) * f.test x     (f supported in (a, b))
```

so the representer is the raw exponential `x ↦ exp (conj s * x)` and the
concrete Gram entry is `∫ x in a..b, exp ((s + conj t) * x)`.

## Formal owner and theorem anatomy

One leaf, paired with one audit.

`ConnesWeilRH/Dev/C1WindowMellinGram.lean` (14 public declarations):

- `windowExpGram (a b : ℝ) (s t : ℂ) : ℂ` — the window Gram entry as the exact
  interval integral of the pairing exponential `exp ((s + star t) * x)`;
- `windowExpGramMatrix` — the `Matrix ι ι ℂ` of a node family;
- `star_windowExpGram` — the Hermitian law `star (windowExpGram a b s t) =
  windowExpGram a b t s`;
- `laplaceAt_eq_windowIntegral` — the register evaluation restricted to the
  window for a supported test;
- `norm_sq_windowIntegral_eq_compactLogL2sq` — the window integral of the
  squared modulus equals the record-1381 accessor `compactLogL2sq`;
- `star_sum_exp` — the conjugate of a representer combination is the
  combination of conjugated exponentials;
- `windowExpGram_quadratic_eq_integral` — the concrete quadratic identity: the
  Gram quadratic form is exactly the window integral of the squared modulus of
  the representer combination;
- `integral_norm_sq_cast`, `integral_norm_sq_re` — the cast/real-part bridge
  between the `ℂ`-valued and `ℝ`-valued integral spellings;
- `windowDual_integral_le` — the raw-interval Cauchy–Schwarz dual bound;
- `windowDual_le` — the `CompactLogTest`-side shadow of the record-1382
  abstract minimum-norm theorem;
- `windowExpGram_cost_le_compactLogL2sq` — **the deliverable**: every test
  whose moments factor through a solved Gram system pays at least the real Gram
  quadratic cost,

  ```text
  (star coeff ⬝ᵥ y).re ≤ compactLogL2sq f
  ```

- `windowExpGram_of_ne_zero` — closed form at nonzero frequency,
  `(e^{(s+conj t)b} - e^{(s+conj t)a}) / (s + conj t)` under the explicit
  nonzero premise;
- `windowExpGram_of_zero` — closed form at zero frequency: the width `b - a`
  (the critical-line diagonal of record 1382).

## Why the proof shape is right (first principles)

The whole leaf stays on raw interval integrals plus the record-1381 window
Cauchy–Schwarz brick. The `Lp`/`MemLp` a.e.-quotient API is deliberately not
touched: it would replace a genuine `ℝ`-valued integral by an equivalence
class and lose the pointwise damped-mass bookkeeping that the later taper and
Young steps need.

The scope note is the important part. The deliverable is conditional on a
SOLVED Gram system — it is a cost comparison, not an existence or
invertibility claim. That is what makes the 2c tail necessary and what keeps
an unjustified inverse out of the construction: no `G⁻¹` appears here.

## Evidence

Focused WSL runner logs (repository build-log naming, kept in the Linux-side
verification environment): probes `009_window_gram_probe2.log` through
`009_window_gram_probe7.log`, acceptance `009_window_gram_build1.log`, audit
`009_window_gram_audit1.log`.

Acceptance log read back on 2026-09-13 (this record's writing pass):

```text
Build completed successfully (3548 jobs).
^error: lines = 0     sorryAx = 0     'Quot.sound' prints = 14
```

14 prints = the 14 declarations of `C1WindowMellinGramAudit.lean`, each exactly
`[propext, Classical.choice, Quot.sound]`.

Trap ledger forwarded to the project AGENTS §7b: `λ` is not a legal identifier
character in Lean 4; the RCLike-vs-Complex cast split (`rw` cannot cross it,
term mode can); a type ascription on an integral PROPAGATES the expected type
into the integrand; a bare `↑t` inside `‖↑t‖ ^ 2` can resolve to the identity
coercion `ℝ → ℝ`.

## Boundary and next consumer

FORMAL lane only: no independence, no invertibility, no existence, no
feasibility, no decay rate, no orbit instantiation, no numeric digit, no RH.

The consumer is the 2c tail
([1384](1384_component2c_independence.md)): it proves the exponential family
independent on any open window, derives trivial kernel and hence `IsUnit` of
the concrete window Gram for distinct nodes, and instantiates the deliverable
above at the inverse solve, certifying the record-1379 quantity
`K_loc = y* G⁻¹ y` as a machine-checked lower bound of `compactLogL2sq f`.
