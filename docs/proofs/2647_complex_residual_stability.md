Record 2647: complex list helpers + complex residual stability GREEN (2624 GO-route brick 2)
Date: 2026-10-10

Result

Positive: `ConnesWeilRH/Dev/C1RouteAComplexResidualStability2647.lean`
built green (0 error, 0 `uses sorry`, 0 module warning) and lands the
generic complex layer the off-diagonal panel tables instantiate.

§1-2 complex list helpers over `List RatPair2542` (the certified 2542
pair layer — coefficients are exactly the engine's rational pairs):

    complexPolyAdd2647 / complexPolyScale2647 / complexPolyMul2647
    complexPolyDerivative2647 / complexPolyEvalRat2647
    complexPolyAbsBound2647 (coefficient-moduli bound, |re| + |im|)
    complexPolyEval2647 : List RatPair2542 -> R -> C (embedPair2542 Horner)

with the embed-hom theorems (`_add`, `_scale`, `_mul`), the replay
bridge `_cast` (rational-point evaluation equals the pair Horner),
`_hasDerivAt` (Horner derivative structure), `_abs_le` (norm bounded
by the |re|+|im| coefficient table — the recorded over-approximation
of record 2624), and `embedPair_zero2647`.

§3 the complex residual stability theorem — the complex analog of
`exp_polynomial_residual_stability2619`:

    complexExpPolynomialResidualStability2647
      hypotheses: polynomial 0 = 1, HasDerivAt for phase/polynomial on
        the panel, residual bound
        |norm (poly' - phase' * poly)| <= residualUpper,
        and the variation on the REAL part only:
        |(phase t - phase 0).re| <= variation
      conclusion:
        norm (exp (phase t - phase 0) - poly t)
          <= exp (2 * variation) * residualUpper * |t|

The real-part variation is the whole point: `Complex.norm_exp`
(norm (exp z) = exp z.re, Mathlib Trigonometric.lean:995) makes the
imaginary slope `i * psi * t` rotate without entering the error, which
is exactly the mechanism record 2624 prices the (0,3) panels with
(|exp(i psi u)| = 1). The proof mirrors 2619 line for line: the
adjusted function poly * exp(phase 0 - phase), its derivative via
`HasDerivAt.smul`/`HasDerivAt.comp` + `Complex.hasDerivAt_exp`, the
norm bound `Convex.norm_image_sub_le_of_norm_hasDerivWithin_le`
(generic in the ℂ codomain), and the exp-product cancellation.

Build evidence: first-green 42 s over the 3728-job graph after four
debug iterations (14 -> 7 -> 5 -> 0 errors), then a warning-hygiene
pass; final incremental recheck 1.9 s green, errors 0, `uses sorry` 0,
module warnings 0. No new axioms (pure Mathlib + the certified 2619 /
2542 layers).

Scope

This is the generic layer only — no panel table, no degree-55
coefficients, no off-diagonal claim. The generated tables plug into
`complexPolyEval2647` exactly the way the real tables plug into
`polynomialEval2621`. Producer GO, SourceRH, RH remain open.

Pipeline notes (new laws, AGENTS 2ci)

- Horner product is a VARIABLE product: `x * P x` needs
  `HasDerivAt.smul (hasDerivAt_id position) ih` with the simpa set
  `[Pi.smul_apply, id_eq, one_smul, Complex.real_smul, add_comm]`
  (`add_comm` is allowed in `simp only` as a permutative rewrite and
  fixes the sum order). `HasDerivAt.const_mul` is for CONSTANT
  coefficients only.
- `Complex.hasDerivAt_exp` composes with `HasDerivAt.comp` (HasDerivAt
  is generic in (K, E, F); the same K = R base serves ℂ-valued
  functions via `NormedAlgebra R C`).
- `sub_add_sub_cancel : a - b + (b - c) = a - c` (NOT = 0); follow it
  with `sub_self` when cancelling `a - a`.
- exp-product cancellation `(exp a) * (exp (-a)) = 1`: after
  `mul_sub` the term is right-nested `a * (b * c)` — insert
  `← mul_assoc` BEFORE `mul_right_comm` (which needs left-nested
  `a * b * c`).
- `linarith` does not split `|x|`: feed `abs_le.mp h` explicitly.
- `mul_le_mul'` requires `MulLeftMono` (fails on R); use the two-step
  `mul_le_mul_of_nonneg_right` / `_of_nonneg_left` chain instead.
- WSL /tmp logs can vanish between separate wsl.exe invocations (idle
  VM restart): copy the log to /mnt/c in the SAME invocation as the
  build, then grep the /mnt/c copy.
- Python patching of Lean files: avoid backslash escapes in
  replacement strings — `\|` was written literally and corrupted the
  Lean source.

Next obligations

1. Complex panel-table generator for the pilot entry (0,3): 190
   panels, degree 55, complex numerator
   `N_c = (beta + i*psi) * D - 60 * (c + t)` with the exp(i*psi*center)
   rotation carried at assembly (2624 pricing), using the 2622 batch
   machinery as the template.
2. Panel containment theorems consuming
   `complexExpPolynomialResidualStability2647` +
   `complexPolyEval2647_*`, then the 190-panel partition + monotone
   edge bound -> the (0,3) entry containment against the committed
   2597 rectangle.
3. Widen row 0 to all 27 non-cancelling columns; Producer GO,
   SourceRH, RH stay out of scope.
