# 966 - Wall-A 1.4 residual: explicit plan to close arch(witness^2) != 0

Date: 2026-08-10.  Status: actionable plan for the single surviving analytic
step (docs/965).  Not a proof yet; this is a作战路线 for a dedicated session.
RH NOT claimed.

## Target

For the explicit self-created test `witnessTest = unitFourierCoreBumpSchwartz`
(even, smooth, compact in `[-1,1]`, `test(0) = 1`), prove in Lean

    (HealthyArchData.healthySymbols).archimedeanTerm
      (healthySymbols.convolutionStar witnessTest witnessTest) != 0

which by docs/965 refutes the healthy-carrier Wall-A 1.4.

## Definitions to bind

`arch = (log(4*pi)+gamma) * Re((f*f)(0)) + I`

- `(f*f)(0)` = L2 norm squared via `convolutionSquare_zero_eq_integral_normSq`
  (already proven in the library).
- `I = 2 * Int_{y>0} ( e^(y/2) * h(y) - (f*f)(0) ) / (e^y - e^(-y)) dy ` with
  `h(y) = real part of the convolution square `(f*f)(y)`, even, nonnegative.

## Known library assets (verified in-tree)

- `convolutionSquare_zero_eq_integral_normSq`, `..._zero_re_nonnegative`,
  `..._zero_im` (CompactLogConvolution).
- `SelectedArchimedeanIntegrability`: integrability, `eventually_archimedeanIntegrand_eq_tail`,
  `archimedeanIntegrand_isBigO_exp_neg` (decay at infinity).
- `archimedeanNumerator_zero`, `archimedeanDenominator_pos`,
  `archimedeanIntegrand_im_eq_zero`.

## Two-part lower-bound strategy for `arch > 0`

Write `Lambda = log(4*pi)+gamma > 0`, `A = Re((f*f)(0)) > 0`, and
`arch = Lambda*A - 2*(J_near + J_tail)` with the integral split at support radius `R`.

### Part 1 (tail `y >= R`): provable now
- On `y >= R` the convolution is `h(y) = 0` (compact support), so the integrand is
  `- (f*f)(0) / (e^y - e^(-y))`.
- `Int_R^inf 1/(e^y-e^(-y)) dy = -ln(tanh(R/2))` (finite), so `J_tail` is a known
  negative constant proportional to `A`.
- The assembly lemmas in `SelectedArchimedeanIntegrability` already cover the decay;
  only the closed-form antiderivative for the tail integral is needed.

### Part 2 (near `y in [0,R]`): the real work — explicit pointwise bound
- Need pointwise control on `e^(y/2)*h(y) - h(0)` on `[0,R]`.
- `h = f*f` is even, nonnegative, `h <= A = h(0)`; and `e^(y/2) <= e^(R/2)`.
- Near `y=0`: the integrand is bounded by `O(A)` (numerator vanishes like `A*y/2`,
  denominator `e^y-e^(-y) ~ 2y`), so split `[0,eps]` and `[eps,R]`.

### Decisive obstacle (verified)
Mathlib `ContDiffBump` (used by `witnessTest`) exposes only
`nonneg`, `le_one`, `one_of_mem_closedBall`, `support` — NO pointwise numeric
bounds and no `h(y) <= h(0)` / Lipschitz control.  Closing Part 2 therefore
requires one of:

1. building a concrete bump the author fully controls (see Recommendation), or
2. importing the internals of `ContDiffBump` (large, exact-definitional work).

## Recommendation: an explicit bump the author controls

Do not fight the abstract `ContDiffBump`. Build a concrete smooth compact bump `f`
with exact pointwise bounds, e.g. even, non-negative, compact in `[-1,1]`:

    f(x) = exp(-1/(1-x^2))   if |x| < 1,  else 0

(smooth zero-extension, flat at |x| = 1, so `f` is C-inf and compact). Then:

- `(f*f)(0) = ||f||^2 (L2)`, and a concrete lower bound `||f||^2 >= A0 > 0` from
  `f >= 1/e` on `[-1/2,1/2]`.
- `h(y) = f*f(y)` is explicit and even; bound `|h(y)-h(0)|` pointwise on `[0,R]`
  using Lipschitz / integrable control, giving a computable `J_near` bound.
- Assemble `arch = (Lambda)*A - 2*(J_near + J_tail); if `2*(J_near+|J_tail|) < Lambda*A0`
  then `arch > 0`, done, plug into `healthy_target_refuted_of_arch_ne_zero`.

This is the only closing-chance path. Timebox: a dense multi-hour Lean session,
best run as a dedicated follow-up.

## Milestones for the dedicated session

1. Build the concrete `f` above as a `CompactLogTest` (compact, smooth, even).
2. Prove `(f*f)(0) = ||f||^2` and `||f||^2 >= A0 > 0`.
3. Prove the tail bound (Part 1).
4. Prove the near bound (Part 2), all exact.
5. Assemble `arch = Lambda*A - 2*(J_near + J_tail) > 0`; feed into
   `healthy_target_refuted_of_arch_ne_zero`.

RH not claimed.  Cross refs: docs/965, 963, 964, 958.
## UPDATE (2026-08-10): numeric evidence for the exact witness — target is REAL and positive

Verified with probe `docs/proofs/967_wall_a14_witness_arch_probe.py`
(FFT convolution of `smoothTransition(2-2|x|)`, exact tail antiderivative):

```
A  = (f*f)(0) = ||f||^2     = 1.405705
C  = log(4*pi)+gamma         = 3.108240
I(0..R)  R=2 (compact part)  = -0.672917
I(tail, y>2, exact)          = -0.765664   (= 2*A*ln tanh(R/2))
I total                      = -1.438580
arch = C*A + I               = +2.930689   (> 0)
|I|/A                        = 1.0234      (need < C = 3.1082)
headroom C*A - |I|           = +2.930689
```

So the single surviving scalar is NOT borderline: on the exact lean witness the
arch term is `+2.93`, and an integral bound `|I| < C*A` (headroom ~3x) suffices
to conclude `arch > 0 != 0` and feed `healthy_target_refuted_of_arch_ne_zero`.

### Sharpened 3-term split (replaces the crude 2-part split)

`arch = C*A + I` with

    I = 2*Int_0^R ( e^(y/2) r(y) - A )/(e^y - e^(-y)) dy
        + 2*A*ln(tanh(R/2))                       (exact tail, r=0 for y>R)

Near 0 the integrand has the removable limit `A/2` (proved `tendsto_*_nhdsGT`),
so there is no singularity; the integrand is continuous on `(0,inf)`.  Split the
compact part at the crossover `y0` where `r(y) = A*e^(-y/2)`:

- `I_+` on `[0,y0]` (integrand >= 0, bounded by ~A): easy, no pointwise decay.
- `I_-` on `[y0,R]` (integrand < 0): bound by
  `2/ Int_{y0}^R A/(e^y - e^(-y)) = -2*A*[ ln(tanh(R/2)) - ln(tanh(y0/2)) ]`
  (needs only a LOWER bound on `y0`, i.e. how long `r(y) >= A*e^(-y/2)`).

Total need: `|I| < C*A`; measured headroom `C*A - |I| = +2.93`.  A pointwise
`r(y) >= A*e^(-y/2)` on `[0,y0]` for even `y0=0.2..0.5` plus the exact tail would
close this entirely, without any smooth-bump internals of `ContDiffBump`.

### Concrete recommendation (revised)

Prefer proving the two easy facts at the exact witness (no new bump needed):
1. `(f*f)(0) = ||f||^2` and `||f||^2 >= A0 > 0` via `f >= 1/e` on `[-1/2,1/2]`
   (the bump is `= 1` there; only `f > 0` and `f >= 1/e` midpoint must be shown).
2. `tendsto_archimedeanNumeratorRe_div_denominator_nhdsGT` gives the removable
   limit `A/2` at 0; wire `Integrable` + `integral_add` to bring the split
   `[0,y0]`, `[y0,R]`, tail into three provable pieces.
Then a single real-arithmetic check `|I| < C*A` closes wall-A 1.4. RH not claimed.
