# 971 - Wall-A 1.4 `hI` near-band: the explicit-F re-point, concretely

Date: 2026-08-11.  Status: execution spec for the surviving Wall-A leaf.  The near
band `(0,1]` of `|I| < C*A` cannot be closed at an opaque mathlib `ContDiffBump`
(docs/969; verified again this session: the F-slope `|e^{y/2}F-A| <= k*y` is the
*only* integrable pointwise-envelope, and it needs the bump's transition slope,
which `ContDiffBump`/`someContDiffBumpBase` hides).  This doc turns the required
re-point into concrete definitions + target lemmas, so the next session can execute.

RH NOT claimed.

## Why the re-point is necessary (one-line)

On `(0,1]`, `g y = 2(e^{y/2}F(y)-A)/den y`, `F(0)=A`.  A crude `0<=F<=A` bound gives
`|g| ~ A/y -> blows up logarithmically` at 0; only a slope bound `|X(y)| <= c*y`
(X = e^{y/2}F - A), equivalently `F(y) = A - O(y)`, makes `(0,1]` integrable.
For the *plateau* `plateauBump` (rIn=9/10, rOut=1) that slope needs `f`'s values on
the thin wall `(9/10,1)`, which the bundled mathlib bump hides.

## The explicit witness: replace `plateauTest.test` with an explicit bell

A concrete, author-controlled compact bump with a flat plateau + known decay, so
`F(y)=int f(t) f(y-t)` is pointwise-readable.  Recommended:

    f(x) = exp(-r^2/(r^2 - x^2)) ,  |x| < r ;  f(x) = 0 ,  |x| >= r

inner plateau `p = r/2`, outer `r`.  Properties used:

    (P0) compact support in `[-r, r]`, value `1` on `[-p, p]`
    (P1) 0 <= f <= 1
    (P2) even, `C^inf`
    (P3) `|f(x)|`, `|f'(x)|` and `|f''(x)|` bounded by explicit constants on all of R
         via the closed form `x/r` and `exp(-1/(u))` bounds (the whole point: closed
         forms are provable).

For concreteness take `r = 2`, `p = 1` (plateau radius 1), giving
`(f*f)(0) = int f^2 >= 2*p = 2` (on the plateau `[-1,1]` integrand = 1).

## Target Lean lemmas (names for the new `Dev/Wall14PlateauExplicit.lean`)

  1. support / bounds:
     `f_abs_le_one : |f x| <= 1`, `f_eq_zero_of_abs_le`: `x<=r -> f x = 0`
     `f_eq_one_of_abs_le`: `|x| <= p -> f x = 1`
  2. `A = (f*f)(0)` bounded and positive: `two <= A`, `A <= 2*e` etc. (e..normSq integral)
  3. convolution bounds:
     `F_le_A : F(y) <= A`, `F_nonneg : 0 <= F(y)`
     `F_slope : forall y in [0,1], |F(y) - A| <= C1 * y`      (C1 explicit, e.g. 2*p*sup|f'|)
     `F_even : F(-y) = F(y)`
  4. the assembled near/mid/tail integral chain feeding `|I| < C*A` as in
     (Wall14ArchSufficiency + healthy bridge), identical to the current proof but with
     explicit `f`.

## Bookkeeping
- New file `Dev/Wall14PlateauExplicit.lean` imports the same `CompactLogConvolution`
  chain, defines `plateauBell`, `plateauRealE`, `plateauOwnerE`, and the F-lemmas.
- Do NOT touch `/cc Proj` sufficiency / `Wall14ArchReduction` / `Wall14ArchSufficiency`
  (closed bytes). The witness replacement happens by defining `plateauOwnerE` and
  feeding `archimedeanTerm_ne_zero_of_lead_pos_and_integral_bound` at it, exactly as
  the plateau path did.
- Verify with the numbered ladder (module build, `#print axioms` = `[propext,
  Classical.choice, Quot.sound]`, 0 sorry). Full build only at a closing milestone.

## Why this will close
- `F` now has an explicit slope bound, so the near-band `|g| <= k` bound holds
  (deny_ge_two = the `den >= 2y` leg, already proven axiom-clean).
- The `middle [1,2]` + `tail [2,inf]` bounds are already green.
- `3 < C = log(4*pi)+gamma` is a Latin-of-closed-form numeric (standalone leaf).
- Texting the finiteness: total `|I| ~ 0.6*A << 3.1*A`; plenty of margin.

## Concrete next-but-one sub-tasks (in dependency order)
  1. build the explicit bell + (P0)-(P3), focus on proving `f` is a Schwartz/compact
     test (`SchwartzMap Real Complex`) re-usable as `plateauOwnerE`.
  2. prove A (normSq integral) lower/upper and the F slope `|F(y)-A| <= C1 y`.
  3. assemble near/mid/tail + `3<C`, feed sufficiency, audit.