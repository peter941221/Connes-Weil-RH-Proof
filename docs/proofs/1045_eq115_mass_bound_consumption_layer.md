# 1045 - The Fact-1 mass-bound consumption layer (and why the table is not data yet)

Date: 2026-08-28.  Follows 1044.  Records the Lean side of CC20 Fact 1's
strict mass inequality and the judgment that the numeric grid table is not
producible yet.

## What landed

`ConnesWeilRH/Dev/C1CC20Eq115MassBound.lean` (+ Audit), five declarations,
all printing exactly `[propext, Classical.choice, Quot.sound]`, zero
`sorryAx`; batch build 3642 jobs clean:

1. `l1_uniform_grid` - on a uniform grid of positive step `delta` with one
   per-tile upper bound `B j`, the L1 mass over `[0, n * delta]` is at most
   `delta * sum_{j < n} B j`.  Induction on `n`; adjacent-tile integrability
   is combined with `IntervalIntegrable.trans`.
2. `l1_tail_bound` - on one interval, a pointwise upper bound gives
   `integral <= (b - a) * B` via `intervalIntegral.integral_mono_on` against
   the constant function.
3. `l1_mono_upper` - monotone upper limit for nonnegative integrands over
   nested right endpoints.
4. `continuousOn_cc20Eq115DifferenceProfile` - the concrete table's
   difference profile is ROOT-window continuous as soon as the endpoint
   profile is (caller field `hchi` of 1044).
5. `cc20Eq115_halfGapCertificate_of_uniformGrid` - the complete assembly:
   from a grid bound table plus the two analytic caller fields to the full
   `CC20FiniteRankHalfGapCertificate` for the extracted eq-(115) data.

## The certificate contract

The grid tiles `[j * step, (j + 1) * step]` for `j < count` must stay inside
the ROOT window (`count * step <= cc20RootLength = log 2`); the last piece
`[(count * step), log 2]` ends exactly at the irrational endpoint and
contributes `(log 2 - count * step) * boundTail`.  The aggregate obligation
is the single inequality

    2 * (step * sum_{j < count} bound j
         + (log 2 - count * step) * boundTail) <= epsilon1,

with `bound` / `boundTail` bounding the pointwise norm of the difference
profile.  Lean never evaluates `log 2` numerically - the tail length stays
symbolic.  This is the "floats generate, Lean verifies the aggregate"
shape: a future certified quadrature run only has to emit per-tile rationals
and this layer does the rest.

## Why the table is not produced now (the judgment)

Two independent reasons, one per endpoint side:

1. The integrand is not enclosable yet.  The difference profile
   `chi - tau` needs a concrete `CC20EndpointSpectralData` instance with an
   analytic enclosure of `qEpsilon(e^|v|) / (2 * endpointSlope)` on
   `e^|v|` in `[1, 2]` - Sturm-Liouville spectral regularity that Mathlib
   does not carry (the same GATE-2-class obstacle documented in 1044).
2. A tau-only quadrature would be honest and useless.  Exact-rational
   diagnostics from the real manifest (Python `Fraction`, no floats):
   with `L = log 2`, `tau(0) = lambda * (2 / L) * sum_n (1 - d_n)` and
   `sum_n (1 - d_n) = -114996652757599 / 312500000000000 = -0.367988...`
   (m = 1732, sum of the 1732 published coefficients), so
   `tau(0) = -1.0619... * lambda`: the finite-rank profile alone is NOT
   small - only the difference `chi - tau` is.  Bounding `|chi - tau|` from
   `|tau|` alone gives an `O(lambda)` bound, which forces `lambda` down to
   the `10^-3` scale before `epsilon1 ~ 0.00122` is reachable, and even
   then the strict form of Fact 1 needs half the mass the open form allows.
   A certificate of an O(lambda) bound would satisfy the letter of the
   interface while proving nothing - so it is not generated.

Conclusion: the durable brick is the consumption layer (this record); the
grid table becomes meaningful the moment the endpoint enclosure (caller
field `hchi`) exists, and then feeds `cc20Eq115_halfGapCertificate_of_uniformGrid`
directly.

## Engineering notes (v4.30)

- `IntervalIntegrable.trans` is the adjacent-interval combiner
  (`IntervalIntegrable f mu a b -> IntervalIntegrable f mu b c ->
  IntervalIntegrable f mu a c`).  `IntervalIntegrable.add` is the
  SAME-interval pointwise add - using it across adjacent pieces silently
  creates metavariables.
- `intervalIntegral.integral_add_adjacent_intervals` states
  `(integral a..b) + (integral b..c) = integral a..c`.  When the goal has
  the single `integral a..c`, rewrite with the `<-` direction.  Both uses in
  this file needed `<-`.
- Nat-cast spelling bridge: the `forall j < n` premise instantiates to
  `(up j + 1) * delta`, while the `forall n` conclusion carries
  `up (n + 1) * delta`.  These are NOT defeq (nor interpolable by `ring`);
  bridge once with `Nat.cast_succ` and rewrite BEFORE splitting the
  conjunction, so both components live in the `(up j + 1)` spelling.
- `rw [integral_const, smul_eq_mul]` on `integral_mono_on`'s output reduces
  the constant side cleanly to `(b - a) * B` - no lambda leftovers.  But
  integrals whose integrand is an instantiated lambda argument carry
  beta-redexes that display reduced: normalize with `simp only []` before
  `linarith`, and do NOT follow a rewrite (which arrives beta-clean) with
  `simp only []` - it errors "made no progress".
- calc with two interval integrals on one line: parenthesize the first
  integral.  The interval-integral notation sucks the following `integral`
  into the first integrand's body (recurring hazard).
- Products of two atoms are different atoms for `linarith`:
  `boundTail * (L - c*s)` vs `(L - c*s) * boundTail` do not unify.  Fix the
  FORM at the statement (state the hypothesis in the lemma's natural
  product order) instead of a bare `mul_comm` rewrite - the first-match
  hazard makes untargeted commutativity rewrites land inside the norm body.
- `Set.Ι` is not an addressable constant.  For the degenerate interval:
  `rw [intervalIntegrable_iff]`, then `Set.uIoc_of_le` +
  `Set.Ioc_eq_empty_iff` reduce `uIoc 0 0` to the empty set, and
  `integrableOn_empty` closes it.
