# 1047 - The (gamma) coercivity: sandwich contract, Bessel breakthrough, and the reconnaissance ledger

Date: 2026-08-29.  Follows 1046.  Records three things: the sandwich
consumption contract for certified spectral data, the elementary Bessel
route proposed to discharge the flagship `hT` premise for the concrete
equation-(115) table without an eigenvalue enclosure, and the reconnaissance
verdicts from the literature sweep (what does and does not bypass payload
(alpha)).  The Bessel source is not an accepted Lean result at this checkpoint.

Superseding correction (2026-08-29): equation (119) includes the central
`n = 0` term, and CC20's reported scale is near `lam = 1.05158 > 1`.
Accordingly, the discussion below of Bessel as a possible shortcut for the
paper-scale gamma payload is historical reconnaissance only.  The repaired
Bessel theorem is valid for `lam < 1`, but paper-scale gamma still requires
the exceptional-direction/complement/rank-one argument.  See proof 1050.

## What landed

This checkpoint contains three Dev leaves plus two audit leaves in
`ConnesWeilRH/Dev/`.  Their validation states differ: the generic sandwich
and coefficient-positivity leaves are accepted; the Bessel leaf is retained
as an unaccepted research frontier.

1. `C1CC20GammaCoercivity.lean` - the (gamma) SANDWICH CONTRACT.
   Two structure-agnostic lemmas that fold a certified row-band enclosure
   (real diagonal centres `center`, symmetric per-entry radius `rad`, row
   dominance `center i - sum_j rad i j >= lambda` /
   `center i + sum_j rad i j <= lambda`) of the equation-(119) matrix into
   whole-space quadratic-form bounds (`hspectral` lower bound and
   `hR_upper` Rayleigh upper bound), without ever evaluating the matrix.
   The proof is an AM-GM fold over the symmetric radius; no Hermiticity of
   the matrix is needed and no Mathlib spectral calculus is touched.  This
   is the "floats generate, Lean verifies the aggregate" pattern of
   `C1CC20Eq115MassBound` moved from the L1 side to the spectral side.
   Axiom-clean: `[propext, Classical.choice, Quot.sound]`.

2. `C1CC20Eq115CoefficientPositivity.lean` - every branch of the
   1732-coefficient `ite` chain `cc20Eq115CoefficientQ` is strictly positive,
   discharged in two machine-generated layers (generator:
   `scripts/cc20_eq115/gen_positivity.awk`, committed for provenance):

   - one kernel-`rfl` theorem per branch
     (`..._branch_k : cc20Eq115CoefficientQ <k> = literal`, 1732 of them,
     each an O(k) trivial chain descent);
   - a single aggregation theorem: decompose the `Fin 1732` index to a
     natural number, sweep all 1732 literals with ONE `interval_cases k`,
     close every goal by rewriting the matching branch equation + `norm_num`.

   The per-branch equations replace the O(N^2) cost of re-simpping the whole
   chain inside each of the 1732 goals (the route that timed out in
   production shape; see the Lean-error ledger below).  The real-valued
   corollary `cc20Eq115Coefficient_nonneg` follows by `mod_cast`.  Kept as
   its own leaf because this compile is the expensive part and lake caches
   it once.

3. `C1CC20GammaBesselCoercivity.lean` - the proposed (gamma) BESSEL BRICK,
   intended to produce the flagship `hT` premise:

   - `window_exp_integral` - the interval Fourier integral of the window
     exponential equals the Kronecker delta (FTOC route: antiderivative
     `c⁻¹ * exp(c*x)`, boundary values `(n*pi*I)` and `(n*pi*I) - 2*(n*pi*I)`,
     `Complex.exp_int_mul` + `exp_two_pi_mul_I`).
   - `inner_cc20WindowFourierVector_int_eq` - the un-normalized Gram entry
     of two windowed modes is `if m = k then cc20RootLength else 0`
     (`integral_indicator` reduces the Bochner integral over the indicator
     to the set integral, which equals the interval integral over
     `[-L/2, L/2]`).
   - `cc20Orthonormal_unitWindowFourierMode` - with the repo's phase
     convention `cc20FourierPhase alpha x = exp(2*pi*alpha*x/L * I)`, the
     windowed INTEGER modes scaled by `(sqrt L)⁻¹` are orthonormal, so
     Mathlib's `Orthonormal.sum_inner_products_le` (Bessel) applies directly.
   - `cc20DefectQuadraticForm_ge_of_bessel` - the GENERAL brick: for any
     table with integer base frequencies (`hbase`), injective indexing
     (`hinj`), nonnegative coefficients (`hcoef`) and `lambda >= 0`
     (`hlam`), every vector satisfies
     `cc20DefectQuadraticForm (cc20FiniteRankOperator data) xi >=
     (1 - data.lambda) * ‖xi‖²`.
   - `cc20Eq115DefectBessel_ge` - the instantiation to the concrete
     equation-(115) table, using the extracted base-frequency function
     `cc20Eq115BaseFrequency` (positive branch for `b`, negative for
     `!b`), its injectivity, and the positivity leaf.
   - `cc20Eq115_gate1hT` - the flagship premise, exhibited with
     `ell := 0`: for `0 <= lam < 1` and any `gapData` with
     `epsilon2 <= 1 - lam`,
     `defect(xi) + gapData.a * (ell xi)² >= gapData.epsilon2 * ‖xi‖²`.

   These declarations are source-level targets, not accepted theorems:
   the forced `gamma6` build has 15 root errors, so this leaf and its audit
   have not elaborated successfully.

4. `C1CC20GammaCoercivityAudit.lean` and
   `C1CC20GammaBesselCoercivityAudit.lean` - the axiom-audit leaves.
   The former has accepted `#check` and `#print axioms` output for all three
   sandwich declarations.  The latter contains the corresponding checks for
   the positivity and Bessel declarations, but cannot run until the Bessel
   leaf compiles.

The positivity leaf is machine-generated; its generator
`scripts/cc20_eq115/gen_positivity.awk` (parses the committed table chain
and emits the per-branch equations plus the aggregation sweep) is committed
alongside `extract_source.py` / `gen_eq115_table.py` for provenance.

Two small probes are retained with this checkpoint:
`C1CC20GammaBesselProbe.lean` (the FTOC-integral reconnaissance) and the
root-level `probe_sinh.lean` (exp-independence API reconnaissance).  Neither
is imported by an accepted route leaf or treated as proof evidence.

## Why Bessel is the proposed shortcut for the hard version of (gamma)

1046's judgment said (gamma) "needs a certified eigenvalue enclosure of a
3464x3464 Gram-modulated matrix".  That judgment was about the sharp lower
bound `lambda` of the concrete operator.  The proposed flagship premise does
not ask for sharpness - it asks for coercivity of `I - T` against
`epsilon2 * ‖xi‖²`, where `epsilon2` is a free data field whose only flagship
constraint is the sandwich `epsilon2 <= 1 - lam`.  The intended route is
Bessel's inequality:

    T = lam * sum_i (P_{n_i} - d_i P_{a_i})   (rank-one Fourier projections)
    <xi, T xi> = lam * sum_i (|<e_{n_i}, xi>|² - d_i |<e_{a_i}, xi>|²)
              <= lam * sum_i |<e_{n_i}, xi>|²      (d_i >= 0, positivity leaf)
              <= lam * ‖xi‖²                        (Bessel, orthonormal modes)
    => defect = ‖xi‖² - <xi, T xi> >= (1 - lam) ‖xi‖².

If the Bessel source is repaired and accepted, this avoids a Gram matrix,
directed rounding, and a transcendental enclosure.  The Gershgorin sandwich
(leaf 1) remains the optional route for pushing `epsilon2` past `1 - lam`
toward the paper's ~0.00441 scale, and the accepted consumption contract if a
sharper spectral certificate is ever built.

## What (gamma) can become, and what it is today

- The accepted generic sandwich is a consumption contract for a certified
  row-band spectral block.  It does not by itself instantiate the concrete
  equation-(115) operator.
- The concrete Bessel route would make (gamma) independent of a sharp
  eigenvalue enclosure, but `cc20Eq115_gate1hT` is not currently available:
  its owning Bessel leaf fails the `gamma6` forced build.
- Once that leaf is accepted, the remaining (gamma) work is a consistency
  obligation on the assembly: supplied `gapData` must satisfy both
  `h_gap : epsilon1 < epsilon2` and `epsilon2 <= 1 - lam`.  The `ell := 0`
  filler is honest but degenerate, so the sandwich alone carries the latter
  inequality.  A nonzero `ell` with `a > 0` would require independent slack.

## The reconnaissance ledger (literature sweep verdicts)

- Bombieri's `K*` (the dual/adjoint kernel appearing in the Bombieri-Hejhal
  literature around Weil's explicit-forms positivity) is NOT a bypass of
  payload (alpha): it reformulates the same endpoint-profile condition on
  the adelic side; it neither supplies `hchi` nor removes the need for it.
- Honest (alpha) is an 11-term series truncation with a `10⁻¹¹` remainder
  term: no closed-form enclosure is known, so (alpha) remains an
  interval-arithmetic certification project (Sturm-Liouville regularity is
  absent from Mathlib, so the enclosure must be built from ODE-integration
  certificates, not from an existence theorem).
- (delta) is pinned to the CC20 §6 root window: the archimedean comparison
  can only be stated with the root-length window `L = log 2`; any other
  window breaks the trace normalization `-(4/log 2) * q(K_I)`.

## Lean-error ledger (this slice)

- `norm_num` on the 1732-branch `ite` chain: "deterministic timeout at
  whnf, maxHeartbeats 200000" after 1613 s.  simp pre-processing plus whnf
  pays the chain depth O(N) times.
- `interval_cases k; decide`: "Expected type must not contain free
  variables" x103 - `interval_cases` keeps the Fin bound proof `hk` as a
  free variable inside `⟨95, hk⟩`, so each goal is open.
- Dead end (found the hard way): kernel `decide` cannot decide even a BARE
  rational literal comparison in this Lean version —
  `by decide : (0 : ℚ) < 17320000001713431 / 10000000000000` gets stuck at
  `Rat.blt` because the `Rat.instDecidableLt` instance cannot whnf the
  externalized rational arithmetic.  `fin_cases n <;> decide` therefore
  fails per case (and `fin_cases`'s own 1732-case substitution plus the
  quadratic per-case chain descent made the first production build stall
  past 60 min at 11 GB RSS before being killed).
- Per-case `simp only [cc20Eq115CoefficientQ]` + bare `norm_num`: the
  per-goal mechanics work (the ite conditions only inspect `n.val`, so open
  subtype-bound proofs do not block simp; `norm_num`'s Rat extensions
  evaluate division literals that `whnf` cannot) - boundary-verified at
  cases 0, 1000 and the deepest case 1731.  But each of the 1732 goals
  rebuilds the whole chain from scratch: O(N^2), and the production-shape
  probe timed out (exit 124).  Rejected for the permanent leaf.
- Winner, measured: 1732 generated per-branch kernel-`rfl` equations plus a
  single `interval_cases k` sweep.  Case generation itself takes ~0.3 s;
  each goal then pays only literal-mismatch rewrite attempts (microseconds)
  plus the one matching branch rewrite and `norm_num`.  This settles the
  head-to-head: `fin_cases n` on the `Fin 1732` index stalls in its own
  substitution machinery (>50 min without a single error, killed at
  12.8 GB RSS); `interval_cases` on the decomposed natural number is the
  supported route (its previously fatal pairing with `decide` was the only
  real problem).
- Term-level `mod_cast` lifts the source relation AS-IS and needs a known
  strict target, so proving `0 ≤ cc20Eq115Coefficient n` from
  `cc20Eq115CoefficientQ_pos n` took two failed forms before settling.
  First, bare `exact mod_cast h`: it lifts the ℚ inequality to a STRICT ℝ
  inequality and does not consult the expected nonstrict target (type error).
  Second, the dot form `(mod_cast h).le`: "expected type must be known",
  because in argument position the macro gets no elaboration context to infer
  a cast target from.  Working form: weaken the goal first with
  `apply le_of_lt`, then `exact mod_cast h` — micro-probe-verified in the
  leaf's own import context before re-spending a full build.  The line had
  been copied from a draft that never compiled far enough, so both failures
  only surfaced in production builds (each of which otherwise elaborated all
  1732 branch equations and the whole sweep cleanly).
- `hfreq ▸ hperp` is ambiguous transport (direction unknown to Lean):
  use `hfreq.trans hperp` explicitly.
- Structure projections (`CC20FiniteRankData.frequency`) are NOT equations;
  listing them in `simp only` errors - rely on beta for `(data.frequency i)`.
- `omega` cannot prove pair equalities that hide an `if` split; discharge
  the mixed-sign case with `exact absurd hab (by omega)` so omega sees only
  the integer projections.
- WSL2 login shell eats `$VAR` inside `wsl.exe sh -c '...$M...'` even in
  single quotes (the outer PowerShell/cmd layer interpolates first): use
  inline absolute paths in one-off commands.
- `grep "^theorem lemmaName"` misses namespaced lemmas
  (`theorem Orthonormal.sum_inner_products_le`): search the bare name.
- CLM pointwise sums: `(sum i, t i) xi = sum i, t i xi` is true by `rfl`
  (the CLM `AddMonoidAlgebra`-style ops are definitionally pointwise);
  if a future Mathlib change breaks it, fall back to
  `ContinuousLinearMap.map_sum` / `fintype_sum_apply`.
- Forced `gamma6` removed the earlier missing-window-name and Unicode-minus
  parser failures, but still reports 15 root errors: star/exponential rewrite
  mismatches, ambiguous `integral_indicator`, incomplete Fourier-projection
  rewrites, mixed-sign index arithmetic, and the final norm-square fold.
  This is a red research leaf, not an accepted Bessel theorem.

## Build evidence

| Target | Evidence | Status |
| --- | --- | --- |
| `C1CC20GammaCoercivity` + audit | Forced re-elaboration, zero `error:`, `Build completed successfully (2943 jobs)`; all three audit declarations print `[propext, Classical.choice, Quot.sound]`. | ACCEPTED |
| `C1CC20Eq115CoefficientPositivity` | `gamma5` log records `Built ... (1242s)` before the dependent Bessel build began; its final strict-to-nonstrict cast uses `apply le_of_lt; exact mod_cast h`. | ACCEPTED |
| `C1CC20GammaBesselCoercivity` + audit | Forced `gamma6` build ends `Lean exited with code 1` and `build failed`, with 15 root errors; the dependent audit did not run. | RED |

## GATE 1 status after this slice

| # | Payload | Status |
| --- | --- | --- |
| alpha | endpoint enclosure `hchi` | OPEN - interval-arithmetic ODE certificates, 11-term + 10⁻¹¹ honest form |
| beta | joint (chi - tau) uniform-grid table | OPEN - blocked by alpha |
| gamma | concrete flagship `hT` | PARTIAL - accepted generic row-band sandwich; concrete Bessel producer is RED in `gamma6` |
| delta | archimedean comparison | OPEN - pinned to the CC20 §6 root window |
| gapData | choice satisfying all flagship premises incl. `epsilon2 <= 1 - lam` | OPEN - assembly obligation |

RH is not claimed.  The concrete T-side premise remains open until the Bessel
leaf and its audit build cleanly; the endpoint profile (alpha), grid table
(beta), archimedean side (delta), and `gapData` choice are also open.

## Next steps

1. Resolve the 15 `gamma6` Bessel errors, then rebuild the Bessel audit and
   read back the standard-axiom output for every public declaration.
2. Instantiate the accepted row-band sandwich with a certified spectral block
   if a sharper `epsilon2` bound is required.
3. After a concrete `hT` producer is accepted, exhibit one
   `CC20OperatorGapData` satisfying `h_gap` and `epsilon2 <= 1 - lam`.
