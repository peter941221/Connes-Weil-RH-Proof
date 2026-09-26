# Record 1992 — Family brick F1b LANDED: the optimized-n identification is now a theorem — `deriv^[n] (gevreyInner k) u = exp(-k/s) * B_n` on `|u| < 1`, with `B_n` the F1a monomial family and the recursion `B_{n+1} = B_n' + g' * B_n` proved as a single `HasDerivAt` step; 18 declarations, all std axioms, zero sorryAx, zero new warnings

- **Date**: 2026-09-26
- **Status**: LANDED (Lean brick)
- **Brick**: `ConnesWeilRH/Dev/C1GevreyFamilyIdentification.lean` (namespace
  `GevreyFamily`, ~250 lines) + audit
  `ConnesWeilRH/Dev/C1GevreyFamilyIdentificationAudit.lean`
- **Build logs**: `build-logs/f1b_build3.log` (module, 0 errors / 0 module
  warnings), `build-logs/f1b_audit.log` (18 × `#print axioms`), 
  `build-logs/f1b_fullbuild.log` (full `lake build`, success; only
  pre-existing long-line warnings in older Source modules)
- **Pre-check**: `scripts/check_f1b_identification_1992.py`, logs
  `build-logs/r1992_check{1,2}.log` — 60-dps mpmath, identity grid 144 rows,
  worst relative error `1.3e-59`; multiset-vs-merged value parity PASS;
  `B_1 = -2ku/s^2` closed form PASS
- **Spec**: record 1990 §1(c) (the recursion-as-derivative identification);
  consumes brick F1a (`monos`/`children`, record 1991) and the committed
  window `gevreyInner` (brick 1)

## 1. What landed

| theorem | statement (informal) | role |
|---|---|---|
| `sinv`, `hasDerivAt_sinv`, `hasDerivAt_sinv_pow` | `sinv u = (1-u²)⁻¹`; `d(sinv^b)/du = 2b·u·sinv^(b+1)` (b = 0 collapse exact: `2·0 = 0`) | the `g'` engine |
| `Bmon` / `Bsum` | level-n monomial `c·k^p·u^a·sinv^b`; `B_n = Σ_{monos n}` | the polynomial ladder |
| `dBmon` / `dBsum` | per-term derivative value in exact `.mul`-output shape | no-ring bridge |
| `gfun` | `g' = -k·(2u·sinv²)` (the `-2ku/s²` of record 1990, `sinv` form) | recursion factor |
| `hasDerivAt_Bmon` / `hasDerivAt_map_sum` | per-term and finite-sum derivative | product rule layer |
| `children_Bmon_sum_eq` | `Σ children values = dBmon + g'·Bmon` per parent (4 branches; forced values `m.a = 0` / `m.b = 0` where the conditionals dropped a move) | per-parent bridge |
| `sum_map_children_eq` / `Bsum_step_eq` | `B_{n+1} = dBsum n + g'·Bsum n` — the record-1990 recursion as an identity of values | sum-level bridge |
| `hasDerivAt_expBsum_step` | `d/du [exp(-k/s)·B_n] = exp(-k/s)·B_{n+1}` on `|u| < 1` | **the recursion IS the theorem** |
| `Bsum_zero` / `Bsum_one` | `B_0 = 1`; `B_1 = gfun` (matches rung 1 of brick 2 / `gevreyDeriv`) | cross-checks |
| `deriv_iterate_gevreyInner` | `deriv^[n] (gevreyInner k) u = exp(-k/s)·B_n` on `|u| < 1` | **main theorem** |

Design choices frozen:

- **`sinv` stays FOLDED everywhere.** All powers are positive powers of the
  atom `sinv u` — no divisions, no inverse expansions. This is what makes
  `children_Bmon_sum_eq` close by `pow_succ`/`ring`: after `pow_succ`, both
  sides are sums of identical monomials over the atom basis
  `{m.c, ↑m.a, ↑m.b, k, k^m.p, u, u^(m.a-1), u^m.a, sinv u, sinv u^m.b}`.
  A first draft passed `sinv` itself to plain `simp`, which rewrote
  `sinv u^(m.b+2)` via `inv_pow` into `((1-u²)^m.b·(1-2u²+u⁴))⁻¹` on one
  side while the other side kept a different inverse-atom form — `ring`
  cannot see through `⁻¹` and failed permanently. Lesson: inverse-valued
  helper defs must never be handed to a simplifier that knows `inv_pow`.
- **`dBmon` is written in the exact `HasDerivAt.mul` output shape**
  `(const·(a·u^(a-1)))·sinv^b + (const·u^a)·(2b·u·sinv^(b+1))`, so
  `hasDerivAt_Bmon` is `exact` with zero rewriting.
- The truncated `u^(m.a-1)` of `hasDerivAt_pow` makes the dropped `u`-move
  EXACT at `a = 0` (term value `0·u^0 = 0`); the `b = 0` collapse of the
  first `s`-move is exact (`2·0 = 0`). The drops of `children` are therefore
  equalities, not bounds — no slack enters anywhere.
- The `exp`-factor derivative reuses the committed brick-1 pattern
  (`EventuallyEq` onto the `sinv` form + `hasDerivAt_iff.2 … .exp`), with
  the value first converted through a pinned `mul_comm` so both sides agree
  syntactically before `hasDerivAt_iff` unification.

## 2. Honesty box

- **Interior only**: the main theorem is stated on `|u| < 1`. The boundary
  flatness `deriv^[n] → 0` at `u = ±1` and the `C^∞` glue are F1c, not here.
- **No shape bound yet**: nothing bounds `|B_n|` — `S_n·k^n·s^(-2n)` with the
  `sumAbs_le` feeder (already a theorem in F1a) is the F1c content.
- **Multiset vs merged**: the Lean `monos n` multiset (children in emission
  order, duplicates NOT merged) carries the same FUNCTION as the merged-dict
  recursion of record 1989 — value parity verified numerically 84/84 rows
  (3 k × 4 u × 7 n). The COEFFICIENT SUMS differ: `Σ|c|` over the multiset is
  ≥ the merged value. The F1a `sumAbs_le` bound `5ⁿ·n!` is proven for the
  multiset, so it dominates both — the F2 constants are safe, but they are
  multiset constants, and any later sharpening through merged cancellation
  is deliberately not claimed.
- The A-machine (`Afunc`, `Afunc_step`, envelope) of F1a applies to the
  multiset weights unchanged; nothing in this brick touches it.
- The identification is an EQUALITY on the interior; no growth/decay
  estimate is proved here, and no gate sign; RH not claimed.
- Pre-check lesson (recorded): at `u = 0` odd orders the true derivative is
  exactly 0 (even profile) and `mp.diff` reports ~1e-78 roundoff — a pure
  relative metric explodes there (rel 4.3e+222). The grid check scales by
  the magnitude prior `profile·(6k·s_inv²)ⁿ`; all 144 rows then PASS at
  `1.3e-59`. A rig's metric must carry a magnitude prior before it is
  allowed to vote.

## 3. v4.30 elaboration hazards hit this wave

Mirrored into the internal WSL-side hazard catalogue:

1. `show T from omega` — missing `by`: `from` wants a TERM; bare `omega`
   becomes an unknown identifier. Write `from by omega`.
2. **Never pass an inverse-valued helper def to plain `simp`** when `ring`
   must finish: `inv_pow` + `pow_add` produce INCONSISTENT inverse-atom
   forms across the two sides and `ring` treats each `X⁻¹` as an opaque
   atom. Keep the def folded; let `pow_succ`/`pow_two` work on positive
   powers of the folded atom.
3. **Plain `simp` does not propagate `¬(0 < m.b)` to `m.b = 0`**: the ite
   branches resolve, but symbolic `↑m.b` terms survive and `ring` reports
   monomials that differ by an `↑m.b`-atom. Fix: pass the forced equalities
   as simp arguments (`simp […, hbz]` with `hbz : m.b = 0`) — this refines
   the F1a `rw [hbz]`-first pattern.
4. `deriv^[n+1] f u = deriv (deriv^[n] f) u` is NOT closed by `rfl` in this
   toolchain (the unifier refuses the iterate unfold through `deriv`'s
   application). Use `rw [Function.iterate_succ_apply']`.
5. `deriv^[0] f u` is not syntactically `f u`: a rewrite lemma about `f u`
   finds no pattern. Bridge with `change f u = _` — NOT `show`, which now
   trips `linter.style.show` when it changes the goal.
6. `t1 <;> t2` warns (`linter.unnecessarySeqFocus`) when `t1` provably
   leaves exactly one goal — use the `;` newline form; verify `t2` actually
   fired first, otherwise `;` turns a no-op into "no goals" failure.
7. In the `HasDerivAt.inv` + `congr_deriv` bridge, `neg_neg` is an UNUSED
   simp argument (a simproc already normalizes the double negation) and
   `ring` handles `-(-2*u)` natively — drop it, `unusedSimpArgs` fires
   otherwise.

## 4. Next steps (the brick order stands)

1. **F1c (shape + glue)**: `|B_n(u)| ≤ S_n·k^n·s^(-2n)` with `S_n ≤
   (Σ|c|)·(2n-sup)` fed by F1a's `sumAbs_le` (`Σ|c| ≤ 5ⁿ·n!`), then the
   `C^∞` flatness/glue at `u = ±1` (brick-1 squeeze pattern; the boundary
   derivative is already 0 there for the window itself).
2. **F2 (consumer)**: order-n IBP with the boundary killed by F1c,
   `|L_phi(w)| ≤ e^{|Re w|}·(A_n + M_n)/|w|^n`, then the choose-n
   corollary `e^(-c_env·sqrt(k|T|))` with the record-1990 §1(d) constants
   (c ≥ 1/2 certified for k ≥ 3; k = 1 needs the b-slice refinement); the
   two-ring middle bound `M_n` lands alongside.
3. **Resolution certificate** (1985's `cert_ok = FALSE` root cause) and the
   re-bracket of the 1981 GO_CANDIDATE at `rho = 1/2 + 0.10 + i*gamma_1`
   (obligation `D < 0`).

No gate sign is proved here; RH is not claimed.
