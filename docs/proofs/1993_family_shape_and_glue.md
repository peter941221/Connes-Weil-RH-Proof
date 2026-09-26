# Record 1993 — Family brick F1c LANDED: shape bound + C^∞ glue for the whole optimized-n ladder — `|deriv^[n] (gevreyInner k) u| ≤ sqConst n k * (1-u²)²` on `|u|<1`, every iterate `= 0` and differentiable with derivative `0` on `1 ≤ |u|`; 18 declarations, all std axioms, zero sorryAx, zero new warnings

- **Date**: 2026-09-26
- **Status**: LANDED (Lean brick)
- **Brick**: `ConnesWeilRH/Dev/C1GevreyFamilyGlue.lean` (namespace
  `GevreyFamily`, ~430 lines) + audit
  `ConnesWeilRH/Dev/C1GevreyFamilyGlueAudit.lean`
- **Build logs**: `build-logs/f1c_build4.log` (module, 8478 jobs,
  0 errors / 0 module warnings), `build-logs/f1c_audit.log` (18 ×
  `#print axioms`, all `[propext, Classical.choice, Quot.sound]`)
- **Pre-check**: `scripts/check_f1c_shape_glue_1993.py`,
  `results/1993_f1c_shape_glue.json`, logs
  `build-logs/r1993_check{1,2}.log` — 50-dps mpmath; squeeze-bound
  dominance 396/396 rows (min ratio 7.53), boundary-slack scan
  (max (1−(u+w)²)/(3|w|) = 0.666), recursion parity vs `mp.diff` PASS
  (after fixing the rig's own rewritten recursion; see §2)
- **Spec**: record 1990 §1(c) shape/glue split + the F1c step of the
  record-1991/1992 brick order; consumes F1a (`mono_invariant`,
  `sumAbs_le`, `sum_map_le_sum_map`, `sum_map_mul_left`), F1b
  (`Bmon`/`Bsum`, `deriv_iterate_gevreyInner`) and brick 1
  (`exp_neg_div_le_div`, the boundary-squeeze and `EventuallyEq` patterns)

## 1. What landed

| theorem | statement (informal) | role |
|---|---|---|
| `sinv_one_le_of_abs_lt` | `1 ≤ sinv u` inside the window (`s ≤ 1`) | feeds `pow_le_pow_left_real` |
| `pow_le_pow_left_real` | `1 ≤ a → m ≤ n → a^m ≤ a^n` (self-contained) | exponent monotonicity |
| `exp_pow_nat` | `exp x ^ n = exp (n * x)` | one canonical exp-power form (avoids sign-paren drift) |
| `abs_pow_le_one_of_le` | `|x| ≤ 1 → |x| ^ j ≤ 1` | the `u^a` factor |
| `abs_Bmon_le` | `|Bmon k u m| ≤ |m.c| * k^n * sinv^(2n)` per term | per-term shape (F1a invariants) |
| `abs_map_sum_le` | `|(l.map f).sum| ≤ Σ |f m|` | list triangle (Mono-form, `abs_add_le`) |
| `abs_Bsum_le` | `|Bsum n k u| ≤ (Σ|c|) * k^n * sinv^(2n)` | sum-level shape |
| `abs_deriv_iterate_gevreyInner_le` | `|deriv^[n] φ_k u| ≤ 5^n n! * (k^n * sinv^(2n) * exp(−k/s))` | interior shape via F1b |
| `exp_sinv_trade` | `exp(−k/s) * sinv^(2n) ≤ (2n+2)^(2n+2) s² / k^(2n+2)` | the 7s-style power trade at order `2n+2` (brick-1 lemma `exp(-k/t) ≤ t/k` with `K = k/(2n+2)`) |
| `sqConst` / `sqConst_pos` | `5^n n! (2n+2)^(2n+2) / k^(n+2)`, positive | the squeeze constant |
| `abs_deriv_iterate_le_sq` | `|deriv^[n] φ_k u| ≤ sqConst n k * (1−u²)²` | **interior bound in squeeze form** — quadratic vanishing at the glue |
| `one_sub_sq_add_le` | `1 − (u+w)² ≤ 3|w|` at `|u| = 1` | boundary slack |
| `iterate_zero_hasDerivAt_ext` | on `1 ≤ |u|`: `deriv^[n] φ_k = 0` AND `HasDerivAt (deriv^[n] φ_k) 0` — one induction on `n` | **the C^∞ glue** (exterior: eventually zero; boundary: brick-1 squeeze through `9 * sqConst (n+1) k * |w|`) |
| `deriv_iterate_gevreyInner_of_one_le_abs` / `hasDerivAt_iterate_gevreyInner_ext` | the two projections | F2 boundary-term killers |
| `continuous_iterate_gevreyInner` | every iterate continuous on ℝ | F2 integrability |
| `intervalIntegrable_iterate_gevreyInner` | `IntervalIntegrable (deriv^[n] φ_k) volume a b` | F2 IBP hypothesis |

Design choices frozen:

- **Hypothesis is `1 ≤ k` throughout the glue** (not `0 < k`): the shape
  bound needs `k^m.p ≤ k^n`, which INVERTS for `k < 1`. The first draft
  assumed `0 < k` and the elaborator caught it at
  `abs_deriv_iterate_le_sq` (`le_of_lt hk : 0 ≤ k` vs the lemma's `1 ≤ k`)
  — a real mathematical bug, not a syntax slip. All rungs and the F2
  consumer state `1 ≤ k`, so nothing downstream weakens.
- **The squeeze at `|u| = 1` uses the LEVEL-(n+1) shape bound**:
  `|f(u+w)| ≤ sqConst (n+1) k * s²` and `s ≤ 3|w|` give
  `‖w‖⁻¹‖f(u+w)‖ ≤ 9 * sqConst (n+1) k * |w|` — the same
  exponential-beats-polynomial mechanism as brick 1, now generated from the
  family shape bound instead of a hand-rolled `(1-u²)^4` trade.
- **The `w = 0` point needs no patch**: at `w = 0` the difference quotient
  reads `‖0‖⁻¹ * ‖f u‖ = 0` because `f u = 0` (level-(n+1) value at the
  boundary) — the `simp [hf0]` branch closes it.
- `exp_pow_nat` exists because `Real.exp x ^ n` and
  `Real.exp ((n:ℝ) * x)` appear with THREE different negation
  parenthesizations across brick 1's `exp_neg_div_le_div`
  (`(-(K))/(1−u²)` form) and the key identity; one lemma, `rw` forward.

## 2. Honesty box

- **Constants valid, not sharp** (house style). The pre-check measures the
  squeeze bound at min ratio 7.53 (best point) and ~5.5e20 (k=1, n=8 worst
  on the grid): the triangle/sup ceiling costs ~2–3 orders per n step.
  This is FINE for the glue (only the s²-vanishing matters) and for F2's
  boundary terms; the F2 MASS constants come from the A-machine (record
  1990), not from `sqConst`.
- **Tightness table** (min bound/true ratio per (k, n), pre-check):
  `k=1`: 7.5 / 1.8e2 / 1.1e4 / 2.0e7 / 1.1e9 / 1.0e12 / 1.2e15 / 4.1e17 /
  5.5e20 for n = 0..8; `k=30`: 4.8e10 … 1.3e22. Feeds nothing directly;
  recorded so the choose-n corollary's expectations are calibrated.
- **`max ratio = inf` rows are the odd-order zero rows**: at `u = 0` the
  true derivative of the even profile is EXACTLY 0 (record 1992 lesson);
  the rig maps `true = 0` to `ratio = inf`, the safe direction for a
  dominance check. No relative metric on zero rows is claimed.
- **The rig's own first recursion was WRONG** (`r1993_check1.log` FAIL):
  rewriting the committed 1990 step from memory dropped the `u^(a+1)` lift
  of the g′-move and double-counted `k` (rel ≈ 1.0 across all parity rows —
  the signature of a total desync, not noise). Fix: copy the committed
  `step` of `scripts/check_family_induction_1990.py` verbatim (three moves:
  `(a−1,b,p) += c·a`, `(a+1,b+1,p) += c·2b`, `(a+1,b+2,p+1) += −2c`, k
  absorbed into the p-slot). Re-run: parity PASS, bound PASS. Lesson
  re-confirmed: **never re-derive a committed recursion — copy it**.
- The glue theorems are for the UNIT window `gevreyInner k` (no scaling
  `φ_k(u/a)` yet — same scope as rungs 1–3).
- No Laplace transform, no mass bound, no gate sign here; RH not claimed.

## 3. v4.30 elaboration hazards hit this wave

Mirrored into the internal WSL-side hazard catalogue (§7-series):

1. **`mul_le_mul` slot order in v4.30**: `(a ≤ b) → (c ≤ d) → (0 ≤ c) →
   (0 ≤ b) : a*c ≤ b*d` — the 4th slot is the RIGHT side's FIRST factor
   (`0 ≤ b`), not the left's. Two silent mis-placements compiled to
   "Application type mismatch" naming the wrong factor.
2. **`mul_div_assoc` direction**: stated `(a*b)/c = a*(b/c)` — to turn
   `C * (X / |w|)` into `(C * X) / |w|` use `rw [← mul_div_assoc]`.
3. **`zero_lt_one.trans hk` needs `1 < k`** (`LT.lt.trans`); with
   `hk : 1 ≤ k` use `zero_lt_one.trans_le hk`.
4. **`rw [heq]` closes `a^(n+1) ≤ a^(n+1)` by its automatic `rfl`** — a
   trailing `exact le_refl _` then errors "No goals". Same for
   `rw [← pow_add]` on `s^(2n) * s^2 = s^(2n+2)` and for
   `rw [div_pow, mul_pow]` on fully syntactic identities: the rewrite
   alone can close; trailing `ring` must be dropped per-site.
5. **`positivity` cannot see through `sinv`** (an inverse-valued def): it
   proved `k^n ≥ 0` but failed on `sinv^(2n)`. Feed it
   `pow_nonneg (sinv_pos_of_abs_lt h).le (2*n)` explicitly. Same for the
   factorial-cast squeeze constant (`sqConst_pos` is manual:
   `Nat.factorial_pos` + `exact_mod_cast`).
6. **`abs_add` does not exist in v4.30** (rung-2 lesson re-hit): the
   triangle is `abs_add_le a b : |a + b| ≤ |a| + |b|`, used with `.trans`
   — not a rewrite.
7. **A `fun u _hu => ?_` binder that the body still needs** — the
   `< |u| < 1` branch proves `False` from `hu`; renaming to `_hu` kills
   the identifier. Elaboration order makes this surface as "Unknown
   identifier `hu`" far from the refine.
8. **`inv_le_inv₀ (ha : 0 < a) (hb : 0 < b) : a⁻¹ ≤ b⁻¹ ↔ b ≤ a`** — to
   DERIVE `1⁻¹ ≤ s⁻¹` from `s ≤ 1`, apply it as
   `(inv_le_inv₀ one_pos hs).mpr hs_le_1` (the ≤-statement sits on the
   LEFT of the iff). Getting the orientation wrong reads as a linarith
   failure one step later.
9. `mp.diff` on a piecewise-defined lambda is fine, but a rewritten
   recursion can agree with nothing at all (rel ≈ 1.0): a parity check
   with `rel ≈ 1` everywhere is a STRUCTURAL desync signature, not noise —
   diff the channel, do not tune the tolerance (F80 spirit).

## 4. Next steps (brick order stands)

1. **F2 (consumer)**: order-n IBP with boundary killed by
   `hasDerivAt_iterate_gevreyInner_ext`, per-term annulus mass via the
   A-machine (`Afunc`) + two-ring middle `Mfunc`, headline
   `‖L_φ(w)‖ ≤ e^{|Re w|} (2 * Afunc n k + Mfunc n k) / ‖w‖^n`, then the
   choose-n corollary with the record-1990 constants (c ≥ 1/2 certified
   for k ≥ 3; k = 1 b-slice refinement priced).
2. **Witness economics recompute** with the LEAN constants at
   `T_need ≈ 31.88` — the Cut-1 early kill-check (needs M_n ~ 7.5e-13 at
   λ = 1, n ~ 50; M_n ~ 7.8e-9 at λ₊ ≈ 70, n ~ 35–40).
3. **Resolution certificate** (record 1985's `cert_ok = FALSE` root cause)
   and the re-bracket of the 1981 GO_CANDIDATE.

No gate sign is proved here; RH is not claimed.
