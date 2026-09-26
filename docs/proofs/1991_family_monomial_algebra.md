# Record 1991 — Family brick F1a LANDED: the optimized-n monomial algebra is now Lean theorems (invariant set, three-ratio machine A_{n+1} ≤ (n + 16n²/k)·A_n, product envelope with A_1 = 6/5, coefficient sum ≤ 5ⁿn!); 17 declarations, all std axioms, zero sorryAx, zero new warnings

- **Date**: 2026-09-26
- **Status**: LANDED (Lean brick)
- **Brick**: `ConnesWeilRH/Dev/C1GevreyFamilyMonomials.lean` (namespace
  `GevreyFamily`, ~430 lines) + audit
  `ConnesWeilRH/Dev/C1GevreyFamilyMonomialsAudit.lean`
- **Build logs**: `build-logs/f1a_build5.log` (module, 0 errors / 0 warnings),
  `build-logs/f1a_audit.log` (17 × `#print axioms`),
  `build-logs/f1a_fullbuild.log` (full `lake build`, success)
- **Spec**: record 1990 (desk wave; the constants and the machine shape were
  40-dps-pre-checked there — this brick formalizes §1(a)/(b) minus calculus)

## 1. What landed

The pure-algebra layer of the optimized-n family induction (no calculus —
`phi_k` and the Laplace transform enter only in later bricks):

| theorem | statement (informal) | record-1990 source |
|---|---|---|
| `mono_invariant` | every level-n term has `a ≤ n`, `p ≤ n`, `b ≤ 2n`, `2 ≤ b` (n ≥ 1) | §1(a) |
| `weight` / `Afunc` | `weight = |c|·k^{p+1}/k^b·Γ(b-1)`; `A_n = (3/5)·Σ weight` | §1(b) |
| `weight_move1/2/3` | the three moves scale a weight by exactly `a`, `2b(b-1)/k`, `2b(b-1)/k` (Γ-recurrences) | §1(b) table |
| `children_weight_sum_le` | per-parent child-weight sum = `(a + 4b(b-1)/k)·w` (equalities, no slack) | §1(b) |
| `Afunc_step` | `A_{n+1} ≤ (n + 16n²/k)·A_n` | §1(b) headline |
| `Afunc_envelope_aux` + `Afunc_one` | `A_{m+1} ≤ (6/5)·Π_{j<m}(j + 16j²/k)` | §1(b) envelope |
| `children_abs_sum_eq` / `sumAbs_step` / `sumAbs_le` | `Σ|c|`-machine: per-parent `a+2b+2`, step `(5n+2)`, bound `5ⁿ·n!` | M_n feeder |
| `monos_one` | executable cross-check: `monos 1 = [-2ku s⁻²]` (matches rung-1) | sanity |

Design choices frozen for the later bricks:

- **`children` mirrors the 1990 recursion including the conditional drops**
  (`u`-move only if `a ≥ 1`, first `s`-move only if `b ≥ 1`) — the drops are
  needed so the level-(n≥1) invariant `2 ≤ b` survives induction; the seed
  case (`monos 0 = [1]`) is handled by `mem_children_seed` (its only child is
  the rung-1 term).
- **The mixed coefficient form `↑n + ↑(16n²)/k` is now load-bearing**: the
  `a`-term is NOT divided by k. A first draft flattened it to
  `(n + 16n²)/k`; `ring_nf` exposed the mismatch (`↑m.a·w` vs `↑m.a·w/k`)
  and the statement was corrected before landing.
- `weight` is written as a quotient `k^(p+1)/k^b` (no `zpow`), and `Real.Gamma (b-1)`
  with REAL subtraction `(↑b - 1)` — the elaborator's choice from the match
  body, embraced everywhere.

## 2. Honesty box

- **No calculus yet**: this brick proves statements ABOUT the monomial lists
  and weights; it does not yet prove `phi_k^(n) = e^{-k/s}·B_n` (F1b), the
  boundary flatness/glue (F1c), nor the IBP consumer (F2).  The A-machine is
  formal; its APPLICATION to `|L_phi(iT)|` is not.
- The exact per-term identity `b - p = (n+a)/2` of record 1990 §1(a) is
  deliberately NOT formalized (the ratio machine has no consumer for it; it
  prices a later sharpening brick).
- `weight_move1` is an unconditional equality (the truncated `a-1` is
  harmless since the weight ignores `a`); the dropped child contributes
  nothing — both facts are used, not hidden.
- The upper-bound character (triangle inequality, Γ-completion) is inherited
  from record 1990 unchanged; sharpness is NOT claimed.
- No gate sign; RH not claimed.

## 3. v4.30 elaboration hazards hit this wave

Full lesson list (mirrored into the internal WSL-side hazard catalogue):

1. `Nat.cast_sub (by omega)` inside a typed `have`: elaboration order let the
   OUTPUT-type unification instantiate the lemma's implicit `m := 2` from a
   context hypothesis BEFORE the `by omega` argument was typed — producing
   `Nat.cast_sub hb : ↑(m.b - 2) = ↑m.b - ↑2`.  Fix pattern: feed the
   arithmetic through a FULLY-TYPED lemma application
   (`Nat.cast_le.mpr hb : (2:ℝ) ≤ ↑m.b`) and finish with `linarith`.
2. `simp only` eats `0 < x ∧` guards: when the guard hypothesis is a simp
   argument, the conjunction `(0 < m.a ∧ m' = c1)` in the goal reduces to
   `m' = c1` — the delivery tactic must not re-pair the guard (`⟨h1, h⟩`
   type-mismatches).  Restructure: `rcases` the bare disjunction.
3. `abs_mul` without explicit args fragments nested products unpredictably:
   `|2 * ↑m.b|` inside `|m.c * (2*↑m.b)|` gets split into `|2|*|↑m.b|` and
   eats an `abs_mul` from the budget, leaving `|m.c * -2|` unexposed so
   `abs_neg` finds no `|-?a|`.  Fix: pin EVERY rewrite:
   `rw [abs_mul m.c ↑m.a, abs_mul m.c (2 * ↑m.b), abs_of_nonneg (… 2 * ↑m.b …), …]`.
4. Boolean-split branches must rewrite the forced value: in the
   `¬(0 < m.b)` branch the claim needs `m.b = 0` (`hbz := by omega` + `rw`),
   otherwise `ring` faces a symbolic `↑m.b` it cannot cancel.
5. `div_le_div_of_nonneg_left` is `0 ≤ a → 0 < c → c ≤ b → a/b ≤ a/c` — it
   compares DIVISORS, not numerators.  For same-divisor comparison use
   `div_eq_mul_inv` + `mul_le_mul_of_nonneg_right`.
6. `mul_le_mul_right'` changed signature in v4.30 (deprecated; the constant
   now leads differently).  `mul_le_mul_of_nonneg_right h hc` verified
   working — prefer it.
7. Unused simp args are now a WARNING (`linter.unusedSimpArgs`) —
   `List.map_append`/`List.sum_append` must be dropped when
   `nil_append`+`cons_append` already normalize the (left-assoc) append chain.
8. `norm_num` does not fold `↑m.b + 2 - 1` (atom inside) — use `ring`.
9. `field_simp` may close the goal entirely — a trailing `ring` then errors
   "No goals to be solved".  Check which tactic actually finishes.
10. Structure projections in `rw`-ed goals: after `rw [heq]` the goal has
    `Mono.a ⟨…⟩`; close components with `show … by omega` (defeq-reduces the
    projection) instead of `subst` + omega.

## 4. Next steps (the brick order stands)

1. **F1b (identification)**: `HasDerivAt` chain proving
   `phi_k^(n) = e^{-k/s}·B_n(u)` inside `|u| < 1`, with `B_n` the sum over
   `monos n` — the monomial machinery above is its algebra skeleton.
2. **F1c (shape + glue)**: `|B_n(u)| ≤ S_n·kⁿ·s^{-2n}` with
   `S_n ≤ (Σ|c|)·(2n-sup)` (feeds `sumAbs_le`), then the C^∞ flatness/glue
   at `u = ±1` (brick-1 pattern).
3. **F2 (consumer)**: order-n IBP with boundary killed by F1c,
   `|L_phi(w)| ≤ e^{|Re w|}(A_n + M_n)/|w|^n`, then the choose-n corollary
   `e^{-c_env·sqrt(k|T|)}` with the record-1990 §1(d) constants; the
   two-ring middle bound `M_n` lands alongside (its `Σ|c|` feeder is now a
   theorem).

No gate sign is proved here; RH is not claimed.
