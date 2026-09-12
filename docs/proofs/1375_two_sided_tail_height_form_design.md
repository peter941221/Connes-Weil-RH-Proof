# 1375 - N0' design: height-form two-sided tail for the selected square

Date: 2026-09-13. Consumes [1372](1372_phase_diagram_total_variant_attack.md)
(N0' task ledger) and [1374](1374_phase_rig_outcome.md) s4 (ranking: N1 >
N0' > N2 > N3 > N4). This is a FORMAL design record written before any leaf
is built; no MODEL digits are involved. Evidence class for the mathematical
claims below: READBACK of existing formal statements, with file:line cites
against the working tree at this commit.

## 1. The one-point root cause of the support blow-up

The construction family accepts any radius (`∀ R : ℝ, 0 ≤ R → ...`,
CC20YoshidaConvolution.lean:1026), the assembled support is
`((n+1)*baseLower+lower, (n+1)*baseUpper+upper)` (ibid. :1030-1032) — a
function of `n` alone — and `n` is produced by
`exists_convolutionIterate_convolution_distance_bound_lt`, which depends on
`epsilon, C, T`, not on `rho`. Nothing in the construction forces
`R ≈ |Im rho|`.

The pin lives entirely in the TAIL interface:
`FourthOrderSpectralTail` carries the hypothesis `2 * |rho.im| <= |z.im|`
(C1SpectralTailBound.lean:33), and its sole use inside the machinery is the
conversion of shell height into DISTANCE from `rho`:
`(2:Real)^n <= |sigma.1.1.im - rho.im|` (C1SpectralTailBound.lean:70-74),
which feeds the distance weights `‖z - rho‖^2 * ‖(1 - star z) - rho‖^2` of
the fourth-order bound. Through the budget lemma
`exists_dyadic_tail_start_with_budget_lt_xiMultiplicity` (consumed at
C1HealthyYoshidaSpectralNegativity.lean:533-534) this forces
`n0 >= log2 max(T, 2|Im rho|)`, hence ball radius
`2^(n0+1) + 2 + dist 2 rho` (ibid. :535) and — via the wrapper's tail-start
coupling — the current wrapper's effective support scale.

Conclusion: to unlock small `R`, replace the DISTANCE-form tail with a
HEIGHT-form tail. One such tail already exists in disguise: the quadratic
frequency bounds are GLOBAL (no height restriction, no rho):

- base contraction premise, CC20YoshidaConvolution.lean:184-186:
  `‖t / (2*π)‖^2 * ‖laplaceAt base (sigma + t·I)‖ <= C`, for ALL
  `sigma ∈ Icc 0 1, t : ℝ`;
- correction: same shape, exported internally by
  `exists_residualWindow_correction_with_quadratic_decay` (used in the proof
  of the assembly theorem, ibid. :1049 ff., as the `hC` premise of the
  distance-bound theorem).

Dividing by `(t/2π)^2` (valid at any `|t| > 0`): every strip point of
height `t` obeys `‖laplaceAt f z‖ * |t|^2 <= C * (2π)^2`. The assembled
value is a product
(`laplaceAt_convolution`, `laplaceAt_convolutionIterate` = power `n+1`,
CC20YoshidaConvolution.lean:465-467), and the selected square factors as the
Hermitian product
`laplaceAt (selectedOwner b c n).convolutionSquare (z - 1/2) =
 star (laplaceAt h (1 - star z)) * laplaceAt h z`
(UnscaledYoshidaSelectedOwner.lean:153-159), with
`(1 - star z).im = z.im` (ibid. :426-427). Hence the two-sided
HEIGHT-form tail:

```
‖laplaceAt (selectedOwner b c n).convolutionSquare (z - 1/2)‖
    * |Im z|^(4*(n+2))
  <= C_b^(2*(n+1)) * C_c^2 * (2*π)^(4*(n+2))
```

for EVERY `z` in the strip with `0 < |Im z|`, no `rho`, no `T`, no
`epsilon`, no `2*|Im rho|`. This is N0'-a. It is a two-sided tail in the
sense that it covers BOTH mid heights (where the distance-form tail was
unavailable because `2|Im rho|` fails) and high heights (where it overlaps
the old tail).

## 2. The low-height obstruction and its resolution (hLow)

Height-form decay cannot cover `|Im z| → 0`: the quadratic bound degenerates
there, and absorption by a fixed budget is impossible anyway because the
detector value at the anchor node is 1 BY CONSTRUCTION
(`hbaseTargets`, CC20YoshidaConvolution.lean:1015-1016), so no global
sup-norm of the assembled test can be small. Formally: zeros with height
below the useful range have uncontrolled square values and finitely-many
but nonzero total contribution; killing them requires a ball of radius
`≈ |Im rho| + T_max` — the linear-in-rho behavior N0' exists to remove.

Resolution: the wrapper carries the hypothesis

```
(hLow : ∀ z ∈ sourceNontrivialZeros, gamma0 <= |z.im|)
```

for a fixed certificate height `gamma0` (target: 50, backed by the
Platt-Trudgian-class verified zero-free strip; the exact constant is a
D7/N4-lane input, RH-independent). Under `hLow` EVERY source zero is inside
the height-tail range, no ball kill is needed at all, and the negativity
chain becomes: orbit anchor `<= -xiMultiplicity rho` plus a height-shell
sum bounded by `K(n) * (shell summation constant)`. This is the same
anchor-plus-tail architecture as
`selectedOwner_spectralWeilValue_neg_of_closedBall_square_zero_control_and_fourthOrderTail`
(C1HealthyYoshidaSpectralNegativity.lean:412-443) with the closed-ball
prefix replaced by "empty below gamma0" and the fourth-order tail replaced
by the height tail. The final RH exit consumes the wrapper only through its
conclusion, and discharges `hLow` through the D7/N4 certificate lane — an
hypothesis import at an intermediate node is legitimate; it is not a
hypothesis of the final theorem.

## 3. Increment ladder (each its own leaf + build)

- A  `laplaceAt_le_of_quadraticBound`: point evaluation of a quadratic
     frequency bound, multiplicative form
     `‖laplaceAt f z‖ * |Im z|^2 <= C * (2*π)^2`.
- A' `convolved_laplaceAt_heightDecay`: product over the `(n+1)`-fold base
     iterate and the correction; exponent `2*(n+2)`.
- A'' `selectedOwner_convolutionSquare_heightTail`: the two-sided square
     tail above; exponent `4*(n+2)`; constant
     `C_b^(2*(n+1)) * C_c^2 * (2*π)^(4*(n+2))`.  THIS INCREMENT = A, A',
     A'' in `ConnesWeilRH.Dev.C1SelectedSquareHeightTail` + Audit.
- B  per-shell spectral-term instance, mirror of
     `spectralTerm_norm_tail_instance_of_fourthOrderTail`
     (C1SpectralTailBound.lean:42-80) with the height tail: for
     `sigma : spectralHeightShell k`,
     `‖spectralTerm F sigma.1‖ <= xiMultiplicity sigma.1 * K / 2^(k*4*(n+2))`.
- C  shell-sum budget: `Σ' m, Σ' z : spectralHeightShell m, ‖spectralTerm‖
     <= K * (explicit geometric constant)`; mirror of
     `spectralTail_norm_shellSum_le_of_fourthOrderTail` internals.
- D  anchor-without-kills: prefix re-sum `<= -xiMultiplicity rho` up to the
     non-orbit contribution of the orbit shell; mirror of
     `spectralHeightShellPrefix_re_le_neg_xiMultiplicity_of_closedBall_control`
     internals. RISK: the closed-prefix lemma's internal accounting must be
     readable; if the orbit-shell split is not reusable, restate via
     `spectralWeilValue_neg_of_spectralHeightShellPrefix_and_tail`
     (ibid. :332-349) with `N = 0`-style full-sum premise.
- E  wrapper: assembly variant that EXPORTS the base/correction quadratic
     bounds (internal today), plus `hLow`, plus budget hypothesis
     `hnBudget`; conclusion `∃ g, HealthyYoshidaDetectorData rho.1 g` with
     support `⊆ Ioo (-(n+2)) (n+2)` from the assembly's own support clause
     (CC20YoshidaConvolution.lean:1030-1032) — `n`-only, never `|Im rho|`.
     Budget discharge by epsilon-shrinking is a SEPARATE later increment
     and requires reading the n-choice in
     `exists_convolutionIterate_convolution_distance_bound_lt`; until then
     `hnBudget` stays an explicit hypothesis.

## 4. Sanity of the constant (mental arithmetic only, no MODEL claim)

At `n = 3`, `C_b = 1`, `C_c = 3`, `gamma0 = 50`: per-zero square value
`<= 9 * (2π)^20 / 50^20 ≈ 7e-18`; even multiplied by shell-count growth the
total is far below `xiMultiplicity >= 1`. The formal budget will be proved
abstractly (B/C), so this paragraph carries zero verdict weight.

## 5. Falsifiers / abort conditions

- F-1375-1: if A'' fails to build after the algebra is exhausted, the
  Hermitian-product route (centered lemma) is wrong somewhere — abort and
  re-read `selectedOwner_laplaceAt_convolutionSquare_centered`.
- F-1375-2: if B's instance cannot avoid `2*|Im rho|` because
  `spectralTerm` itself carries distance weights, inspect `spectralTerm`'s
  definition; the existing fourth-order instance (C1SpectralTailBound
  :42-80) shows the weights are ABSENT from `spectralTerm` and supplied by
  the tail premise — if that readback is wrong, the design dies here.
- F-1375-3: if D's anchor cannot be produced without ball kills, fall back
  to a `hLow`-strengthened prefix that kills only the finitely many zeros
  below an ABSOLUTE height (independent of rho), still removing the
  linear-in-rho ball; that fallback is strictly weaker but sufficient for
  the small-R wrapper.

## 6. Build outcome (2026-09-13, increment A/A'/A'' GREEN)

All three leaves landed in `ConnesWeilRH.Dev.C1SelectedSquareHeightTail` +
paired Audit; owning-target build try-8: footer
`Build completed successfully (3498 jobs)`, zero `^error:` lines, and all
three `#print axioms` read back exactly `[propext, Classical.choice,
Quot.sound]` (zero sorryAx). Log: WSL mirror
`build-logs/1375_height_tail_try8.log` (gitignored, not an artifact).

Statement-form amendment (made during try-1, BEFORE any green build): the
s3 statements were restated into the house DIVISION-FREE form — the engine
lemma now reads `‖z.im / (2*π)‖^2 * ‖laplaceAt f z‖ <= C` directly (mirror
of `norm_sub_sq_mul_laplaceAt_le_of_vertical_quadratic_bound`,
CC20YoshidaConvolution.lean:710-718, whose docstring already announces this
shape for dyadic-shell estimates), and the two decay lemmas multiply the
GLOBAL frequency factor `‖z.im / (2*π)‖^(2*(n+2))` / `^(4*(n+2))` against
the Laplace value instead of dividing it out. Gains: no `0 < |Im z|`
hypothesis, no `div_le_iff₀`/positivity work, and the statement is exactly
what Leaf B (per-shell instance) consumes. Constants kept composite:
`C_b^(n+1) * C_c` and `C_b^(2*(n+1)) * C_c^2` (see API note 3 below).

Final names:

- `laplaceAt_heightQuadratic_le_of_quadraticBound`
- `convolved_laplaceAt_heightQuadratic_le`
- `selectedOwner_convolutionSquare_heightQuadraticTail`

API notes for the next leaves (all hit in tries 1-8, Lean v4.30 toolchain):

1. Point decomposition `z = ↑z.re + ↑z.im * I` must NOT be materialized and
   then rewritten; the house pattern is to apply the ∀σ∀t bound at
   `(z.re, z.im)` and `simpa only [Complex.re_add_im] using h`
   (CC20YoshidaConvolution.lean:701-705).
2. `pow_le_pow_left₀ (h0 : 0 ≤ a) (hab : a ≤ b) (n)`: the base-nonneg arg
   must be the WHOLE product (`mul_nonneg ...`), and `sq_nonneg` cannot
   witness `0 ≤ x^(2*(n+2))` (non-literal exponent) — use
   `pow_nonneg (norm_nonneg x) _`. `norm_nonneg` takes the INNER term:
   `norm_nonneg (z.im / (2*π))`, not `norm_nonneg ‖z.im / (2*π)‖`.
3. `ring` cannot identify `4^n = 2^(2n)`: never close an equality that
   regroups powers of the COMPOSITE atom `(2*Real.pi)` across different
   exponent groupings; keep constants composite (`C_b^(n+1) * C_c`), and
   for powers of one atom use `pow_add`/`mul_pow` rewrites + `ring` only
   for reordering.
4. `mul_le_mul` argument order in this Mathlib: `(hab) (hcd) (0 ≤ c)
   (0 ≤ b)` — the nonneg side conditions are for the SECOND LHS factor and
   the FIRST RHS factor. `0 ≤ C_b`/`0 ≤ C_c` are NOT hypotheses of the
   division-free lemmas; derive them from `hB`/`hC` via
   `le_trans (mul_nonneg (sq_nonneg _) (norm_nonneg _)) (hB z.re hzre 1)`.
5. calc tactic-block indentation must be >= the indentation of the
   expression lines of that step; a shallower tactic line is parsed as an
   expression continuation ("expected '{' or indented tactic sequence")
   and cascades into bogus unsolved-goal errors.
6. A `noncomputable section` needs its own bare `end` before the namespace
   `end`s (matches C1A2WindowSplit.lean closing convention).

Falsifier F-1375-2 status: `spectralTerm` carries NO distance weights —
the weights are supplied entirely by the tail premise
(C1SpectralTailBound.lean:42-80 readback confirmed during design), so Leaf
B (per-shell height instance) is unblocked. Next: B, then C (shell-sum
budget), D (anchor without kills), E (wrapper with exported quadratic
bounds + hLow + hnBudget).

## 7. Increment B GREEN (2026-09-13)

Two theorems appended to the same module; shell build try-5: footer
`Build completed successfully (3545 jobs)`, zero `^error:`, five prints
all `[propext, Classical.choice, Quot.sound]`, zero sorryAx, byte-identity
verified.

- `selectedOwner_convolutionSquare_heightTail_raw`: raw-height restatement
  `‖square(z−1/2)‖ * |Im z|^(4*(n+2)) <= C_b^(2*(n+1)) * C_c^2 *
  (2*π)^(4*(n+2))` — the global frequency factor is traded for an explicit
  `(2*π)` power so the statement compares `|Im z|` DIRECTLY against dyadic
  shell heights. Bridge lemma `‖z.im/(2π)‖ * (2π) = |z.im|` proved once and
  reused (`field_simp` with a `2*π ≠ 0` hypothesis in context).
- `spectralNormTerm_shell_instance_of_heightTail`: for
  `sigma : spectralHeightShell (k+1)`,
  `spectralNormTerm square sigma.1 * ((2:Real)^(k+1))^(4*(n+2)) <=
  xiMultiplicity sigma.1 * (constant)` — the height-form mirror of
  `spectralTerm_norm_tail_instance_of_fourthOrderTail` with the three
  distance hypotheses (`T`, `1 <=`, `2*|rho.im| <=`) replaced by NOTHING.
  `spectralTerm`/`spectralNormTerm` carry no distance weights
  (C1SpectralWeil.lean:112-121); the shell instance is pure height
  geometry via `shell_lower_im`.

API notes: `spectralNormTerm` unfolds by `rfl`; after that rewrite the goal
is LEFT-associated `(xi * ‖·‖) * pow`, so pre-empt with `rw [hterm,
mul_assoc]` and state the calc steps right-associated;
`mul_le_mul_of_nonneg_left hpow (norm_nonneg _)` for shared-factor-on-LEFT
bridges (the `_right` variant puts the shared factor on the right).

Increment C next: sum the instance over all shells into the explicit
budget `K(n) * (shell summation constant) < xiMultiplicity rho`, mirroring
the geometric internals of `spectralTail_norm_shellSum_le_of_fourthOrderTail`.
