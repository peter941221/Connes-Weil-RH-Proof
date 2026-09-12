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

## 8. Increment C GREEN (2026-09-13, try-2) and D GREEN (try-4)

`spectralNormTerm_shellSum_le_of_heightTail`: the per-shell instance summed
over every dyadic shell above the start `N + 1` gives the explicit geometric
budget

```
Σ' m, Σ' shell (m+N+1), spectralNormTerm square σ
    ≤ spectralMultiplicityConstant * Kc * r^N / (2^(4*(n+2)) - 3),
Kc = C_b^(2*(n+1)) * C_c^2 * (2*π)^(4*(n+2)),  r = 3 / 2^(4*(n+2)) ≤ 3/256.
```

Mirror of `spectralTail_norm_shellSum_le_of_fourthOrderTail`
(C1SpectralTailBound.lean:147-268) with NO `epsilon`, NO `T`, NO `rho`.  The
closing identity is `Σ r^m = 1/(1-r)` composed with
`2^{-4(n+2)}/(1-3/2^{4(n+2)}) = 1/(2^{4(n+2)}-3)`.  Build try-2: footer
`Build completed successfully (3545 jobs)`, zero `^error:`, three-standard-
axiom print, zero sorryAx.

`spectralWeilValue_neg_of_prefix_and_heightTail`: the composition lemma —
unchanged kill-based prefix accounting (`hprefix`) plus the height budget
(`hnb` explicit strict inequality) yields `spectralWeilValue square < 0`.
Height-tail mirror of
`spectralWeilValue_neg_of_spectralHeightShellPrefix_and_fourthOrderTail`
(C1HealthyYoshidaSpectralNegativity.lean:353-373); the `N+1` tail-start
bridge needs `simpa only [Nat.add_assoc, norm_spectralTerm]` because the
budget is stated in `spectralNormTerm` form while the consumer wants
`‖spectralTerm‖`.  Build try-4: `Build completed successfully (3634 jobs)`.

API notes hit in tries 1-4 (Lean v4.30 toolchain):

1. `pow_mul` in this Mathlib is `a ^ (m * n) = (a ^ m) ^ n`.  To convert
   `(x^a)^b = (x^b)^a` write `rw [← pow_mul, ← pow_mul]` then a targeted
   `mul_comm` on the exponents; a forward `rw [pow_mul]` rewrites the
   EXPONENT product of the composite base instead and silently changes the
   goal shape.
2. `summable_geometric_of_lt_one` / `tsum_geometric_of_lt_one` take
   `(0 ≤ r)` (NOT `-1 < r`), and the `tsum` form concludes `(1-r)⁻¹` —
   after `rw` into a `1 / (1-r)` goal, close with `ring`.
3. `Summable.of_le` does not exist in v4.30.  Use
   `Summable.of_nonneg_of_le (hg : ∀ b, 0 ≤ g b) (hgf : ∀ b, g b ≤ f b)
   (hf : Summable f)`; per-shell nonnegativity via `tsum_nonneg` with the
   `spectralNormTerm` rfl-unfold and `mul_nonneg`.
4. `field_simp` cancels NUMERAL-base factors (`3^m`, `(2*π)^k`) on its own
   and leaves a `pow_add`-shaped residual (`W^(m+N+1) = W * W^(m+N)`);
   close with an exponent-ring rewrite, `pow_add`, `pow_one`, `ring`.

## 9. Increments E1 + E3 GREEN (2026-09-13, try-6) — the N0' wrapper closes

Two recon facts reshaped the E ladder (both readbacks, no new analysis):

- The base quadratic bound is FREE:
  `exists_uniform_compactLog_laplaceAt_vertical_quadratic_decay`
  (C1SpectralWeil.lean:154-160) gives `∃ C, 0 ≤ C ∧ ∀ σ ∈ Icc 0 1, ∀ t,
  ‖t/(2π)‖²·‖laplaceAt F (σ + t·I)‖ ≤ C` for EVERY `CompactLogTest F` —
  no assembly change needed to export `C_b`; the correction's bound is
  exported verbatim by
  `exists_residualWindow_correction_with_quadratic_decay`
  (CC20YoshidaConvolution.lean:323-333, last conjunct exactly the `hC`
  shape).
- The half-density multiplier preserves support EXACTLY:
  `halfDensityShift_support_subset` (UnscaledYoshidaSelectedOwner.lean:64-67)
  — `exp(x/2)` has no zeros, so the detector's support clause is the
  assembled `(n+1)`-fold window with no shift term.

E1 `exists_nearbyZero_targetValues_assembly_anyIterate`: the target/kill
interpolation holds at ANY construction iterate — the assembled value is
`laplaceAt(base^n)(w) * laplaceAt(correction)(w)`, the base factor is
`1^(n+1)` at targets, and the correction vanishes at every non-target node
regardless of `n`.  The distance-form tail and its `T`/half-contraction
premises are dropped; the correction's quadratic bound is exported.  This is
the theorem that decouples `n` from the height of `rho`.

E3 `exists_smallSupport_healthyDetectorData_of_quadraticBounds_and_heightBudget`:
THE N0' WRAPPER.  Premises: healthy construction data (target values, square
kills over the `2^(N+1)`-ball plus route nodes), explicit quadratic bounds
`hB hC`, prefix coverage `hrhoShell : dyadicShellIndex |rho.1.im| < N + 1`,
and the budget `hnb`.  Conclusion:

```
∃ g, HealthyYoshidaDetectorData rho.1 g ∧
  support g.test ⊆ Ioo ((n+1)*baseLower + lower) ((n+1)*baseUpper + upper)
```

with NO `2 * |rho.im|` and NO `T` anywhere.  `n` is chosen by the budget;
`N` only covers the prefix.  Detector bookkeeping mirrors
:473-514 (`healthyUnscaledTargetValue_*` raw values), the negativity comes
from D via the unchanged prefix lemma
`spectralHeightShellPrefix_re_le_neg_xiMultiplicity_of_closedBall_square_zero_control`
(:298-327), and the support clause is
`halfDensityShift_support_subset ∘ convolution_support_subset_add_Ioo`.
Build try-6: `Build completed successfully (3634 jobs)`, zero `^error:`,
all NINE prints `[propext, Classical.choice, Quot.sound]`, zero sorryAx,
byte-identity verified.

E3 API traps (try-5, six errors):

1. Premise ORDER is semantics: referencing `N` in `hsquareZeros` BEFORE the
   `(N : ℕ)` binder made Lean auto-bind a DIFFERENT variable (`N✝`) — the
   application then failed with two visibly distinct `N`/`N✝`.  Bind `N`
   first.
2. `healthyDetectorData_halfDensityShift_of_raw_values_of_spectral_neg`
   takes the detection value in `bne` form; bridge with
   `(bne_iff_ne).mpr hdetect` (as the existing wrapper does at :509).
3. In the any-iterate assembly the intro'd kill hypothesis is a plain
   nonmembership (`↑z ∉ targetNodes`), NOT a subtype membership — no `.1/.2`
   projections; the node itself is already `FiniteMellinNode selectedNodes`
   up to let-zeta.

E2 deferred (next increment): the budget-discharge leaf
`∃ n, budget(n, N) < xiMult ρ` from the decay hypothesis
`C_b^2 * (2*π)^4 < 2^(4*(N+1))`.  Plan: `q := C_b^2 * (2*π)^4 /
2^(4*(N+1)) < 1`, per-n majorization `budget(n) ≤ c₀ * q^n` (uses
`1/(W-3) ≤ 2/W` for `W ≥ 6`), then `tendsto_pow_atTop_nhds_0` +
`Filter.Tendsto.eventually_lt_const`.  Power splits go through an
exponent-ring rewrite + `pow_add` (never a first-match `pow_mul` on
composite atoms).  hLow stays an ALTERNATIVE kill-free lane (D7/N4); the
wrapper above achieves `n`-only support with the prefix/kill accounting
unchanged.  Falsifiers F-1375-1/2/3: all survived.

## 10. Increment E2 GREEN (2026-09-13, try-15) — the budget leaf discharges

`exists_iterate_heightTail_budget_lt_xiMultiplicity` (the s9-preregistered
leaf, inserted after the E3 wrapper) is GREEN: under
`hdecay : C_b ^ 2 * (2 * π) ^ 4 < 2 ^ (4 * (N + 1))` there EXISTS `n` with

```
K · (C_b^(2(n+1)) · C_c² · (2π)^(4(n+2))) · (3/2^(4(n+2)))^N
    / (2^(4(n+2)) − 3)  <  xiMult ρ
```

i.e. the explicit geometric budget of `spectralNormTerm_shellSum_le_of_heightTail`
falls below the fixed positive constant `xiMultiplicity rho`.  The E3
wrapper's `hnb` premise is now dischargeable conditional on `hdecay`, and the
N0' ladder A→E3 is CLOSED at the formal level.  Build try-15:
`Build completed successfully (3634 jobs)`, zero `^error:`, all TEN prints
`[propext, Classical.choice, Quot.sound]`, zero sorryAx, byte-identity
verified.

Proof route (as preregistered, with two refinements):

1. `q := C_b²·(2π)⁴ / 2^(4(N+1)) < 1` (from `hdecay` via
   `div_lt_iff₀ hqden` + `linarith`), `c₀ := 2K·(C_b²C_c²(2π)⁸)·3^N /
   2^(8(N+1))`.
2. Per-`n` majorization `budget n ≤ c₀ · q^n`, `W := 2^(4(n+2)) ≥ 256`:
   step 1 is `1/(W−3) ≤ 2/W`, proved MULTIPLICATIVELY — `X·W ≤ X·2(W−3)`
   via `mul_le_mul_of_nonneg_left` (X ≥ 0) and `X·W ≤ 2X(W−3) ≤ 2X·(W−3)`
   — then converted to the quotient form inside
   `le_of_mul_le_mul_right ?_ (mul_pos hD1 hWpos)` with two `field_simp`
   equality rewrites `e1 e2`.
3. The bookkeeping equality `2X/W = c₀ · q^n` is a single deterministic
   20-step `rw` chain: `div_pow` ×2 + `mul_pow` to explode the pow-of-div
   terms, `← pow_mul` ×3 to flatten `C_b^(2n)`/`(2π)^(4n)`/`2^(4(N+1)n)`,
   `← mul_div_mul_comm` to merge the two divs of `q^n`, `← pow_add` for
   `2^(8(N+1) + 4(N+1)n)`, then the exponent identities `he1 he2 he3`
   (`ring`-closed haves).  ORDER MATTERS: the R-side merge steps run
   BEFORE the L-side `mul_div_assoc` chain — after the assoc steps the
   `q^n` div is nested inside R's numerator and `← mul_div_mul_comm` no
   longer matches.  Closed by `field_simp [hDne] <;> ring`.
4. Decay: `summable_geometric_of_lt_one hq0 hqlt` → `Summable.mul_left c0`
   → `.tendsto_atTop_zero` → `(hzero.eventually_lt_const hxipos).exists`
   → `lt_of_le_of_lt (hmajor n) hn`.  `xiMult ρ > 0` needs
   `Nat.cast_pos.mpr` (see trap 1).

API/trap ledger (tries 7-15, nine builds, Lean v4.30):

1. `exact_mod_cast` does NOT exist in this Mathlib — `Unknown identifier`.
   `0 < (↑k : ℝ)` from `0 < k` goes through `Nat.cast_pos.mpr`.
2. BY-BLOCK GARBAGE LAW (cost four builds): a `by tac` in an ARGUMENT
   position whose expected type still has unassigned metavars (e.g. first
   arg of `mul_le_mul_of_nonneg_right (by linarith) hX`, or
   `le_of_eq (by ring)` inside `le_trans`) elaborates the tactic against
   GARBAGE instantiations — here it manufactured a monster `K²·r^(2N)`
   polynomial goal and also splattered phantom failures onto unrelated
   lines (a `linarith failed` on a hypothesis whose own context was
   correct).  Fix: state the inequality/equality as a separate `have`
   with a FULLY CONCRETE type, then pass it; or `refine ... ?_` so later
   arguments fix the metavars first.
3. `mul_le_mul_of_nonneg_left (h : a ≤ b) (hc : 0 ≤ c) : c * a ≤ c * b`;
   `_right` multiplies on the right.  `_right (by linarith) hX` was both
   the wrong direction AND a by-block (trap 2).
4. `ring`/`ring_nf` CANNOT flatten `(x^a)^b` for VARIABLE exponents, nor
   equate numeral-base variants (`2^(8(N+1))` vs `256^N`).  All pow-pow
   forms must be rewritten via `← pow_mul` / `pow_add` BEFORE `ring`.
5. `field_simp` may close a simple equality completely; a trailing `ring`
   then errors `No goals to be solved`.  The robust idiom is
   `field_simp ... <;> ring` (fires only if goals remain).
6. A FAILED composite tactic rolls back, and the residual state it
   DISPLAYS is `ring_nf`-NORMALIZED — try-11's displayed
   `2 ^ (N * 8)` vs `256 ^ N` was an artifact; the TRUE post-`field_simp`
   residual (revealed in try-12 when `rw [h256]` could not find `256`)
   contains `2 ^ (8 * (N + 1))` and `(2 ^ (4*(n+2))) ^ N` unexpanded.
   Never write the next fix against the displayed form of a rolled-back
   state; probe with an identity `rw` first.
7. This Mathlib's `mul_div_mul_comm : a * b / (c * d) = a / c * (b / d)`
   — the ← direction MERGES a product of divs into one div.  In a long
   div-normalization chain, run every ← merge step while the target div
   is still CLEAN (top-level), before `mul_div_assoc` steps nest it.
8. Ops law re-confirmed (violation in try-8):
   `cp … && cmp … && nohup … & echo` — `&` binds looser than `&&`, so the
   WHOLE chain backgrounded and wsl.exe killed it; the build ran on the
   STALE file.  Sync (foreground, with `cmp` + marker `grep`) and the
   build launch are separate harness calls, never one `&`-chain.
9. `grep '\b…'` fails to match after a multibyte char (`₀`): `\b` is
   byte-oriented.  Use prefix matching (`error` not `\berror`) in
   log-greps over Lean identifiers.

Next: wire E1+E2+E3 into the orbit package (end-to-end instantiation,
ε = 1, `N = shell(ρ)+1`, MODEL digits only per law 65); the open science
interface is the `hdecay` discharge — `C_b` from
`exists_uniform_compactLog_laplaceAt_vertical_quadratic_decay` vs
`16^(N+1)` — then back to N1 (vertical bridge, `rho_b`) per the 1374
ranking.  Falsifiers F-1375-1/2/3: all survived (budget shape unchanged).

## 11. Increment F prereg: the orbit package (E1+E2+E3 wired end-to-end)

Composition analysis (register readbacks only, no new analysis): E3's four
`n`-dependent premises decompose as `hnb` = E2's discharge; `hB hC` =
constants (n-free); `htargetValues`/`hsquareZeros` = RAW node data plus the
assembly identity `laplaceAt (convolutionIterate base n .convolution c) w =
(laplaceAt base w)^(n+1) * laplaceAt correction w` (laplaceAt_convolution +
laplaceAt_convolutionIterate, CC20YoshidaConvolution.lean:465) and the
Hermitian bridge
`selectedOwner_laplaceAt_convolutionSquare_eq_zero_of_source_eq_zero`
(UnscaledYoshidaSelectedOwner.lean:336).

CIRCULARITY VERDICT: E2 fixes `(C_b, C_c)` before choosing `n`, so the
correction must exist ONCE, n-independently, before E2 runs — E1's
`exists correction AFTER n` interface cannot close the loop.  The correction
engine `exists_residualWindow_correction_with_quadratic_decay`
(CC20YoshidaConvolution.lean:323) takes only `(nodes, lower, upper, y)` —
all n-free — so the package is stated on RAW data.  FALSIFIER F-1375-4
pre-registered: the package fails if the assembly identity needs `n`-shaped
corrections (it does not: y is n-free).  Note `epsilon` is obsolete on this
route: the package carries no `T`/`epsilon` anywhere (both died with the
distance form); the MODEL-digits clause of law 65 has nothing to bind.

Two theorems, same leaf, added after E2:

F1 `exists_smallSupport_healthyDetectorData_of_heightDecay` — premises:
`rho` (+`hoff hright`), `routeNodes`, windows with `hlower hupper`,
`N` + `hrhoShell`, `{C_b C_c}` nonneg, `hdecay`, and two raw-data packages:
`hbaseData : exists base, support in (baseLower,baseUpper) AND base = 1 on
healthy targets AND quadratic bound <= C_b`; `hcorrData : exists correction,
support in (lower,upper) AND correction = healthyUnscaledTargetValue on
healthy targets AND correction = 0 at every node of
`sourceNontrivialZerosInClosedBallFinset rho.1 (2^(N+1)+2+dist 2 rho.1) UNION
routeNodes` outside the healthy targets AND quadratic bound <= C_c`.
Conclusion: `exists n g, HealthyYoshidaDetectorData rho.1 g AND support
g.test in the (n+1)-window`.  Proof: E2 picks `n`; raw->assembled targets via
the product identity; raw->square kills via the :336 bridge; E3 closes.

F2 `exists_smallSupport_healthyDetectorData_heightDecay_construction` — the
fully self-contained corollary: builds base (values `1` on healthy targets)
and correction (healthy values on `killSet UNION healthyTargets`, `y` the
dependent-if value function exactly as E1's) from the correction engine, and
concludes `exists C_b C_c, 0 <= C_b AND 0 <= C_c AND (C_b^2 (2pi)^4 <
2^(4(N+1)) -> exists n g, ...)`.  The exported decay antecedent IS the open
science interface (C_b vs 16^(N+1)); nothing numerical is claimed.

Acceptance gates: try-N green with 3634+ jobs, 0 errors, 12 axiom prints
(10 old + F1 + F2) all `[propext, Classical.choice, Quot.sound]`, 0 sorryAx,
byte-identity; no numerical prereg needed (pure formal increment).

F1+F2 OUTCOME (2026-09-13, try-2): both GREEN in one build.
`Build completed successfully (3634 jobs)`, zero `^error:`, all TWELVE
prints `[propext, Classical.choice, Quot.sound]`, zero sorryAx,
byte-identity verified.  The falsifier F-1375-4 did not fire.

What F1+F2 give the register: the N0' ladder A→E3 now has a SINGLE
entry point — F2 takes only `(rho, hoff, hright, routeNodes, windows, N,
hrhoShell)` and returns `(C_b, C_c, decay → ∃ n g, HealthyYoshidaDetectorData
∧ support ⊆ (n+1)-window)`.  The correction engine's inputs are n-free, so
the circularity feared in the prereg (E2 fixes constants before choosing n)
never materializes: base and correction are built ONCE, E2 picks n, and F1
rebuilds the assembled values and square kills at that n from the raw node
data.  The decay antecedent on the CONSTRUCTED `C_b` is the open science
interface (C_b vs 16^(N+1)); nothing numerical is claimed.

Try-1 errors (three roots, all shallow):

1. The Hermitian bridge consumes ASSEMBLED kills, not raw kills — its `hz`
   is `laplaceAt ((convolutionIterate base n).convolution correction) z = 0`.
   Raw correction kills transfer in two lines via the product identity
   (`rw [laplaceAt_convolution, laplaceAt_convolutionIterate, hcorrKills w
   hw]; simp`) — a zero factor kills the product, so NO base-value
   hypothesis is needed at the kill nodes.
2. Anonymous-constructor flattening: `⟨n, _, proofOfExistsG⟩` against
   `∃ n, ∃ g, P ∧ Q` mis-parses (three components read as n/g/P).  Give the
   nested ∃ value directly: `⟨n, proofOfExistsG⟩`.
3. PRECEDENCE: `∧` binds tighter than `→` — `0 ≤ C_b ∧ 0 ≤ C_c ∧ decay → D`
   parses as `(0 ≤ C_b ∧ (0 ≤ C_c ∧ decay)) → D`.  Parenthesize the arrow
   tail: `... ∧ (decay → D)`, and close the paren at the statement end.

Log-verification note: the axiom-print lists WRAP across log lines, so a
single-line pattern like `propext, Classical.choice, Quot.sound]` finds
nothing.  Check instead that (a) `depends on axioms` count = expected
prints, (b) every `-A1` continuation line is the SAME class (`uniq -c` size
1), (c) `Quot.sound]` appears exactly once per print.

The orbit package is CLOSED formal-side.  Remaining: the hdecay discharge
(open science, C_b vs 16^(N+1)), then back to N1 (vertical bridge, rho_b)
per the 1374 ranking.  RH NOT claimed.
