# 1414 — Campaign brick 3 GREEN: `C1PsiSectorSplit`, kill (a) is now fully machine-checked

Wave: F2 formal campaign (brick 3 of 4). Depends on: 1412 (brick 1
`C1PsiBlindness`), 1413 (brick 2 `C1PsiLinearity`).
Status: **GREEN — 19 declarations (2 defs + 2 rfl accessors + 15
theorems), 17/17 standard-axiom trios, 0 error, 0 `sorryAx`, build
footer `Build completed successfully (3479 jobs)`**.
Zero rig digits in this record (law 65 discipline). **RH is not
claimed.**

+========================================================================+
| [1] WHAT THE BRICK IS                                                   |
+========================================================================+

Brick 1 proved: odd tests die (`psi f = 0`). Brick 2 proved: sums
split (`psi (f + g) = psi f + psi g`, hypothesis-free on the square
class). Kill (a) of record 1406 — "`psi` reads only the reflection-even
sector of its test argument; the imaginary-odd Chuk cross term
`F_d = 2i · odd` contributes nothing" — needed one more fact to be a
complete machine statement: INVARIANCE. Brick 3 supplies it:

  `psi_reflection : psi f.reflection = psi f` — UNCONDITIONAL.

And the reason it is unconditional is structural, found by transcribing
the kernel definitions verbatim (law F18), C1SameOwnerWeil.lean:31-64:

  +--------------------------------+---------------------------------+
  | readout                        | symmetry under f ↦ f.reflection |
  +--------------------------------+---------------------------------+
  | poleTerm (pair ±1/2)           | swaps the pair:                 |
  |                                | laplaceAt f.reflection s        |
  |                                |   = laplaceAt f (-s)            |
  |                                | (x ↦ -x change of variables)    |
  +--------------------------------+---------------------------------+
  | finitePrimeTermComplex kernel  | pointwise FIXED:                |
  | F(log n) + F(-log n)           | the sum is symmetric by         |
  |                                | construction                    |
  +--------------------------------+---------------------------------+
  | globalPrimeIndexSet            | therefore EQUAL (same filter    |
  |                                | on the same range)              |
  +--------------------------------+---------------------------------+
  | archimedeanNumerator           | pointwise FIXED:                |
  | e^{y/2}(F y + F (-y)) - 2F 0   | (and F 0 -> F (-0) = F 0)       |
  +--------------------------------+---------------------------------+
  | archimedeanTerm integral       | integral_congr_ae on the        |
  |                                | pointwise identity — no         |
  |                                | integrability bookkeeping       |
  +--------------------------------+---------------------------------+

Declaration list (leaf `ConnesWeilRH/Dev/C1PsiSectorSplit.lean`, audit
`...Audit.lean`):

  1  laplaceAt_reflection          9  archimedeanIntegrand_reflection
  2  poleTerm_reflection           10 archimedeanTerm_reflection
  3  finitePrimeTermComplex_reflection  11 psi_reflection  [TOP]
  4  finitePrimeTerm_reflection    12 evenSym2 / evenSym2_apply
  5  mem_globalPrimeIndexSet_reflection_iff  13 oddDiff2 / oddDiff2_apply
  6  globalPrimeIndexSet_reflection_eq  14 oddDiff2_odd
  7  finitePrimeSum_reflection     15 psi_oddDiff2_eq_zero
  8  archimedeanNumerator_reflection  16 testAdd_evenSym2_oddDiff2
                                     17 psi_evenSym2 (conditional)

Sector language: since no scalar layer exists (by design, brick 2),
the projections are DOUBLED forms: `evenSym2 f = f + f.reflection`
(= 2 × even part), `oddDiff2 f = f - f.reflection` (= 2 × odd part).
The two corollaries: the doubled odd part is annihilated
unconditionally (brick 1 consumes `oddDiff2_odd`), and
`evenSym2 f + oddDiff2 f = f + f` as tests — the exact decomposition
identity, doubled. `psi_evenSym2 f = psi f + psi f` carries the two
`IntegrableOn` hypotheses that `psi_testAdd` itself carries (honest
scope, not invented).

+========================================================================+
| [2] INVOCATION LEDGER                                                   |
+========================================================================+

  +------+-------------------------------------------+---------+
  | pass | action                                    | result  |
  +------+-------------------------------------------+---------+
  | try1 | first leaf write                          | 67      |
  |      | (fast single-file lake env lean)          | errors, |
  |      |                                           | ALL one |
  |      |                                           | cascade |
  +------+-------------------------------------------+---------+
  | try2 | + missing `import` line                   | 13      |
  |      | + nested-namespace open for               | errors  |
  |      |   reflection_apply + unfold-evenSym2      |         |
  +------+-------------------------------------------+---------+
  | try3 | 5 fixes ([3] classes I..L)                | 5       |
  |      |                                           | errors  |
  +------+-------------------------------------------+---------+
  | try4 | rewrite of the 5 sites                    | 0 error |
  +------+-------------------------------------------+---------+
  | build| acceptance build (leaf + audit)             | GREEN   |
  |      | 3479 jobs, 17/17 trios, 0 error, 0 sorryAx, |       |
  |      | 0 warnings attributable to the new files  |         |
  +------+-------------------------------------------+---------+

Acceptance log: `build-logs/c1psi-sector-try3.log` (WSL ext4 mirror);
marker counts taken with DIRECT literal paths per the rule re-burned in
1413 — first try on this brick.

+========================================================================+
| [3] FAILURE CLASSES                                                     |
+========================================================================+

Class H (meta-lesson, costliest wall-clock) — missing import cascades
into 67 "independent" errors: every `open` line errors "unknown
namespace", every proof body then errors downstream. Rule: when the
first errors are namespace-shaped, STOP and read the file's own
preamble before touching a single proof. (This brick's try1 never
reached its real bugs; try2 exposed them.)

Class I — numeral-negation normal forms. `poleTerm`'s statement writes
`laplaceAt F (-1 / 2)`, which parses as `(-1)/2` (negated literal,
then division); the rewrite result carries `-((-1)/2)` where
`simp only [neg_neg]` makes NO progress — the inner node is `HDiv`,
not `Neg`. `neg_div` must fire first to expose the double negation.
Fix shape: `simp only [laplaceAt_reflection, neg_div, neg_neg]` then
`rw [add_comm]`.

Class J — `rw [h, h]` on an iff: `mem_globalPrimeIndexSet_iff`
instantiates `?F := f.reflection` on the left in pass one and
`?F := f` on the right in pass two; a SINGLE pass rewrites only the
first instantiation's occurrences and leaves the other side in the
old form (then the term-level rewrite yields an unsolved mixed goal).
One rw-list entry PER side needed. (My brick-2-era "drop the duplicate"
instinct was wrong here; the duplicate was load-bearing.)

Class K — annihilation lemma argument order: `psi_eq_zero_of_odd`
takes the FUNCTION first, the oddness proof second. Passing
`(f, oddDiff2_odd f)` yields a mismatch whose expected type mentions
the wrong function — easy to misread as a shape problem.

Class L — `.test` is a `SchwartzMap` (bundled), not a bare `Pi`:
`funext` fails ("could not unify the conclusion") on goals
`f.test = g.test`; the `ext x` tactic reaches
`SchwartzMap.ext` correctly.

+========================================================================+
| [4] MACHINE / MODEL BOUNDARY                                            |
+========================================================================+

Now machine facts, the full kill-(a) bundle:

  1. psi annihilates odd tests.                      [brick 1]
  2. psi splits pointwise sums (conditional; free on square class).
                                                     [brick 2]
  3. psi is reflection-invariant, unconditionally;    [brick 3]
     the doubled odd part dies inside every test.

Consequence chain, machine-level: for ANY test f, psi is determined by
the reflection-even coset of f (3), odd perturbations vanish (1), and
sums decompose (2). The MODEL argument of 1406 — that Chuk-style
sector definitions reach nothing psi misses — now rests on these three
machine legs INSTEAD of prose.

Still model/open (honest):

  - The owner-specific leg: identifying the Chuk cross term
    `F_d = 2i · odd(r̃ m̃)` of a hypothetical owner's autocorrelation
    AS a reflection-odd perturbation of the test that psi consumes.
    For the square class that identification is dictionary work — it
    belongs to brick 4's consumer statement, not to this leaf.
  - Brick 4: the dictionary `psi = classical Q` (sign and factor), the
    LONG brick.
  - The wall `B0b`: untouched by design; no campaign brick moves a
    `sorry` in the mainline tower.

+========================================================================+
| [5] REGISTER DELTAS                                                     |
+========================================================================+

  - Lean-conventions hazard section: Classes H/I/J/K/L recorded.
  - docs/map/README.md: item 40 appended.
  - Campaign queue after this brick: brick 4 (dictionary) is the only
    remaining planned brick. Its scope decision (how much of the
    Yoshida/Chuk normalization can be transcribed from the in-repo
    004-era formalizations vs written from the paper) is a prereg
    question, not a coding question.

+========================================================================+
| [6] NEXT STEPS                                                          |
+========================================================================+

  1. Commit + push brick 3 (leaf, audit, this record, README item).
  2. Brick 4 prereg: enumerate the dictionary statement's formal shape
     at the register level (psi on convolutionSquare vs the selected
     owner's W-value), and which of the 1395-era formal readouts can
     absorb it; zero content before the prereg is locked (law 42).
  3. If brick 4's prereg shows the statement already matches an
     existing formal owner API, the leaf may be short; if it requires
     importing the Yoshida normalization chain, that is a multi-day
     campaign and its price gets stated BEFORE writing (law F15).

RH not claimed. No sign statement, no positivity, no falsification
anywhere in this wave.
