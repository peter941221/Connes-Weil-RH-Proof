# 1413 — Campaign brick 2 GREEN: `C1PsiLinearity`, the additive structure of `psi` is machine-checked

Wave: F2 formal campaign (brick 2 of 4). Depends on: 1412 (brick 1
`C1PsiBlindness`), 1406 (kill (a) MODEL argument).
Status: **GREEN — 23 declarations, 23/23 standard-axiom trios, 0 error,
0 `sorryAx`, build footer `Build completed successfully (3478 jobs)`**.
This record contains **zero rig digits** (law 65 discipline: a formal
brick is registered by its machine facts only). **RH is not claimed.**

+========================================================================+
| [1] WHAT THE BRICK IS                                                   |
+========================================================================+

Brick 1 (`ConnesWeilRH/Dev/C1PsiBlindness.lean`, record 1412) proved:
`psi` annihilates every negation-odd test. But the MODEL argument that
1406 embedded that annihilation in treats `psi` as **additive** — it
splits `psi(testAdd aSquare bSquare)` into a sum of readouts before the
odd part dies. That additivity was an assumption of the MODEL prose,
never a machine fact. Brick 2 supplies it.

New leaf: `ConnesWeilRH/Dev/C1PsiLinearity.lean`
(audit: `ConnesWeilRH/Dev/C1PsiLinearityAudit.lean`), 23 declarations:

  +--------------------------------------------------------------+
  | layer                | additivity             | negation      |
  +----------------------+------------------------+---------------+
  | test object          | testAdd (pointwise,    | testNeg       |
  |                      | support via .add)      | (support .neg)|
  +----------------------+------------------------+---------------+
  | laplaceAt            | unconditional          | unconditional |
  | poleTerm             | unconditional          | unconditional |
  | finitePrimeTermComplex| pointwise identity    | pointwise     |
  | finitePrimeTerm (re) | pointwise identity     | pointwise     |
  | finitePrimeSum       | unconditional          | unconditional |
  |                      | (union-set argument)   | (index-set    |
  |                      |                        |  equality)    |
  +----------------------+------------------------+---------------+
  | archimedeanNumerator | pointwise identity     | pointwise     |
  | archimedeanIntegrand | pointwise identity     | pointwise     |
  | archimedeanTerm      | CONDITIONAL: needs     | unconditional |
  |                      | IntegrableOn both on   | (integral_neg |
  |                      | Ioi 0 (hypothesis      | is uncond.)   |
  |                      | carried, not invented) |               |
  +----------------------+------------------------+---------------+
  | psi                  | psi_testAdd            | psi_testNeg   |
  |                      | (conditional)          |               |
  +----------------------+------------------------+---------------+
  | psi on squares       | psi_testAdd_convolutionSquare:        |
  |                      | HYPOTHESIS-FREE — each integrable by  |
  |                      | C1SameOwnerWeil.archimedeanIntegrand_ |
  |                      | square_integrableOn_Ioi (:263-267)    |
  +--------------------------------------------------------------+

Key structure decisions (not accidents):

- `testAdd`/`testNeg` are built through the `TestFunction` component as
  structure literals, so `(testAdd f g).test = f.test + g.test` is
  `rfl`; every readout then unfolds to a pointwise statement.
- The two conditional statements carry `IntegrableOn` hypotheses that
  brick 4's consumers discharge or inherit; nothing is assumed that the
  top square-class corollary `psi_testAdd_convolutionSquare` also needs.
  That corollary — the one brick 3 will actually consume — is
  hypothesis-free.
- The prime-sum additivity is the only genuinely non-algebraic leg: the
  summation set itself depends on the test. It is handled by the union
  superset `D = globalPrimeIndexSet F ∪ globalPrimeIndexSet G`:
  `globalPrimeIndexSet (testAdd F G) ⊆ D`
  (`globalPrimeIndexSet_testAdd_subset`: a nonzero sum-term is nonzero
  in some summand), and outside a set its terms vanish
  (`finitePrimeTerm_eq_zero_of_not_mem`), so three `Finset.sum_subset`
  legs glue through `sum_add_distrib`.
- No scalar-multiplication layer: decided by design — brick 3's sector
  split needs only `+` and `-`.

+========================================================================+
| [2] INVOCATION LEDGER                                                   |
+========================================================================+

  +------+-------------------------------------------+---------+
  | pass | action                                    | result  |
  +------+-------------------------------------------+---------+
  | pre  | 4 rounds of API probing on a scratch      | all     |
  |      | probe file (untracked, never imported,    | names & |
  |      | deleted before this commit)               | shapes  |
  |      |                                           | settled |
  +------+-------------------------------------------+---------+
  | try1 | first full leaf, fast single-file          | 4 local |
  |      | `lake env lean` typecheck                  | errors  |
  +------+-------------------------------------------+---------+
  | try2 | fixes [3] applied; retypecheck            | 0 error |
  |      |                                           |         |
  | try2 | acceptance build (leaf + audit)             | GREEN   |
  |      | 3478 jobs, 23/23 trios, 0 error, 0 sorryAx|         |
  |      | 0 warnings attributable to the new files  |         |
  +------+-------------------------------------------+---------+

Acceptance log: `build-logs/c1psi-linearity-try2.log` (WSL ext4 mirror,
`run_resource_aware_task.sh`), footer and counts verified by
log-not-exit-code (log-inspection) acceptance.

+========================================================================+
| [3] TRY1 FAILURE CLASSES (each fixed in one edit)                       |
+========================================================================+

Class D — `push_neg` destroys a conjunction. `push_neg` on
`¬(IsPrimePow n ∧ term ≠ 0)` yields the IMPLICATION
`IsPrimePow n → term = 0`, not an `Or`; the planned
`rcases hn with hnpow | hterm` then fails. Fix: skip `push_neg`
entirely — `by_cases hprime : IsPrimePow n`, and in the prime branch
recover the zero by `by_contra hne; exact hn ⟨hprime, hne⟩`.
(Also: `n.IsPrimePow` dot notation does not parse; write `IsPrimePow n`.)

Class E — equation direction in `Finset.sum_congr`. The congruence
argument must read `term_new n = term_old₁ n + term_old₂ n`, i.e. the
lemma VERBATIM; an instinctive `.symm` is a type error. Fix: drop it.

Class F — `simp only` cannot eat a metavariable-bearing equation
argument. `simp only [Pi.add_apply, integral_add hFI hGI]` reported
"no progress": `integral_add hFI hGI` still has `?f ?g` unassigned in
its LHS, and the simproc declines it silently. `rw` DOES instantiate
those metavars by matching. Fix: use `rw [hfn, integral_add hFI hGI]`.

Class G (design rule, same root as brick 1's Class B) — keep
function-extensionality witnesses as a SINGLE lambda whose body is
`+`-headed (`fun y => a y + b y`), never as the Pi-algebra sum of two
lambdas (`(fun y => a y) + fun y => b y`). Only the first form leaves a
literal `∫ y, a y + b y` redex that `integral_add` matches. This is the
exact shape that already made `laplaceAt_testAdd` go through, so the
`archimedeanTerm_testAdd` witness was rewritten to copy it (law F19:
transcribe what demonstrably works in the same file).

+========================================================================+
| [4] MACHINE / MODEL BOUNDARY                                            |
+========================================================================+

What is now machine fact:

  1. `psi` (as defined in `C1SameOwnerWeil`) is a group homomorphism
     from (compact log tests with pointwise `+`, restricted to the
     square class or under explicit `IntegrableOn`) to `ℝ`, odd under
     pointwise negation. [C1PsiLinearity, 23 decls, standard axioms]
  2. Together with brick 1: negation-odd tests die AND sums split.
     [C1PsiBlindness + C1PsiLinearity]

What is still MODEL or open:

  - brick 3: the `convolutionSquare` sector split — for a hypothetical
    counterexample owner, show the cross-term
    `odd(real-part-of-F)` part of `testAdd aSquare bSquare` lives in a
    blind sector. Now that additivity is machine fact, brick 3 is the
    statement "psi(testAdd aSquare bSquare) = psi(aSquare) + psi(bSquare)
    and the odd-part input annihilates", i.e. completing kill (a)
    formally.
  - brick 4: the dictionary `psi = classical Q` (sign and factor) —
    LONG, paper-scale, and per 1407-1408 it is the only brick with real
    mathematical content outside the wall.
  - the wall `B0b` (Weil criterion ↔ RH): untouched by design; no
    brick in this campaign touches it, and none of them changes any
    `sorry` in the mainline tower.
  - No sign theorem anywhere in this leaf: the audit header states
    explicitly that these are linear-algebra facts about the existing
    readouts.

+========================================================================+
| [5] REGISTER DELTAS                                                     |
+========================================================================+

  - Lean-conventions hazard section: Classes D/E/F/G registered.
  - F19 reconfirmed: every try2 fix was a transcription of a shape that
    already existed in-probe or in the same file; zero
    reconstructed-from-memory tactics this brick.
  - docs/map/README.md: item 39 appended.
  - Campaign queue: brick 3 next (sector split on the square class),
    then brick 4 (dictionary). No rig work enters this wave; rig queue
    remains empty by 1404's construction argument.

+========================================================================+
| [6] NEXT STEPS                                                          |
+========================================================================+

  1. Commit + push the brick (leaf, audit, this record, README item).
  2. Brick 3 prereg reading: enumerate exactly which odd-part inputs
     the counterexample cross-term produces on `testAdd aSquare bSquare`
     and which blindness lemma of brick 1 consumes each.
  3. Brick 3 leaf: `C1PsiSectorSplit` on the square class, reusing
     `psi_testAdd_convolutionSquare` + `psi _eq_zero_of_odd` bundle.

RH not claimed. No digit in this record falsifies or supports any sign
statement; the wall is untouched.
