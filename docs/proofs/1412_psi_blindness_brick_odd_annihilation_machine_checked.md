# 1412 — C1PsiBlindness GREEN: the odd-annihilation half of 1406 kill (a) is now a machine fact

Verdict up front: **GREEN.** The first brick of the authorized formal
campaign (the F2 reading of the third verbatim re-issue of
"都完成。目标是完成009，然后打通RH。") compiled and axiom-audited:
`ConnesWeilRH.Dev.C1PsiBlindness` + `C1PsiBlindnessAudit`,
`Build completed successfully (3477 jobs)`, zero `^error:`,
all 9 `#print axioms` lines exactly
`[propext, Classical.choice, Quot.sound]`, no `sorryAx`.
**RH not claimed; no sign or positivity statement lives in this leaf.**

+========================================================================+
| [1] What this brick is                                                  |
+========================================================================+

Record 1406 kill (a) said, at MODEL level: every readout of the register
functional `psi` pairs `y` with `-y` —

  - `poleTerm` reads `laplaceAt F (1/2) + laplaceAt F (-1/2)` (`.re`),
  - `finitePrimeTermComplex` reads `F (log n) + F (-log n)`,
  - `archimedeanNumerator` reads `F y + F (-y)` and `F 0`.

Consequence used to seal the Chuk sector objection (1405-1411): a
negation-odd function `F_d` (the cross term `2 * I * odd(...)` of a
sector decomposition) satisfies `psi F_d = 0` — `psi` is BLIND to it, so
Chuk-style sector definitions cannot reach anything `psi` misses. Until
today that consequence was an argument, not a machine-checked fact. This
leaf makes it a fact:

  -+--------------------------------------------------------------+-
  | test_eq_zero_of_odd            odd f => f.test 0 = 0           |
  | laplaceAt_neg_eq_neg_of_odd    odd f => laplaceAt f (-s)       |
  |                                = -laplaceAt f s                |
  | poleTerm_eq_zero_of_odd        odd f => poleTerm f = 0         |
  | finitePrimeTermComplex/Sum     odd f => prime readouts = 0     |
  | archimedeanNumerator/Integrand odd f => pointwise 0            |
  | archimedeanTerm_eq_zero_of_odd odd f => archimedeanTerm f = 0  |
  | psi_eq_zero_of_odd             odd f => psi f = 0    (THE TOP) |
  +----------------------------------------------------------------+

`hodd : forall x, f.test (-x) = -f.test x` is complex-valued oddness on
`CompactLogTest`, so it covers BOTH real-odd and purely-imaginary-even
inputs; the `.re` readouts plus this annihilation are exactly what kill
(a) invoked. The imaginary-part invisibility of the `.re` projections was
already structural (they are real parts by definition); the remaining
live content — the signed-pairing annihilates odd inputs at the pole,
prime and archimedean readouts simultaneously — is now checked.

Scope note (kept honest, inside the leaf header): this is the
ANNIHILATION half only. The full kill (a) for a concrete owner also needs
`psi` linearity and the `convolutionSquare` sector decomposition (future
bricks, [5]).

+========================================================================+
| [2] Invocation ledger (law 7j discipline)                               |
+========================================================================+

  +------+---------------------------------------------+---------------+
  | try  | outcome                                     | errors        |
  +------+---------------------------------------------+---------------+
  | try1 | FAIL: `Unknown identifier CompactLogTest`   | 15 (first at  |
  |      | (type lives under `CCM25Concrete.Compact    |  :38:33)      |
  |      | LogConvolution`; `laplaceAt` needs the       |               |
  |      | `CC20YoshidaConvolution.CompactLogTest`      |               |
  |      | namespace open), `eq_neg_self_iff` wrong     |               |
  |      | name, fragile `show ... simp ... ring`       |               |
  +------+---------------------------------------------+---------------+
  | try2 | FAIL: three genuine classes, table below     | 9 real errors |
  +------+---------------------------------------------+---------------+
  | try3 | GREEN (footer + 9/9 trio + 0 sorryAx)        | 0             |
  +------+---------------------------------------------+---------------+

The build log is `build-logs/c1psiblindness_try3.log` in the WSL
verification workspace (not vendored into the repo; the footer and axiom
prints are quoted above, per brick convention since 1375).

+========================================================================+
| [3] The three try2 failure classes (each is a reusable lesson)          |
+========================================================================+

  Class A — `rw` rewrites EVERY occurrence.
    Goal `a + a = 0`, hypothesis `h : a = -a`: `rw [h]` produces
    `-a + -a = 0` (both occurrences), which `abel` then normalizes to the
    unprovable `-2 • a = 0`. Fix: never rw an `a = -a` identity into a
    goal containing `a` twice; route through
    `(congr_arg (fun t => a + t) h).trans (by abel : a + -a = 0)`.

  Class B — beta-redexes block first-order integral matching.
    `rw [integral_neg_eq_self]` searches the pattern
    `∫ (x), ?f (-x)`. If the previous rewrite installed
    `(fun y => ...) (-x)` literally, the matcher refuses
    ("Did not find an occurrence of the pattern"). The PROVEN template
    `CC20YoshidaFullProduct.laplaceAt_involution` (:159-172) avoids this
    with a `let paired : ℝ → ℂ := ...` helper so the RHS is
    `fun x => paired (-x)` — a first-order match. try2 had
    reconstructed the shape from memory (an F17 violation in Lean, not
    just numerics); try3 transcribes the template's skeleton:
    `let`-helper + `funext/dsimp/congr-or-explicit-harg` +
    `rw [hrewrite, integral_neg_eq_self]`.

  Class C — `add_left_neg` is not a global name.
    It is the `AddGroup` class FIELD (projection
    `AddGroup.add_left_neg`), not a theorem in the root namespace —
    "Unknown identifier" at all three uses. The goal shapes here are
    `a + -a` (= `add_neg_self`, which is a simp lemma): fixed by plain
    `simp` after the rewrites, no name risk.

+========================================================================+
| [4] New law F19 (campaign-side transcribe-first)                         |
+========================================================================+

  F19 — Lean tactic archaeology: before hand-writing any proof that
  duplicates an in-repo PROVEN shape (here: negation-substitution under
  the bilateral Laplace integral), grep for the shape and transcribe its
  skeleton verbatim. Evidence: the same proof idea reconstructed from
  memory failed twice (try1/try2, 5 tactic classes of avoidable errors);
  the transcribed `laplaceAt_involution` skeleton compiled in one try
  (try3). F17's "transcribe, never reconstruct" duty extends to proof
  tactics, not just numerical instruments. → AGENTS.md section 7b
  (pitfalls A/B/C) and section 7 law list.

+========================================================================+
| [5] What is now machine fact vs still MODEL                             |
+========================================================================+

  MACHINE FACT (this brick):
    ∀ odd CompactLogTest f, psi f = 0 (and each component readout = 0).

  STILL MODEL / OPEN (the rest of kill (a) + beyond):
    (i) `psi` ℝ-linearity on `CompactLogTest` — easy leaf, next brick
        candidate;
    (ii) sector decomposition: for an owner built as `convolutionSquare`
        of an EvenOddPair target, exhibiting
        `psi F = psi F_even` requires (i) + the support/node analysis of
        the constructed owners;
    (iii) the dictionary bridge `psi(f ⋆ f̃) = Q(f)` (1407/1410 measured
        it on two bump cells) is a LONG brick: it needs the Chuk
        distribution identity formalized against our explicit kernels —
        several weeks of Lean, not a wave;
    (iv) the wall `B0b : (∀ healthy g, 0 <= qw g) ↔ SourceRH` remains
        classical Weil-criterion territory (1411): no brick here touches
        its truth either way.

  This campaign converts our own MODEL arguments into machine facts and
  hardens the register; it produces zero progress on RH itself — that
  boundary was stated to Peter before the first commit of the campaign
  (1411 close, fork presentation) and still holds.

+========================================================================+
| [6] Next steps                                                          |
+========================================================================+

1. Brick 2: `C1PsiLinearity` — pole/prime/archimedean readout additivity
   and real-scalar homogeneity on `CompactLogTest` (integrals via
   `integral_add` on the L²/compact-support pieces already certified in
   C1SameOwnerWeil; transcribe from the existing integrability proofs,
   F19).
2. Brick 3: `C1ConvolutionSquareSectors` — for `f` with negation-closed
   node support, split `convolutionSquare` into even/odd parts and pin
   `psi (f ⋆ f̃) = psi ((f ⋆ f̃)_even)` using bricks 1+2 (the full
   machine-checked kill (a)).
3. Then reassess: brick 4 (dictionary bridge `psi = Q`) is the only item
   in this campaign with literature-level risk (needs the Chuk/Yoshida
   distribution identity), and the wall itself is outside the campaign —
   new mathematics, per 1411. RH not claimed.
