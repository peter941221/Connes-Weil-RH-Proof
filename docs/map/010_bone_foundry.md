# 1416 - the bone foundry: generating obligations from the obstruction ledger

Binding companion to [`004`](004_endpoint_literature_interface_audit.md)
section 8 and subordinate to [`006`](006_new_math_creation_workflow.md) on
process. This record does two things: it fixes the generation procedure for
the post-1415 state, in which the executable queue is empty on every face,
and it registers the first candidate produced by that procedure (BONE-A),
its screen verdict, and the formal by-product that verdict paid for. The
narrative proof record with the acceptance evidence is
[`1416`](../proofs/1416_bone_foundry_bone_a_dead_minimal_weil_criterion.md).

## 0. Why a foundry rather than a sweep

Beat 1 of the [`006`](006_new_math_creation_workflow.md) loop retrieves
candidate mechanisms from the literature. That retrieval is exhausted for
this face, and the exhaustion is itself evidenced rather than assumed:

```text
+-------------+-------------------------------------------------------------+
| Screen      | Outcome                                                     |
+-------------+-------------------------------------------------------------+
| 1342-1353   | A-series: "every candidate positivity theorem encountered   |
|             | was the same Weil-Bombieri wall in different clothes"        |
| 1355        | 2408.15135v17 gate-ADJACENT, fails arbitration trigger      |
| 1355-1364   | Connes 9811068 operator positivity, Maynard-Pratt: COLD     |
| 1405        | 004 M1-M6 located to arXiv:2608.24827 -> COVERS_OWNER,      |
|             | double structural kill                                      |
+-------------+-------------------------------------------------------------+
```

When retrieval returns only restatements of the target, generation has to
start from the obstruction ledger instead. The foundry is that inversion:
treat each registered obstacle `O1`-`O5`
([`004`](004_endpoint_literature_interface_audit.md) section 8) as a
constraint to be *attacked at its hypothesis*, not as a fact to be routed
around.

## 1. The procedure

```text
   O1..O5 (obstruction ledger)        beat-0 OPERATORS (006:135-141)
        |                                   |
        +------------ CROSS ----------------+
                     |
            (operator, obstacle) PAIR
                     |
                     v
        ADMISSION TEST - three hard gates, all must pass
          G1 consumer : names the healthy-CompactLog B5 consumer 0 <= qw g
          G2 falsifier: paper-only, <= 1 day, symbolic / one-prime / one-shell
          G3 novelty  : not in the 004 section 8 spent-class registry
                     |
                     v
        F8  PREREQ  : grep whether a THEOREM already states it
        F20 PREREQ  : grep whether a DEFINITION already abstracts the
                      parameter the candidate wants to vary
                     |
                     v
        F15 PRICING : cost from the exit's hypotheses, not the file count
                     |
                     v
        GENERATION-CARD (006 schema) --> beats 2..5
```

The two grep prerequisites are the discipline that makes the foundry cheap.
Both fired on the first candidate: F8 found no theorem quantifying over an
arbitrary vanishing set, and F20 found that `C1.healthyCriterionState`
already carries `F` as a free parameter
(`C1HealthyTestSpace.lean:100,108`) with its `iff` proved generically. The
second finding is what converted a dead attack into a landable brick.

Rule of the foundry: **a dead attack is a result only if it is typed.** A
paper-only "this cannot work" that leaves no machine-checkable residue does
not enter the ledger; it is gossip. Every foundry run must end in either a
`GENERATION-CARD` promoted to beat 2 or a kill-ledger row plus, where one
exists, the formal statement of why the route is closed.

## 2. BONE-A: the scale-covariant producer

Generation pair: operator 6 (negate one scoped hypothesis of a
family-specific no-go) x O2 (radius gap).

The observed fact that started it: `cc20TripleFiniteVanishingSet`
(`CC20RHExit.lean:21`) appears 696 times across 45 files, is pinned by
definition through `SourceFiniteSetAdmissibility.finiteSetIsTriple`
(`CC20RHExit.lean:36-40`), and - before this record - no theorem anywhere in
the repository quantified over an arbitrary vanishing set. An unpriced
degree of freedom of that size is exactly what the foundry exists to find.

```text
GENERATION-CARD  BONE-A
  candidate/id      : scale-covariant producer / vanishing-set flexibility
  target equation   : exists lam != 1 and a producer P_lam with
                      (i)   laplaceAt (P_lam rho) s = 0 for s in {0, lam/2, lam}
                      (ii)  HealthyYoshidaDetectorData rho (P_lam rho)
                      (iii) qw (P_lam rho) < 0
                      ==> gate_{F_lam} => SourceRH for F_lam = {0, lam/2, lam},
                      which intersected with the fixed-window certificates
                      (support <= log2/2) would cross O2
  consumer          : 0 <= C1SameOwnerWeil.qw g (healthy-CompactLog, B5-shaped)
  novel move        : negate SourceFiniteSetAdmissibility.finiteSetIsTriple,
                      a scoped hypothesis treated as environment by 45 files
  sign source       : none claimed
  cheap falsifier   : paper-only, two parts (section 3)
```

## 3. Screen verdict: SCREENED-DEAD

### 3.1 Dilation rigidity of the consumer class (PAPER)

The healthy carrier reads Mellin as bilateral Laplace in the log coordinate
(`C1HealthyTestSpace.lean:47` `mellinAt := CompactLogTest.laplaceAt`;
`CC20YoshidaConvolution.lean:55` `laplaceAt f s = integral x, exp (s*x) * f x`,
i.e. the positive character `e^{+sx}` with `x = log t`). Multiplicative
dilation `t -> t^lam` is therefore `x -> lam*x` in the coordinate the tests
live in, and for `(D_lam g)(x) = g(lam*x)`:

```text
   laplaceAt (D_lam g) s = integral x, e^{sx} g(lam x)
                         = (1/lam) * integral u, e^{(s/lam)u} g(u)
                         = (1/lam) * laplaceAt g (s/lam)
```

Requiring `D_lam g` to satisfy the same three vanishing conditions:

```text
   +------+-----------------------------+---------------------+--------------+
   | s    | required of g               | admissible lam      | verdict      |
   +------+-----------------------------+---------------------+--------------+
   | 0    | laplaceAt g 0 = 0           | any                 | always holds |
   | 1/2  | laplaceAt g (1/(2 lam)) = 0 | 1/(2 lam) in triple | lam in {1,1/2}|
   | 1    | laplaceAt g (1/lam) = 0     | 1/lam in triple     | lam in {1,2} |
   +------+-----------------------------+---------------------+--------------+
   | intersection                                              | lam = 1      |
   +-----------------------------------------------------------+--------------+
```

The consumer class has no nontrivial dilation symmetry.

### 3.2 The structural node is the pole image (FORMAL, landed)

The only place the certificate chain reads the vanishing hypothesis is the
pole kill, and it reads `half` alone:

```lean
-- ConnesWeilRH/Dev/C1HealthyYoshidaDetector.lean:102-110
theorem poleTerm_convolutionSquare_of_vanishesOn_cc20Triple
    (g : CompactLogTest)
    (h : CC20VanishesOn C1.healthyCC20TestSpace
        cc20TripleFiniteVanishingSet g) :
    C1SameOwnerWeil.poleTerm g.convolutionSquare = 0 := by
  refine poleTerm_convolutionSquare_of_laplaceAt_half_eq_zero g ?_
  simpa [C1.healthyMellinReadoff, criticalVanishingPointValue] using
    h CriticalVanishingPoint.half (by simp [cc20TripleFiniteVanishingSet])
```

The pole pair `+-1/2` belongs to `xi`, not to `g` (record 1414 machine-checked
exactly this: the pole is the pair `laplaceAt(+-1/2)`, swapped by
`laplaceAt_reflection`). No transformation of the test can relocate a pole
of the completed zeta function, so a scale-covariant producer cannot exist:
the node it would have to move is not its to move.

Consumers of `zero` and `one`, classified - neither is read by the gate
chain:

```text
+------------------------------------------+-----------+------------------------+
| Consumer                                 | Reads     | On the gate chain?     |
+------------------------------------------+-----------+------------------------+
| C1SpectralRealPair.lean:75-127           | all, but  | No - already generic   |
|   realPartTest/imagPartTest transfer     | F-generic | in F, not triple-bound |
| C1XiCenterTwoGammaConstrainedPrefix.lean | all three | No - laneRLaplacePenalty|
|   :203-256 rank-3 penalty route          |           | side lane, inequality  |
|                                          |           | self-declared open     |
| C1CC20ArchimedeanReadback.lean:58        | zero      | No - readback wiring   |
+------------------------------------------+-----------+------------------------+
```

Verdict: `half` STRUCTURAL, `{zero, one}` INCIDENTAL at the gate. BONE-A is
`SCREENED-DEAD` with a typed reason, at a cost of roughly forty minutes of
paper and grep and zero Lean spent on the attack.

## 4. The by-product: minimal normal form of the wall

Reading the reverse leg to settle 3.2 exposed the fact that the committed
`iff` discards its vanishing hypothesis:

```lean
-- ConnesWeilRH/Dev/C1WeilCriterionEquivalence.lean:103-109
theorem qw_nonneg_of_sourceRH (g : CompactLogTest)
    (hRH : RHDefinitionBridge.standard.SourceRH) :
    0 ≤ C1SameOwnerWeil.qw g := by
  rw [qw_eq_onLineSpectralMass_add_offLineSpectralMass,
    offLineSpectralMass_eq_zero_of_sourceRH g hRH]
  linarith [onLineSpectralMass_nonnegative_of_summable g
    (spectralSummableProp g.convolutionSquare)]

-- ConnesWeilRH/Dev/C1WeilCriterionEquivalence.lean:140
  ⟨sourceRH_of_all_vanishing_qw_nonneg, fun hRH g _hg =>
    qw_nonneg_of_sourceRH g hRH⟩
--                                  ^^^^ discarded
```

The file header already said this in prose (`:20-24`, "The vanishing
hypothesis is not even consumed"), but the consequence was never stated.
`ConnesWeilRH/Dev/C1MinimalWeilCriterion.lean` (13 declarations, green on
try2, log `1416_minimal_try2.log`: footer `Build completed successfully
(3712 jobs)`, zero `^error:` lines, zero `sorryAx`, 13/13 declarations
printing `[propext, Classical.choice, Quot.sound]`) states it:

```text
  Part 1  vanishesOn_of_subset / vanishesOn_empty /
          vanishesOn_singleton_half_iff /
          vanishesOn_half_of_vanishesOn_triple
  Part 2  weilGate (F)                          the parameterized gate
          weilGate_of_subset                    F subset F' : gate F -> gate F'
          weilGate_triple_iff_sourceRH          the committed form, restated
          weilGate_iff_sourceRH_of_subset_triple  EVERY sub-triple is equivalent
  Part 3  weilGate_unconditional_iff_sourceRH   (forall g, 0 <= qw g) <-> SourceRH
          weilGate_halfOnly_iff_sourceRH        one node suffices
  Part 4  poleTerm / qw = -arch - prime / qw = -arch / endpoint interface,
          all from the singleton {half} hypothesis - the minimality witness
```

Direction of the monotonicity, because it is the part that is easy to
invert: a gate on a SMALLER node set quantifies over MORE tests and is
therefore STRONGER. `F = ∅` is the strongest form in the family and it is
still equivalent to `SourceRH`. So the foundry's first product is a
sharpening of the open problem, not progress on it: the wall now has a
side-condition-free statement, and the vanishing-set degree of freedom is
proved vacuous for the equivalence while remaining load-bearing (at `half`)
for the certificate route.

## 5. What this record does NOT claim

No sign theorem, no positivity statement, no inequality about zeta, no
numerical result of any kind. RH is NOT claimed; the gate stays OPEN in all
three restated forms, and 3.1 is PAPER evidence under law 65 - it is a
change-of-variables computation, not a Lean certification, and the dilation
operator it discusses does not exist on `CompactLogTest` in this repository
(F8 grep: no `dilate`/`scale` transform on the carrier; the only test-level
transforms are `reflection` and `convolutionSquare`). Nothing here licenses
a numerical campaign, and the default posture remains the freeze
recommended by records 1411 and 1415.

The foundry itself is open: the remaining unpriced pairs are operator 5
(minimize a known counterexample) x O1, and operator 3 (positive-kernel /
Gram factorization) x O3, both of which must clear G3 against the spent
registry before any spend.
