# 1416 — BONE-A screened dead at paper stage; the wall gets its minimal side-condition-free normal form

Wave: bone foundry (new generation procedure), first candidate.
Depends on: 1343 (B0b `weilCriterion_iff_sourceRH`), 1414 (pole pair is
`laplaceAt(±1/2)`, swapped by reflection), 1415 (campaign closure, wall
anatomy consolidated as map 004 §8).
Status: **Attack SCREENED-DEAD on paper, zero Lean spent on it. By-product
brick GREEN on try2 (13 declarations, standard axioms, zero `sorryAx`).
No digits, no sign claim. RH is not claimed.**

+========================================================================+
| [1] VERDICT                                                             |
+========================================================================+

Two results, opposite in sign, from one forty-minute paper-and-grep run.

  +-------------------+--------------------------------------------------+
  | result            | content                                          |
  +-------------------+--------------------------------------------------+
  | BONE-A            | DEAD. No scale-covariant tower producer can      |
  | (attack)          | exist: the only Mellin node the certificate      |
  |                   | chain reads is `half`, and `half` is the right   |
  |                   | image of the xi pole pair, i.e. a property of    |
  |                   | xi and not of the test. Independently, the       |
  |                   | consumer class has no nontrivial dilation        |
  |                   | symmetry (lam = 1 only). The O2 radius gap       |
  |                   | cannot be crossed by scaling.                    |
  +-------------------+--------------------------------------------------+
  | BONE-A'           | LANDED. The gate's three-point vanishing         |
  | (by-product)      | hypothesis is vestigial in the equivalence, so   |
  |                   | the wall has a side-condition-free normal form   |
  |                   | and a monotone node-set family. A sharpening,    |
  |                   | not an advance.                                  |
  +-------------------+--------------------------------------------------+

Cost model: the attack died for free. Per law F15 the candidate was
priced from its exit hypothesis ("can the structural node move?") rather
than from a file count, and that hypothesis was answerable by reading
one theorem body.

+========================================================================+
| [2] THE FOUNDRY: WHY GENERATION HAD TO INVERT                           |
+========================================================================+

Beat 1 of map 006 retrieves mechanisms from the literature. For this face
retrieval is exhausted, and the exhaustion is evidenced, not assumed:
1342-1353 (every candidate positivity theorem was the same Weil-Bombieri
wall in different clothes), 1355 (gate-adjacent, fails arbitration),
1355-1364 (Connes 9811068, Maynard-Pratt: COLD), 1405 (M1-M6 located to
arXiv:2608.24827, COVERS_OWNER by double structural kill).

The foundry inverts the input: generate from the obstruction ledger.

```text
   O1..O5 (map 004 s8)  x  beat-0 operators (map 006:135-141)
            |
            v
   ADMISSION  G1 names the consumer 0 <= qw g
              G2 paper-only falsifier, <= 1 day
              G3 not in the spent-class registry
            |
            v
   F8  grep: does a THEOREM already state it?
   F20 grep: does a DEFINITION already abstract the parameter?   <-- NEW
            |
            v
   F15 price from the exit's hypotheses, not the file count
            |
            v
   GENERATION-CARD -> beats 2..5
```

Foundry rule (registered in map 010 §1): **a dead attack enters the
ledger only with a typed reason.** A paper-only "this cannot work" that
leaves no machine-checkable residue is gossip, not a kill.

+========================================================================+
| [3] BONE-A: THE UNPRICED DEGREE OF FREEDOM                              |
+========================================================================+

Generation pair: operator 6 (negate one scoped hypothesis of a
family-specific no-go) x O2 (radius gap).

The trigger was a count. `cc20TripleFiniteVanishingSet`
(`CC20RHExit.lean:21`) appears **696 times across 45 files**, is pinned by
definition rather than derived:

```lean
-- ConnesWeilRH/Source/CC20RHExit.lean:36-40
structure SourceFiniteSetAdmissibility
    (F : Finset CriticalVanishingPoint) : Prop where
  zeroMem : CriticalVanishingPoint.zero ∈ F
  halfMem : CriticalVanishingPoint.half ∈ F
  oneMem  : CriticalVanishingPoint.one  ∈ F
  finiteSetIsTriple : RouteFiniteVanishingSetIsCC20Triple F
```

and — before this record — **no theorem in the repository quantified over
an arbitrary vanishing set**. A load-bearing constant that nothing
generalizes over is exactly what operator 6 targets.

Claimed mechanism: a producer `P_lam` whose output vanishes at
`{0, lam/2, lam}` while still detecting `rho` and still carrying
`qw < 0`. That would yield `gate_{F_lam} => SourceRH` for a family of
`lam`, which intersected with the fixed-window certificates
(support `<= log2/2`) is precisely O2's canonical form, entered from the
producer side instead of the certificate side.

+========================================================================+
| [4] THE KILL, LEG 1: DILATION RIGIDITY (PAPER, law 65)                  |
+========================================================================+

The healthy carrier reads Mellin as bilateral Laplace in the log
coordinate — `mellinAt := CompactLogTest.laplaceAt`
(`C1HealthyTestSpace.lean:47`), with `laplaceAt f s = ∫ x, exp (s*x) * f x`
(`CC20YoshidaConvolution.lean:55`, positive character `e^{+sx}`, `x = log t`).
Multiplicative dilation `t -> t^lam` is therefore `x -> lam*x`, and for
`(D_lam g)(x) = g(lam*x)`:

```text
   laplaceAt (D_lam g) s = (1/lam) * laplaceAt g (s/lam)      (u = lam x)
```

Requiring the dilate to satisfy the same node conditions:

```text
   +------+------------------------------+---------------------+---------------+
   | s    | required of g                | admissible lam      | verdict       |
   +------+------------------------------+---------------------+---------------+
   | 0    | laplaceAt g 0 = 0            | any                 | always holds  |
   | 1/2  | laplaceAt g (1/(2 lam)) = 0  | 1/(2 lam) in triple | lam in {1,1/2}|
   | 1    | laplaceAt g (1/lam) = 0      | 1/lam in triple     | lam in {1,2}  |
   +------+------------------------------+---------------------+---------------+
   | intersection                                               | lam = 1       |
   +------------------------------------------------------------+---------------+
```

The consumer class admits no nontrivial dilation symmetry. Status PAPER:
this is a change of variables, not a Lean certification, and no dilation
operator exists on `CompactLogTest` in this repository (F8 grep: the only
test-level transforms are `reflection` and `convolutionSquare`).

+========================================================================+
| [5] THE KILL, LEG 2: THE STRUCTURAL NODE IS THE POLE IMAGE (FORMAL)     |
+========================================================================+

Leg 1 says the class is rigid; leg 2 says why rigidity is not an artifact
of our definitions. The only gate-chain consumer of the vanishing
hypothesis is the pole kill, and its body reads one node:

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

Record 1414 machine-checked that the pole is the pair `laplaceAt(±1/2)`,
swapped by `laplaceAt_reflection`. A pole of the completed zeta function
is not a feature of the test, so no transform of `g` relocates it.

Consumers of the other two nodes, classified — none is on the gate chain:

```text
+-------------------------------------------+-----------+-----------------------+
| Consumer                                  | Reads     | On the gate chain?    |
+-------------------------------------------+-----------+-----------------------+
| C1SpectralRealPair.lean:75-127            | all, but  | No - already generic  |
|   realPartTest / imagPartTest transfer    | F-generic | in F, not triple-bound|
| C1XiCenterTwoGammaConstrainedPrefix.lean  | all three | No - laneRLaplacePenalty|
|   :203-256 rank-3 penalty side lane       |           | inequality self-declared|
|                                           |           | open at :213 and :242 |
| C1CC20ArchimedeanReadback.lean:58         | zero      | No - readback wiring  |
+-------------------------------------------+-----------+-----------------------+
```

Verdict: `half` STRUCTURAL, `{zero, one}` INCIDENTAL at the gate.

+========================================================================+
| [6] THE BY-PRODUCT: MINIMAL NORMAL FORM (BRICK GREEN, try2)             |
+========================================================================+

Settling leg 2 required reading the reverse leg, which exposed the fact
that makes the by-product possible:

```lean
-- ConnesWeilRH/Dev/C1WeilCriterionEquivalence.lean:103-109 (verbatim)
theorem qw_nonneg_of_sourceRH (g : CompactLogTest)
    (hRH : RHDefinitionBridge.standard.SourceRH) :
    0 ≤ C1SameOwnerWeil.qw g := by
  rw [qw_eq_onLineSpectralMass_add_offLineSpectralMass,
    offLineSpectralMass_eq_zero_of_sourceRH g hRH]
  linarith [onLineSpectralMass_nonnegative_of_summable g
    (spectralSummableProp g.convolutionSquare)]

-- ConnesWeilRH/Dev/C1WeilCriterionEquivalence.lean:140-141 (verbatim)
  ⟨sourceRH_of_all_vanishing_qw_nonneg, fun hRH g _hg =>
    qw_nonneg_of_sourceRH g hRH⟩
--                                  ^^^^ the vanishing hypothesis, discarded
```

The signature takes no vanishing argument, and the mechanism is the
spectral-mass split: off-line mass vanishes under `SourceRH`, on-line mass
is nonnegative. Quoted verbatim per law F18 — a paraphrased vertex can
manufacture a crisis the kernel never proved (records 1407/1408).

The file header already said so in prose (`:20-24`, "The vanishing
hypothesis is not even consumed"); the consequence was never stated. F20
then supplied the missing inventory: `C1.healthyCriterionState` already
carries `F` as a free parameter with a generically proved `iff`
(`C1HealthyTestSpace.lean:100,108`). The brick is therefore reassembly.

`ConnesWeilRH/Dev/C1MinimalWeilCriterion.lean` (+ `...Audit`), 13
declarations:

```text
  Part 1  vanishesOn_of_subset              F subset F' : VanishesOn F' -> VanishesOn F
          vanishesOn_empty                  the empty node set binds nothing
          vanishesOn_singleton_half_iff     {half} <-> laplaceAt g (1/2) = 0
          vanishesOn_half_of_vanishesOn_triple
  Part 2  weilGate (F)                      the parameterized gate
          weilGate_of_subset                F subset F' : weilGate F -> weilGate F'
          weilGate_triple_iff_sourceRH      the committed form, restated
          weilGate_iff_sourceRH_of_subset_triple   EVERY sub-triple is equivalent
  Part 3  weilGate_unconditional_iff_sourceRH   (forall g, 0 <= qw g) <-> SourceRH
          weilGate_halfOnly_iff_sourceRH        one node suffices
  Part 4  poleTerm kill / qw = -arch - prime / qw = -arch on root support /
          endpoint sign interface — all from the SINGLETON {half} hypothesis
```

Monotonicity direction, because it is the easy thing to invert: a gate on
a SMALLER node set quantifies over MORE tests and is therefore STRONGER.
`F = ∅` is the strongest member of the family and it is still equivalent
to `SourceRH`. Part 4 is the minimality witness — the whole certificate
reduction runs from one node, so `zero` and `one` are provably never read.

+========================================================================+
| [7] ACCEPTANCE EVIDENCE                                                 |
+========================================================================+

```text
  log              build-logs/1416_minimal_try2.log   (107,548 bytes)
  footer           Build completed successfully (3712 jobs)
  ^error: lines    0
  sorryAx          0
  axiom prints     13/13 = [propext, Classical.choice, Quot.sound]
  invocations      try1: 1 error (hazard class M) -> try2: GREEN
```

The byte count is part of the evidence: a content-hash cache hit can exit
0 with an EMPTY log (record 1326), and acceptance counts taken through
nested shell variables have printed plausible fake zeros (record 1413).
Both checks here use direct literal paths in separate invocations.

Hazard class M (registered in AGENTS 7b): `Finset.not_mem_empty` is not a
constant in this toolchain; for `hp : p ∈ (∅ : Finset α)` close with
`simp at hp`. The failure is a NAME error, not a shape error, so the
surrounding proof gives no hint.

+========================================================================+
| [8] WHAT THIS RECORD DOES NOT CLAIM                                     |
+========================================================================+

No sign theorem, no positivity statement, no inequality about zeta, no
numerical result. The minimal normal form makes the obligation STRONGER,
not weaker: deleting a hypothesis from a universally quantified
obligation widens its scope. The gate stays OPEN in all three restated
forms, and the tower's single open obligation is unchanged.

Law F20 is born here (grep for over-specialized definitions, not only for
existing theorems). The foundry's remaining unpriced pairs are operator 5
x O1 (minimize a known counterexample) and operator 3 x O3
(positive-kernel / Gram factorization); both must clear G3 against the
spent registry before any spend. No numerical campaign is authorized. The
freeze posture of records 1411 and 1415 is unchanged.

RH is not claimed.
