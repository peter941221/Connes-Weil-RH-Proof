# Record 1356 (BUILD PREREG) - C1N1SamplingContest: B1 quartet algebra, statements locked

```text
+---------------------------------------------------------------------+
| BUILD PREREGISTRATION for the funded 1351 green core (owner         |
| "开干" 2026-09-12). B1 SESSION ONLY: B4 wiring gets its own         |
| addendum here (locked text) BEFORE its code lands, per 1351 build   |
| order B1 -> B4 -> review. Statement texts below are LOCKED before   |
| any build output exists (law-42 discipline applied to Lean builds:  |
| the "digit" of a brick session is the green/red log).               |
| Target: new Dev leaf ConnesWeilRH/Dev/C1N1SamplingContest.lean      |
| + paired C1N1SamplingContestAudit.lean (house law: every Dev leaf   |
| paired with an Audit of #print axioms).                             |
+---------------------------------------------------------------------+
```

## 0. Grounding corrections found while reading (recorded honestly, F5)

(a) The 1351 s1 inventory referenced C1Spectral*/C1WeilCriterion files
without directory: they live under ConnesWeilRH/Dev/ (Dev = frontier
leaves, explicit targeting; Source = imported tree). Only
CC20YoshidaConvolution.lean is in Source/. No 1351 claim was wrong
(no directory was asserted); AGENTS 7a amended to say
Source/ AND Dev/.

(b) SUBSTANTIVE: the committed W4a pair algebra (C1SpectralHermitian-
Partner + C1SpectralOfflinePairing) exposes the conjugate transport
`conjugateXiZero` and proves `hermitianPartner rho = 1 - star rho`,
`term(partner rho) = star (term rho)`, multiplicities equal - so the
quartet {rho, rhobar, 1-rho, 1-rhobar} is TWO W4a pairs automatically
(`partner (conj rho) = oneSub rho`). BUT: for COMPLEX test functions
g the two pairs give 2*Re[G_F(w)] and 2*Re[G_F(w̄)], which are NOT
equal in general (they coincide only under the real-symmetric
hypothesis that 1345's scalar shorthand implicitly carried). The
paper record 1345's "quartet total = 4*mult*Re[G(w)G(-w)]" is
therefore re-graded: correct for real g, and the general-correct
form is the PAIR-SPLIT 2+2. B1 locks the pair-split form; no 1345
committed adjudication is contradicted (none quantified over real
vs complex g - the shorthand is tightened, not overruled).

## 1. Locked B1 statements (text is the contract; proofs may vary)

Notation: F := g.convolutionSquare; t(rho) := spectralTerm F rho;
c(rho) := centeredXiCoordinate rho; conj := conjugateXiZero;
part := hermitianPartner; onesub := oneSubXiZero. All on
sourceNontrivialZeroSet; imports as in 1351 s1.

B1-partner-conj:
  part (conj rho) = onesub rho

B1a  quadOrbit_re_sum:
  (t rho + t (part rho) + t (conj rho) + t (onesub rho)).re
    = 2 * (t rho).re + 2 * (t (conj rho)).re

B1b1 spectralTerm_re_unfold:
  (t rho).re = (xiMultiplicity rho : ℝ) *
               (laplaceAt F (c rho)).re
B1b2 laplaceAt_convolutionSquare_norm (NEW wrapper around the
  committed C1HealthyYoshidaDetector identity, no reproof):
  ‖laplaceAt F s‖ = ‖laplaceAt g (-star s)‖ * ‖laplaceAt g s‖
B1b3 spectralTerm_norm_product:
  ‖t rho‖ = (xiMultiplicity rho : ℝ) * ‖laplaceAt g (c rho)‖
                              * ‖laplaceAt g (-star (c rho))‖

B1c  quadOrbit_re_sum_abs_le (the contest-reusable bound):
  |quartetSum.re| <= 2 * ‖t rho‖ + 2 * ‖t (conj rho)‖

B1d  onLine_pair_agreement (sanity bridge to W1 and to the real-g
  shorthand): if rho ∈ onLineZeroSet then c rho = -(star (c rho))
  (purely imaginary center), conj rho ∈ onLineZeroSet, and
  (t rho).re = ‖t rho‖ (W1 gives nonneg; the on-line "quartet"
  degenerates to the conjugate pair {iy, -iy}).

## 2. Axiom and hygiene budget

Target: exactly the three standard axioms (propext, Classical.choice,
Quot.sound), zero sorryAx, per 1343 precedent; Audit module prints
axioms for every B1 declaration. Acceptance = resource-runner log
footer "Build completed successfully (N jobs)" AND zero `^error:`
lines AND audit reads (never exit codes).

## 3. Non-claims

B1 is bookkeeping algebra over committed dictionary terms: it proves
no inequality about zeta and certifies nothing toward the gate. The
(★) <-> gate iff (B4) is a SEPARATE locked statement to be appended
to this file as a LATER addendum before its code lands - it will read
the pair-split quartet side (0 s b) and the committed W3/W4b masses,
not the 1345 shorthand. The N1 lane stays PENDING-unfunded for ANYTHING
beyond this green core (1353 census correction stands).
(Section numbering note, F5: s4 below is the B1 OUTCOME log-summary;
the B4 locked statements will be s5.)

## 4. B1 outcome: GREEN (batch 1556c, log 1556c_b1_brick_green.log)

Acceptance read FROM THE LOG, never the exit code (house law):

| check | contract (s2) | observed |
|---|---|---|
| footer | "Build completed successfully (N jobs)" | "Build completed successfully (3613 jobs)." |
| error lines | zero `^error:` | zero (grep 'error' count = 0 whole-file) |
| axiom prints | 3 standard, 9 declarations | 9/9 print [propext, Classical.choice, Quot.sound] |
| sorryAx | zero | zero |

Iteration ledger (law-42 compliant: statements locked at s1 BEFORE
any log existed; only PROOFS were revised across 1556 -> 1556b -> 1556c):

1. 1556 red: rw direction into hpair2 (:86), `abs_add` unqualified
   (repo uses `abs_add_le`, precedent C1HealthyNarrowPlateau.lean:275),
   `re_centeredXiCoordinate` unknown (exists in C1SpectralOfflinePairing
   but namespace not opened - B1d re-proved from the definitions
   instead of reaching for it), unused simp args (:119).
2. 1556b red, three residuals, each a REAL Lean-culture trap worth
   banking:
   - (a) ASSOC after `simp [Complex.add_re]`: the 4-vs-2+2 regroup is
     associativity over ℝ, which simp normalizes into different
     parenthesizations - closes with `ring`, not more simp args.
   - (b) PARTNER-FIRST ORDER: the committed W4a lemma reads
     `(t (part rho) + t rho).re = 2 * (t rho).re`
     (C1SpectralHermitianPartner.lean:171-176) - the partner on the
     LEFT. Both pair instances in B1a need a prior `rw [add_comm]`;
     the second additionally passes through the heq transport
     (`congrArg` of B1-partner-conj) before the committed match fires.
     Locked statements unchanged.
   - (c) RW INSTANTIATES ONCE: `rw [abs_mul]` rewrote only the FIRST
     `|2 * x|` occurrence (the two summands are different terms); my
     earlier "dedup" of the doubled rw pair had deleted a needed
     instantiation. General fix = `simp only [abs_mul,
     abs_of_pos (0 < 2)]` which rewrites ALL matches.
3. 1556c GREEN as tabled; B1d now: `have hline ... by simpa
   [onLineZeroSet] using h` (same reduction as the compiled mem
   lemma), then `simp only [centeredXiCoordinate, Complex.sub_re];
   rw [hline]; norm_num` - no dependence on the offline-pairing
   namespace at all.

Files: ConnesWeilRH/Dev/C1N1SamplingContest.lean (new leaf, 9
declarations) + C1N1SamplingContestAudit.lean (9 uncommented
#print axioms). Dev leaves stay OUT of the root aggregate (explicit
targeting, AGENTS s2 rule).

## 5. B4 LOCKED STATEMENTS (committed before any B4 build output, law-42)

Session: same Dev leaf (B4 section appended to
C1N1SamplingContest.lean) + Audit extended to every B4 declaration.
Extra import: C1WeilCriterionEquivalence (pulls the whole committed
gate chain; the leaf reuses, never reproves, d767a1d legs).

Grounding read for this lock (all committed, verified line-by-line
today): C1SpectralQwAssembly.lean:65-66 (qw = onLineSpectralMass +
offLineSpectralMass, UNCONDITIONAL); C1SpectralOnlineSplit.lean:57-62
(both masses are Real: the .re of the indicator tsums), :88-90 (W1
nonneg under summability), and spectralSummable for every owner
(C1SpectralSummability); C1CenterTwoCriterionBridge.lean:28-30 (qw =
spectralWeilValue, unconditional); C1WeilCriterionEquivalence.lean:
118-141 (both gate legs, d767a1d).

Design note (F5-honest): B4 wires the TOTAL contest form
("on-line gain covers off-line loss") to the surviving gate. The
WINDOWWISE (star) of record 1345 - per-Nyquist-window sampling energy
vs per-window quartet loss - is B2/B3 science and NEEDS C6/NLLE-v2
(1353 two-limb correction stands). B4 deliberately carries NO
window quantifier, which is exactly why 1351 graded the iff-core
C6-free.

B4.1 contest_balance_iff_qw_nonneg (g : CompactLogTest) - UNCONDITIONAL
per-test balance (no vanishing hypothesis; the class enters at B4.2):
  0 <= qw g  <->  onLineSpectralMass g >= max 0 (- offLineSpectralMass g)

B4.2 contestForm_iff_weilCriterion - the total-contest form IS the
surviving gate (pointwise via B4.1, forall2 congruence):
  (forall g, CC20VanishesOn C1.healthyCC20TestSpace
      cc20TripleFiniteVanishingSet g ->
      onLineSpectralMass g >= max 0 (- offLineSpectralMass g))
  <->
  (forall g, CC20VanishesOn C1.healthyCC20TestSpace
      cc20TripleFiniteVanishingSet g -> 0 <= qw g)

B4.3 contestForm_iff_sourceRH - reassembly only:
  contestForm <-> RHDefinitionBridge.standard.SourceRH
  via B4.2.trans C1WeilCriterionEquivalence.weilCriterion_iff_sourceRH

B4.4 REJECTED as redundant (recorded so it is not re-litigated): the
per-quartet reading combines B1a (quartet re-sum = 2*Re t rho +
2*Re t (conj rho)) with the committed
C1SpectralOfflinePairing.offLineSpectralMass_eq_two_mul_re_tsum_rightHalf
(:209); no new theorem is needed to bridge them, and tsum
re-enumeration per quartet orbit is B2/B3 (window) science.

Non-claims for B4: B4.3 is an IFF about a restated form; it proves no
inequality about zeta, certifies nothing toward the gate beyond the
committed equivalence, and claims no new direction. RH NOT claimed.

Acceptance: same contract as s2 (footer green, zero error lines,
every B4 #print axioms = the three standard, zero sorryAx).

## 6. B4 outcome: GREEN (batch 1557b, log 1557b_b4_brick_green.log)

| check | contract (s5) | observed |
|---|---|---|
| footer | green | "Build completed successfully (3712 jobs)." |
| error lines | zero | zero (grep 'error' whole-file count = 0) |
| B4 axiom prints | 3, all standard | contest_balance_iff_qw_nonneg / contestForm_iff_weilCriterion / contestForm_iff_sourceRH each [propext, Classical.choice, Quot.sound]; B1's nine re-printed identically in the same log |
| sorryAx | zero | zero |

Iteration ledger (s5 statements NEVER touched; proofs only):
1557 red with exactly ONE error: B4.2's forall₂_congr argument needs
the pointwise iff in CONTEST-first orientation while B4.1 is written
gate-first - fixed with `.symm`, a proof-level re-orientation, not a
statement change. 1557b green first try thereafter.

Byte-identity of the committed files with the built mirror copies
verified by cmp before committing (lesson from this session: any
post-build edit, even a comment, is reverted rather than drifting
the verified bytes).

What the brick now holds (all C6-free, 1351 green core COMPLETE):
  B1a-B1d  quartet pair-split algebra + contest-reusable bound;
  B4.1     unconditional per-test balance iff;
  B4.2     total-contest form <=> surviving gate (pointwise congruence);
  B4.3     total-contest form <=> SourceRH (transitivity over d767a1d).
Not included (by design, owner-gated): B2/B3 windowwise reading,
which is where C6/NLLE-v2 enters. The 1356 leaf is 12 declarations,
all axiom-clean.
