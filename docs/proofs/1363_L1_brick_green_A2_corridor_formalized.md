# Record 1363 (OUTCOME LEDGER) - L1 window-split brick GREEN (batch 1558); the A2=>gate corridor is machine-checked down to the single named wall L2; Maynard-Pratt screen closes W1 queue

```text
+---------------------------------------------------------------------+
| Verdict up front: GOOD. Batch 1558 footer "Build completed           |
| successfully (3713 jobs)", zero error lines, all 12 axiom prints    |
| exactly [propext, Classical.choice, Quot.sound], zero sorryAx,      |
| byte-identity mirror==repo. This is a formal bookkeeping advance    |
| (MODEL of nothing new about zeta): the wall between "someone proves |
| TARGET-A2 on paper" and "the gate discharges in Lean" is now        |
| exactly one named face: L2 (the count-to-energy / C6 science).      |
| RH is NOT claimed anywhere.                                         |
+---------------------------------------------------------------------+
```

## 1. Green evidence (the log is the digit)

    /home-side build log 1558_l1_window_split.log:
      ... Built ConnesWeilRH.Dev.C1A2WindowSplitAudit (1.4s)   [3713/3713]
      'windowSet_unique'                axioms: [propext, Classical.choice, Quot.sound]
      'windowSet_disjoint'              axioms: [propext, Classical.choice, Quot.sound]
      'windowSet_mem'      (T0)         axioms: [propext, Classical.choice, Quot.sound]
      'hasSum_comp_equiv'  (infra)      axioms: [propext, Classical.choice, Quot.sound]
      'hasSum_fiberwise'   (core)       axioms: [propext, Classical.choice, Quot.sound]
      'tsum_fiberwise'                  axioms: [propext, Classical.choice, Quot.sound]
      'summable_onLineSpectralTerm_re'  axioms: [propext, Classical.choice, Quot.sound]
      'summable_offLineSpectralTerm_re' axioms: [propext, Classical.choice, Quot.sound]
      'windowMass_split_on'  (T1)       axioms: [propext, Classical.choice, Quot.sound]
      'windowMass_split_off' (T2)       axioms: [propext, Classical.choice, Quot.sound]
      'qw_window_assembly'   (T3)       axioms: [propext, Classical.choice, Quot.sound]
      'contestForm_windowwise_iff' (T4) axioms: [propext, Classical.choice, Quot.sound]
    error grep count: 0.  sorry grep count: 0 (source).
    sha256 byte-identity: repo file == built mirror file, both leaves.
    Source commit 89fbb0f; statements locked at 1362 s3 + s3a pre-digit
    amendment, never edited after launch (contract-integrity rule OK).

## 2. What the corridor now says (chain state)

    TARGET-A2 (paper theorem, 1360 s4 box: f*(A)=A/(A+2), W=pi/log2,
      T1 >= 3e12, N_off-nearline(I) < f*(A(I)) N(I))
        |
        |  L2a localized sampling (=C6)  \
        |  L2b sinc^2 tail gluing          }  THE WALL - one face, named
        |  L2c count-to-energy realization /   (1362 s5), NOT formalized
        v
    per-window contest balance  (paper arithmetic, 1353)
        v
    Sum_k windowOnLineMass >= max 0 (-Sum_k windowOffLineMass)   <-- T4
        v                                                        (GREEN)
    0 <= qw g  per vanishing g   [B4.1, 275aca6, GREEN]
        v
    weilCriterion <=> SourceRH   [d767a1d, GREEN]

    L1 (this batch) = the T0-T4 segment: window masses <-> total masses,
    unconditional Fubini only. Importantly it did NOT need nonnegativity
    (the fork's HasSum.sigma killed the planned ENNReal descent; 1362 s7)
    - the wall L2 remains, untouched: 1361's mechanism table (now
    8 rows, see s3) says NO located theorem produces the
    on-line-cluster => off-line-exclusion arrow. Distance readout:
    formal corridor COMPLETE on the bookkeeping side; analytic corridor
    EMPTY as ever at C6. Waypoint, not result.

## 3. W1 queue item 3 CLOSED: Maynard-Pratt 2206.11729v2 under the A2 lens

Primary reads (arXiv HTML v2, question-scoped, this session), verbatim
key data:

  Title: "Half-isolated zeros and zero-density estimates" (Maynard, Pratt;
  v1 2022-06-23, v2 2023-05-29). Abstract: "a new method to detect the
  zeros of the Riemann zeta function which is sensitive to the vertical
  distribution of the zeros. This allows us to prove there are few
  'half-isolated' zeros."
  Definition (half-isolated, verbatim branches): rho0 = beta0 + i gamma0
  is Y-half-isolated if every nearby zero rho' satisfies either
    (1) |beta' - beta0| <= 1/(10 log Y)  AND  gamma' >= gamma0, or
    (2) beta' <= beta0 - (log log |gamma0|)^2 / log Y.
  Reader's note (their own): for gamma0 in [T,2T], Y ~ T^(1/loglog T),
  zeros within (log T)^2 of rho0 must be either ~loglog^2 LEFT in real
  part, or essentially same-real-part-and-above.
  Conclusion form: "half-isolated zeros have very short zero-detecting
  polynomials", hence an unconditional COUNT bound on half-isolated
  zeros (a zero-density-shaped statement).

A2-lens verdict: mechanism row 8 of the 1361 table class - NEGATIVE,
with two on-record observations:
  (a) Not the right hypothesis: nothing takes an ON-LINE cluster (small
      A(I)) as INPUT; the paper's input is the local configuration
      around a SINGLE zero of ANY real part, and the output is a global
      count bound, not a per-window off-line exclusion. The arrow shape
      (config => detectability => count) never crosses to energy/
      positivity. No frame, no quadratic form, no positivity input.
  (b) Structural cousin noted honestly: the branch asymmetry (nearby
      zeros may move LEFT in real part freely, but not RIGHT within
      ~1/(10 log Y)) is the Deuring-Heilbronn-flavored one-sided
      repulsion our 1361 scan flagged for DH itself; it is a
      single-zero, sigma->1-ward statement, while A2 needs the JOINT
      statement between line-clustering and near-1/2 off-line
      majority. 1347 wave-1 screened it for count-locality; this
      record screens it for A2-correlation: both COLD, same object.

With items 1-4 of 1360 s5 delivered (constants: 1360/1361; mechanism
scan: 1361 NEGATIVE; MP re-screen: this record COLD; W0 is task #14),
WAVE W1 IS FULLY CONSUMED. Task #9 CLOSED. The A-route's remaining
mathematical content is, exactly and only: L2 = L2a (localized
sampling = C6), L2b (sinc^2 gluing), L2c (count-to-energy) + the paper
theorem TARGET-A2 above them. Owner card 1357 weights update
accordingly: option D (thermometer) is DONE data, option B (B2/B3
windowwise = L2a science) is now the ONLY wall-facing build lane;
option E harvest keeps paying (specs 1345/1346/1350, bricks 1343/1356/
1363, closed capacity maps 1338/1357, and now the formal corridor map
of this record).

## 4. Post-green hygiene notes for the next builder (AGENTS 7b candidates)

  1. Five `linter.style.show` warnings (show-that-changes-goal) at
     lines 86/89/94/111/145: non-fatal, log accepted as-is; fix later
     with `change` if the repo ever lints clean by default.
  2. The defeq fact `(SummationFilter.unconditional L).filter =
     Filter.atTop` (1362 s7.3a) is the unlock for hand-rolled net
     arguments in this fork.
  3. When a future leaf needs NONNEG-convex structure (it does not:
     L1 is signed-generic), remember summable_partition (Real) and
     ENNReal.tsum_sigma' still exist as backups; HasSum.sigma makes
     them unnecessary for value splits.

## 5. Next actions (running order)

1. W0 (task #14): Connes adelic-class vs CompactLogTest gap
   certificate - Q1-Q3 on math/9811068; B-blueprint v1 deliverable.
   This is the parallel-route reconnaissance the charter keeps warm.
2. Owner decision point (unchanged, now sharpened): option B =
   commission the L2a (C6) charter draft - localized frame-theoretic
   sampling on our committed kernel; first deliverable would be a
   1364-style design record with a MODEL-grade prolate-ceiling
   arithmetic made rigorous (1353 s5 is the blueprint; the honest
   grade today: NO proof object, weeks-scale science).
3. Harvest lane stays open: 1355 deep pass (option C) is unbudgeted
   and independent of both routes above.
