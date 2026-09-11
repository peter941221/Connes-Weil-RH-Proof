# Record 1343 - 1342 official NO-FIRE verdict + B0b Weil-criterion brick (close-out)

```text
+--------------------------------------------------------------------+
| VERDICT QUALITY: OFFICIAL, fully-gated (11/11 gates green), MODEL  |
| level (certifies nothing, RH not claimed - probe policy).           |
| 1342 B0a official attempt-2 (batch 1545):  VERDICT = NO-FIRE.      |
| 1342 B0b: Weil-criterion equivalence brick COMMITTED (d767a1d),    |
|   green acceptance log now on record (1546_1343_brick_green.log).   |
| The 1342 probe is SPENT (prereg 6b): no further official launch.    |
+--------------------------------------------------------------------+
```

## 1. What this record closes

Beat B0 of the 1341 dissolution plan (B0a falsifier probe + B0b formal
due diligence, executed under the A9 protocol with B0c/B0d left to their
lanes).  Two artifacts, one verdict:

- **B0a** - the prime-free triple-vanishing Gram-minimum falsifier search
  on the m=24 center-shrunk bump class (record 1342 preregistration,
  `1342_b0a_..._preregistration.md`, amendments inv1-inv12) returned
  **NO-FIRE** on the official adjudicating run.
- **B0b** - `ConnesWeilRH/Dev/C1WeilCriterionEquivalence.lean` lands the
  two directions between the surviving gate and `SourceRH`, plus the
  rank-one family trivialization, completing 1341's equivalence claim as
  a machine-checked statement.

## 2. Official attempt-2 disclosure (batch 1545) - the verdict run

Runner `1342_official_runner.sh`, m=24, NQ=2^17, resolution doubling
2^18 for G4, wall 2682.9 s, numpy 2.5.3 / mpmath 1.4.1.  Log
`1342_logs/1545_1342_official_attempt2.log`, machine-readable
`1342_falsifier_results.json` (both preserved; attempt-1 verbatim as
`*_attempt1`).  Verbatim adjudication block:

```text
== 1342 B0a falsifier probe (OFFICIAL) m=24 NQ=131072 QL=28.0 ==
G1a provenance (broken rule): recomputed +1.895767602e-02 vs committed 0.01895768  rel 2.10e-07  [PASS]
G1b corrected control qw = +1.302073921e-01  (independent-path arch dev 4.26e-16)  [PASS]
G8 control: geom +1.302073921e-01 vs spect(800) +1.302071817e-01 gap 2.10e-07 drift 0.00e+00 (ladder 800/1600) [PASS]
lambda_min(Gm) = +3.083243887e-03   lambda_2 = +3.787179e-03   rank 3/3   sv-ratio 0.00e+00   null-res 2.51e-17
witness: peak-rescaled, r=0.322998 (bound 0.336574)  direct qw = +2.070736544e-01  prime +6.23e-16  vanishing 8.50e-17
G2 support PASS   G3a PASS   G3b PASS   G5 gram-identity 1.57e-13 PASS   G6 witness +2.07e-01 rel-check PASS   G7 prime-free PASS
G8 witness: geom +2.070736544e-01 vs spect(3200) +2.070736453e-01 gap 9.11e-09 drift 6.21e-09 (ladder 3200/6400) [PASS]
G4 doubling: lambda_min +3.083243887e-03 -> +3.083243849e-03  delta 3.85e-11  [PASS]
gates G1a=T G1b=T G2=T G3a=T G3b=T G4=T G5=T G6=T G7=T G8c=T G8w=T
VERDICT: NO-FIRE
DONE 1342  (OFFICIAL, 2682.9s, MODEL, certifies nothing, RH NOT claimed)
```

Headline readouts (parsed from `1342_falsifier_results.json`, constants
are data):

| quantity | value | band (prereg s5) | margin |
|---|---|---|---|
| lambda_min(Gm), m=24 nullspace Gram | +3.0832438870712037e-03 | FIRE <= -1e-6 | ~3083x above FIRE, NO-FIRE >= -1e-8 met |
| lambda_2 | +3.7871787255945176e-03 | (reported) | gap to top of spectrum: 21 eigenvalues, all positive |
| G4 grid-doubling delta (2^17 -> 2^18) | 3.8516048857240026e-11 | < 1e-6 | resolution-independent to 11 digits |
| witness direct qw | +2.070736543730913e-01 | FIRE <= -1e-6 | 5.2 orders of magnitude from firing |
| witness prime-term residue | 6.226582521720284e-16 | < 1e-9 | prime-free window G7 |
| witness vanishing residual | 8.500145032286355e-17 | < 1e-8 | exact triple-vanishing class |
| nullspace residual (G3b) | 2.5067759974435224e-17 | < 1e-8 | Z really spans the constraint kernel |
| Gram identity (G5, polarization) | 1.57278165609441e-13 | < 1e-6 | B = Gram of the bump family |
| G8 control (800/1600): gap / drift | 2.10e-07 / 0.0 | <1e-6 & <max(1e-6,1e-5\|geom\|) | PASS |
| G8 witness (3200/6400): gap / drift | 9.11e-09 / 6.21e-09 | same | PASS, ~100x under budget |

Interpretation: under the corrected kernel (`simpson_fixed`, inv9) and on
the measured-tail-verified explicit-formula dictionary (G8, inv10-12),
the 24-bump prime-free root-window span of the healthy triple-vanishing
class carries **no negative direction**, and the minimum-eigenvalue
witness - the best candidate this class can offer for qw(g) < 0 - sits at
+2.07e-01, i.e. 200000x the FIRE threshold in absolute terms, with its
own spectral-side fidelity verified to 9.11e-09 at T=3200.  The
FIRE/NO-FIRE bands were fixed in the preregistration before any digit
(law 42); the verdict is the one preregistered for this configuration.

## 3. Attempt ledger under law 42

| launch | batch | rig state | outcome |
|---|---|---|---|
| attempt-0 | 1544 (crash) | inv11 | CRASHED pre-digits at anchor-window grid restore (index 131071 vs 32768); zero official digits existed -> inv11b fix, no verdict consumed |
| attempt-1 | 1544 | inv11 (fixed ladder {800,1200}) | all object gates green, **G8w FAIL** (gap 3.95e-05, drift 2.69e-05: 21-dim witness Gevrey tail ~160x slower than the 5-dim smoke witness) -> **ABORTED-UNINFORMATIVE**, disclosed with digits in prereg 5a |
| amendment | commit 06a30bf | inv12 | self-calibrating ladder {800,1600,3200} (cap 6400), band UNCHANGED; authorized exactly one re-run |
| attempt-2 | 1545 | inv12 | **NO-FIRE, 11/11 gates** - the verdict above |

Attempt-2's adjudicated object is bit-identical to attempt-1's
(lambda_min +3.083243887e-03, witness +2.070736544e-01): the amendment
moved only the fidelity gate, never the number.  With the deterministic
lambda_min already on the record before the ladder existed, attempt-2 had
zero selection freedom over the verdict - the disclosure order itself is
the anti-tuning proof.  Per prereg 6b the probe is now **spent**:
B0a's answer for the m=24 prime-free class is NO-FIRE, and no further
official launch of this configuration exists.

Rig fixes found en route, banked as AGENTS 7c law (71): unit-test every
hand-rolled composite quadrature against a trusted reference before it
carries a control anchor (the 1116-era `simpson_uniform` was the 2/3
rule on disjoint triples - two probe generations survived without an
`x^4` test); and fidelity-gate truncation points must be calibrated by
measured drift, not hand-picked.

## 4. B0b: the surviving gate IS the Weil criterion (machine-checked)

`ConnesWeilRH/Dev/C1WeilCriterionEquivalence.lean` (commit `d767a1d`),
11 declarations, all three parts pure reassembly - no new analysis:

```text
part 1 (forward)   SourceRH ==> forall g, 0 <= qw g
    W3 split + W1 on-line nonnegativity + SourceRH kills the off-line
    index set (offLineSpectralMass_eq_zero_of_sourceRH: tsum of zeroes).
    The vanishing hypothesis is not consumed: vacuous sign under RH.

part 2 (reverse)   (forall vanishing g, 0 <= qw g) ==> SourceRH
    committed capstone + committed right-zero detector existence +
    sign transfer through qw_eq_spectralWeilValue_centerTwo.

=>  weilCriterion_iff_sourceRH :
    (forall vanishing g, 0 <= C1SameOwnerWeil.qw g) <-> SourceRH

part 3 (trivialization)   qw nonnegativity <=> Nonempty
    PositiveTraceOperatorLimitFamily (iota := Unit, rank-one carrier,
    CONSTANT family (qw(g) • id), zero remainder)
=>  qw_nonneg_iff_nonempty_family
```

This is the construction half of 1341's dissolution claim, now verified:
the operator-family contract carries no strength beyond the scalar
`0 <= qw g`, and the single remaining obligation of the G8 tower is
exactly the classical Weil-criterion gate.

Acceptance: `1546_1343_brick_green.log` - `Build completed successfully
(3710 jobs)`, zero `^error:` lines, zero `sorryAx`, and the file's own
`#print axioms` footer shows only `[propext, Classical.choice,
Quot.sound]`.  (Naming note: `build-logs/1545_1343_brick1.log` is a
mid-fix build round of the same file whose `sorryAx` prints were
downstream artifacts of failed proofs, and the number 1545 there is a
different batch tree from the probe's batch 1545 - logs live in separate
directories; kept for history, not cited as acceptance.)

## 5. What this changes in the tower - and what it does not

```text
                     BEFORE 1342/1343        AFTER
  gate 0 <= qw(g)    named residue of        IDENTIFIED as the classical
  on the vanishing   1341's dissolution      Weil criterion, iff
  class              (a moving target?)      SourceRH  [B0b, formal]
  counterexample     untested at Gram-min    m=24 prime-free root-window
  search             resolution              class: NO-FIRE [B0a, model]
  family contracts   possible extra strength  trivialized to the scalar
                                             [part 3, formal]
```

- Does NOT establish: any lower bound with proof; anything about RH;
  anything outside the m=24 center-shrunk prime-free class (the class
  can be enlarged - new object, new preregistration, never a rerun of
  this spent probe).
- DOES establish: (a) the falsifier lane on the current class is empty
  at the resolution where the machinery is trustworthy - the same
  machinery that in 1212-1213 produced the FP=-3.321*qw readout now
  carries its own affirmative explicit-formula fidelity certificate on
  the adjudicated witness; (b) formally, hunting a counterexample to
  `0 <= qw` on the vanishing class IS hunting an off-line zero - B0b's
  `weilCriterion_iff_sourceRH` removes every intermediary between the
  gate and RH; (c) the moving-family surface (1340's Fork B framing)
  needs no further engineering: part 3 shows any family route is
  scalar nonnegativity in disguise.

## 6. Artifacts

- `docs/proofs/1342_b0a_..._preregistration.md` (inv1-inv12 ledger, 5a
  attempt-1 disclosure, 6b attempt-2 authorization) - commit `06a30bf`
- `docs/proofs/1342_prime_free_falsifier_probe.py`, smoke + official
  runners - same commit line
- `docs/proofs/1342_falsifier_results.json` (attempt-2 verdict) and
  `1342_falsifier_results_attempt1.json` (ABORTED, disclosed) - this
  record
- `ConnesWeilRH/Dev/C1WeilCriterionEquivalence.lean` - `d767a1d`
- logs: mirror `docs/proofs/1342_logs/1544_1342_official_attempt1.log`,
  `1545_1342_official_attempt2.log`, `build-logs/1546_1343_brick_green.log`
- commits pushed: `4c1fdd3..06a30bf` (1342 line) + this record

## 7. Next steps

1. **B0d (owner decision, 1341 s5)**: the only analytic surface left
   under the G8 tower is proving `0 <= qw(g)` on the vanishing class
   directly - i.e. the Weil criterion itself - since B0a closed the
   cheap falsifier lane and B0b+part 3 closed every reformulation
   detour.  Owner decides whether to fund a positive proof campaign
   (H2-style convexity/positivity machinery, now with the exact
   obligation stated) or to route differently.
2. **A4** (registered analytic surface, 1340 line) stays queued behind
   the B0d decision.
3. **NM registry companion lane** (A9 alternating protocol): unaffected,
   continues on its own cadence.
