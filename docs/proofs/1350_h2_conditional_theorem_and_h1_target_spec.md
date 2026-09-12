# Record 1350 (DRAFT HARVEST) - H2 conditional theorem + H1 target-spec annex

```text
+---------------------------------------------------------------------+
| DRAFT ASSEMBLY, not a probe. No new digits, no prereg bands, no     |
| Lean build. MODEL grade; certifies nothing; RH NOT claimed.         |
| Purpose: the N1 lane is registered PENDING (1345) with the harvest  |
| specs H1/H2 named but never written down. This record writes them   |
| down NOW, from constants parsed VERBATIM out of the committed       |
| records 1345/1346 (file:line cited below; constants are DATA) so a |
| future NLLE proof (ours or anyone's) turns the harvest into         |
| ASSEMBLY instead of invention.                                     |
| Owner order 2026-09-12: "can finish everything in parallel".       |
+---------------------------------------------------------------------+
```

## 1. What this is / Why / How

- WHAT: two publishable deliverable specs hanging off the N1 contest
  route - H1 = the exact quantitative statement of NLLE (the single
  missing bone C7), H2 = the conditional theorem "RH unless an
  ultra-near-line local majority exists above height 3e12".
- WHY write pre-proof: (i) the statement inventory forces every
  placeholder in 1346 to be either discharged or named; (ii) if NLLE
  ever lands, priority and clarity belong to whoever wrote the
  quantitative target first; (iii) the H3 margin-map simulator
  (1345 s5) needs exactly this spec as its input format.
- HOW: assembly only. Sections 2-4 quote committed records by
  file:line; nothing here re-derives a bound from scratch.

## 2. H1 - the NLLE target spec (near-line local exclusion)

Verbatim skeleton from the committed spec box
(1346_n1..._NLLE_target_spec.md:132-134):

```text
  For a height parameter T0: in EVERY Nyquist window [y, y + pi/sigma]
  at height >= T0, the multiplicity-weighted count of zeros OFF the
  line is < 1/3 of the multiplicity-weighted count of ALL zeros in
  the window.
```

Parameter dictionary (all parsed, with provenance):

| symbol | value | source (file:line / URL) | status |
|---|---|---|---|
| sigma (log-band) | log 2 | narrowest strip all located tech admits (1345 s4) | locked |
| W (Nyquist width) | pi/sigma ~ 4.53 (two-window 9.33) | 1345:173; 1346:74-75 | locked |
| f* (majority threshold) | 1/3 | 1346:80 "f < 1/3 uniformly for all delta <= 1/2" | locked |
| verified base | 3*10^12 | 1345:174 (Platt-Trudgian 2021) | locked |
| multiplicity cap | m(rho) <= 10 log T unconditional | 1345:175 (Titchmarsh Thm 9.2 via MoE 514655) | locked; sharpening OPEN |
| S(T) band | \|S(T)\| <= 0.112 logT + 0.278 loglogT + 2.51 (+ 0.2/T in a 2026-II citation) | 1345:173; this window's multi-citation parse of Trudgian | T-range of primary STILL OPEN (task #9) |
| max zero gap | ~1.41 << 4.53 | 1345:173 | derived from S(T); inherits its open T-range |
| window occupancy band | [~0.50, ~0.94]*log T | 1346:101, marked PLACEHOLDER | NOT verified - H3/#9 job |

Labelled assumption (the honest asterisk on H1): the derivation of the
per-zero balance (factor 4 exactly consumed by the 4 quartet members,
1346:67-75) uses the bump-family frame bound C6 - the SECOND bone,
registered explicit in 1346 s1. H1 as written above does not quantify
over test functions and so is C6-free; the CONTEST reading of H1
(via (star)) inherits C6.

NLLE(T0) <=> RH for any T0 >= 3e12 is the committed equivalence claim
(1346 header; losslessness of the (star) chain, 1345 s2-3).

## 3. H2 - the conditional theorem (statement + proof skeleton)

Draft statement (schema; constants as parsed):

```text
  THEOREM H2 (target form). Assume: at every height T > 3*10^12, NO
  Nyquist window [y, y + pi/log 2] at that height contains a
  multiplicity-weighted local majority of ULTRA-NEAR-LINE off-line
  zeros (ultra-near-line := Re(rho) - 1/2 <= c0 / log T, with c0 the
  kernel-ratio constant below). Then RH holds.
```

Proof skeleton, per leg (each leg either committed-formal or named
OPEN - no silent gaps):

```text
  Suppose an off-line zero rho exists (beta != 1/2, gamma > 3e12).
    [L1] quartet bookkeeping: the quartet {rho, rhobar, 1-rho,
         1-rhobar} carries total loss 4*mult*Re[G(w)G(-w)]
         (CORRECTED algebra: quartet factor 4, factors are conjugate
         ONLY on the line; 1345:56-64).
    [L2] gate => (star): 0 <= qw(g) for the class is equivalent to
         sum_on mult|G(i gamma)|^2 >= 4 sum_quartets mult|G(w)G(-w)|
         (1345:71; iff legs machine-verified at the gate itself via
         C1WeilCriterionEquivalence.lean:136-141 / :118-129,
         commit d767a1d).
    [L3] per-zero balance: localized kernel (tails sinc^2 ~ 0 at
         adjacent-window nodes, 1346:74-75) forces the (star)
         violation to occur WINDOW-WISE: some window has weighted
         off-line fraction >= 1/3.
         [OPEN: window localization = estimation leg; needs C6 frame
          bound as INPUT. This is the brick B3/B2 split in 1351.]
    [L4] ultra-near-line pinching: a violating window cannot host
         quartets at bounded-away delta, because the kernel ratio
         |G(w)G(-w)| / |G(i gamma)|^2 -> 1 only as delta -> 0
         (1346:78-80 reads f < 1/3 uniformly for delta <= 1/2; the
         converse direction - a violation forces delta small - is the
         quantitative content of H2's hypothesis and inherits the
         same C6 input as L3).
    [L5] S(T)/density slack: none of the located unconditional inputs
         (density, gaps, pair correlation, DH, multiplicity caps)
         BLOCKS the resulting configuration (1346 s3 table rows:
         window occupancy NO / multiplicity NO - needs m <= 0.23 log
         T vs available 10 log T / clustering NO). So H2 is
         CONSISTENT-FORMULABLE, not derivable from located tech -
         same COLD-STRUCTURAL verdict as 1346 s4, now exported as an
         external-facing statement.
```

Conrey-Li immunity rail (1345 s3): H2 is an EQUIVALENCE-condition
statement (RH iff no violating window); like Conrey-Li, such a
theorem can be hard but cannot be wrong-by-accident - and we do not
claim to have proved H2. Its legs L3/L4 are OPEN estimation
problems; the theorem as written is a TARGET.

## 4. What H2 buys if it lands (and what it does not)

- Buys: (i) the falsification search collapses to ONE finite-shaped
  event (a window census at height > 3e12); (ii) the H3 margin-map
  simulator becomes meaningful - it measures HOW FAR the known
  configurations sit from the L3/L4 violation threshold, i.e. turns
  the thermometer into a map; (iii) publication-grade articulation of
  "where RH lives" independent of our Lean tower.
- Does NOT buy: any reduction in logical strength - NLLE <=> RH
  (1346), so H2's hypothesis is as hard as RH unless its ultra-
  near-line refinement is shown strictly weaker (open, and 1346 s3
  says nothing located can show it). NO CAPACITY GAIN IS CLAIMED.

## 5. Discrepancy ledger (honest bookkeeping)

- The "0.72 log(T/2pi) smooth occupancy" figure circulating in
  working notes = W/(2pi) * log(T/2pi) with W = pi/log2; it sits
  INSIDE the [0.50, 0.94]*log T band (1346:101), which is marked
  PLACEHOLDER. Until task #9 recomputes the band from the parsed
  S(T) constants at PRIMARY-source T-range, H2 must be quoted with
  the band, never with 0.72 alone.
- 1345:173 lists S(T) WITHOUT the 0.2/T term; this window's citation
  parse shows a Trudgian "II" refinement adding +0.2/T for T >= e.
  Both retained; primary reconciliation is task #9.

## 6. Status and next steps

STATUS: DRAFT registered; N1 lane stays PENDING (spec exists now,
funding decision unchanged: not funded per 1346 s6 / 1347 s4).

1. Task #9 (thermometer backlog): recompute window-occupancy band +
   S(T) primary T-range -> converts H1 placeholder row to locked.
2. H3 margin-map simulator (needs this spec as input format):
   owner-gated, still unfunded.
3. Lean legs L1/L2 already formal-adjacent: L2's gate legs are
   committed (d767a1d); see 1351 for the (star)-brick design that
   would close L1/L2 mechanically.
