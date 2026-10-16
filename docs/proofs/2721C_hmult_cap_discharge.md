# Record 2721C: the multiplicity premise hmult is discharged -- first
hypothesis actually REMOVED from the wired row-B contradiction

**Verdict: 2721C GREEN -- `wiredMultCapDischargedRowB2721C` proves
`spectralMultiplicityConstant <= wiredMultCapRowB2721` (515) from the
zero-hypothesis coarse cap
`C1RouteAMultiplicityBound.spectralMultiplicityConstant_le_coarse`
(`spectralMultiplicityConstant <= 128.65`, itself proved inside
`C1RouteAMultiplicityBound.lean` from `kernelSmallMomentConstant_le`,
`kernelTailConstant_le` and `xi_two_log_abs_le` plus
`Real.log_two_gt_d9` -- no artifact imports, no numeric data
hypotheses), and the variant theorem
`fourPointContradictionRowBWired2721C` carries EIGHT named hypotheses
where the 2721B parent carried NINE. This is a premise PROVED, not
renamed, under the core-progress gate.**

## What it is

The 2721B wired contradiction (commit 013efd59) packaged the row-B
(gamma_2, N = 5, n = 3) reopen motion into one Lean theorem with nine
explicit hypotheses. The cheap strike flagged in S8 was `hmult :
spectralMultiplicityConstant <= 515`: the pin was chosen to dominate
the record-2354 artifact cap 2573/20 = 128.65, and the checker already
knew that number. The probe here checked the OTHER side of the tie --
the Lean cap theorem `spectralMultiplicityConstant_le_coarse` turns
out to have NO hypotheses at all: it is a closed derivation in
`ConnesWeilRH/Dev/C1RouteAMultiplicityBound.lean:98`, with its own
paired audit (`C1RouteAMultiplicityBoundAudit.lean` prints it among
ten axiom records). So `hmult` was never a residual obligation in
substance; the 2721B packaging simply had not composed it yet.

## Why it is legitimate

- The discharge is a pure Lean composition: `.trans` of the coarse cap
  with the closed arithmetic step `norm_num [wiredMultCapRowB2721]`
  on `128.65 <= (515 : Real)` -- the same proof pattern
  `spectralMultiplicityConstant_le_multProxy2248` already uses one
  file above (line 117).
- 2ab doctrine: the parent
  `fourPointContradictionRowBWired2721` is NOT edited in its
  statement; the variant is additive and existing callers compile
  unchanged.
- No owner, quantifier or detector changed: the variant feeds the
  discharge into the parent at the hmult slot, so the remaining eight
  hypotheses are exactly the S8 reopen-motion list minus hmult.

## Evidence

- `ConnesWeilRH/Dev/C1FourPointRowBWired2721.lean`: new import
  `ConnesWeilRH.Dev.C1RouteAMultiplicityBound` (line 7),
  `wiredMultCapDischargedRowB2721C`,
  `fourPointContradictionRowBWired2721C` (verbatim parent binder list
  minus the hmult line, body = parent application with the discharge
  at slot 3).
- Linux-native incremental build:
  `build-logs/2721c_audit_build.log`, footer
  `Build completed successfully (3862 jobs)`, zero lines beginning
  `error:`, zero sorry occurrences.
- Axiom census: FIVE declarations, each exactly
  `[propext, Classical.choice, Quot.sound]`
  (`results/2721b_axiom_census.json`, rebuilt from the 2721C log).
- Checker `scripts/check_four_point_wired_2721.py` now 43/43 PASS:
  new guards `import_coarse_cap_module`,
  `discharge_uses_coarse_cap`, `hmult_binders_at_two`,
  `variant_drops_hmult_binder`,
  `variant_calls_parent_with_discharge`, plus the arithmetic
  `lean_coarse_cap_eq_artifact_cap` (the 2354 artifact cap
  `2573/20` must equal the Lean theorem literal -- the .trans chain
  closes at that exact rational).
- Win/WSL source md5 parity for both modules
  (1e748d07.., aabe3d79..) before and after the build.

## Instrument notes (record-local laws)

- Prefix-shadowing in line-oriented guards: `#print axioms
  fourPointContradictionRowBWired2721` is a strict substring of the
  variant's print line, so the unanchored count double-hit; guard at
  LINE granularity (`"#print axioms X\n"`). This is the record-2049
  word-boundary law re-firing at text-guard granularity -- every
  identifier guard in a transcription checker needs a boundary
  (line-anchor, word boundary or trailing token).
- Binder-text guards must be written against the BINDING SITE region,
  not the whole file: `(hmult : ...)` legitimately occurs TWICE
  (the eta-budget lemma and the parent contradiction) -- the honest
  variant guard is "no hmult binder inside
  `theorem fourPointContradictionRowBWired2721C ... False :=`" plus a
  global count-equals-two transcription pin. A first-draft guard
  asserting count-one was falsified by the source itself before any
  build.

## Status lines

- Producer: UNCHANGED. No GO. The remaining eight hypotheses are:
  hNorm/hIm (2719-grade interval pins), hvanish/hsupport
  (g-construction), hcontract/hquartic/hquadratic (the 2720 strip
  envelopes at actual-owner grade -- the big transfer brick), hgate24
  (owner-grade P5 gate sign -- the RH core), hprefix (P2 shell
  prefix).
- Map-103 freeze: UNCHANGED (reopen motion in progress, premises
  shrinking one real theorem at a time).
- No RH claim.
