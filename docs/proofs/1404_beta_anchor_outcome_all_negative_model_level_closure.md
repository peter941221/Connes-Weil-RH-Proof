# 1404 — Route-beta anchor outcome: 25/25 NEGATIVE on the exact complex 7-node class; pillar A of the 1081 exit is dead at model level, rung 5 stands alone as the wall

Date: 2026-09-14. Outcome record of prereg 1403 (v1 ae6a12f + v2
4ae30e0, GI clause) and of the recon 1402. Instrument imported from
the certified 1398 v3 chain; the only new code is the n=7
transcription and the SingleOwner evaluator (prereg section 1), plus
one rig-only checker fix (section 2). RH not claimed.

## 1. Verdict (up front)

The measurement 1402 said was the last rung-3 science surface, run and
answered uniformly:

* VALID invocation 3: `DONE gates=G0:PASS,GI:PASS,GS:PASS,GT:PASS,GF:PASS,GD:PASS,GR:PASS,GQ:PASS`
  and `VERDICT betaAnchorWitness=NONE cells=POS:0,NEG:25,TIE:0,BAD:0`.
* **`A_beta(rho) = arch h_rho.convSq < 0` at every cell of the 25-cell
  cohort** — all five rr values x five heights including the three
  first zeta ordinates — with margins 1.3e5..5.3e5 tie-band widths.
  The functional is the 1084/1085 object itself (pair anchor = 4x this).
* The consequence, per the law F14 pattern: the 1086/1087 history was
  never cleanly falsifying (real slice, Galerkin compressions); the
  exact complex class now says the same thing with a certified
  instrument. The anchor-positivity conjecture (pillar A of the 1081
  root-supported exit) is DEAD at model level on the natural class.
  Together with 1402's finding that pillar B of that exit is the
  rung-5 wall itself, the root-supported beta route is closed as a
  campaign at every level except the unlandable: a sign proof of a
  statement whose every measurement says false.
* Cumulative rung-3 census across both families: **107 cells measured,
  107 NEG, 0 POS, 0 TIE** (82 alpha, 1399+1401, + 25 beta here). One
  mechanism family-wide: the sign of the archimedean functional on a
  solved exponential interpolant is FIXED by node content and height,
  and both natural content classes (4-node off-line owner, 7-node
  root-window pair) choose negative. The gate `0 <= qw` survives every
  probe aimed at it — from both directions of construction.

## 2. Invocation chain (all disclosed, laws 42/7j)

* **inv1 — VOID on my own new gate** (v2 section 1 quotes the log):
  GI-beta clause 1 at the v1 class 1e-30 is unsatisfiable against the
  model's own taper band — the sharp-pairing reassembly of the
  TAPERED solution deviates by delta*||c||*R <= 5.6e-15 from the v1
  audit table's own numbers; measured 2.0e-18. Law F12's fourth
  recurrence: the one gate never passed through the audit (whose
  columns contained its predicted failure) was the one I added.
  Remedy: v2 prereg re-locks the clause at 1e-15 (detection margin
  for convention errors stays 15 orders; law F11 preserved).
  Artifacts kept as `*.inv1.*`.
* **inv2 — VALID, cells=POS:0,NEG:20,TIE:0,BAD:5**: all five BADCELLs
  were the im=1054 cohort with gdmax 7.6e-2. Per-node errors localized
  it exactly: detection nodes |error| ~ 3e-16, the five REAL nodes
  3.8e-2 (+-1/2) / 7.7e-2 (+-1) — scaling with |s_j|, the signature of
  ALIASING, not model failure: the imported laplace_g panel-density
  proxy 3|im target|+2 sees 0 at real targets and hands a 16-node
  panel to an integrand oscillating at 730 rad. The A values in inv2
  and inv3 are identical — the defect lived only in the checker.
  Artifacts kept as `*.inv2.*`.
* **rig-only fix** (5885153): `gd_lap` keeps the identical checked
  integral and raises panel density to max(|im target|, |im rho|)+;
  authorized by v2 section 5's pre-written triage path ("bug fix on
  the rig alone if the model is untouched"). No class, no model, no
  cohort change.
* **inv3 — VALID, 25/25 NEG** (this record). GD after the fix: every
  cell 1e-15..1e-13, INCLUDING im=1054 (9.7e-16) and the im=100 cells
  whose 2.2e-7 pass in inv2 had been the same aliasing under class by
  luck; the audit's predicted cancellation scale (~1e-11) is now the
  observed one — better.

## 3. Tier-1 battery (0.99 + 14.134725 I) and gate table

```text
A = -17.3431099115819    S = 1.145e+02    F(0) = +11.909471 (|Im| 6.5e-19)
gdmax = 7.4e-14          gi = (2.0e-18, 7.4e-14)      delta = 1.183e-19
A32 = A64 = A96 = A_R = -17.34311        A(2h) = 4A: exact 0.0 difference
A(eps=0.1) = -17.343109911582044  vs A(eps=0.01) = -17.34310991158192
```

| gate | reading | class | verdict |
|---|---|---|---|
| G0 | rr in (1/2, 0.99], window locked log2/2 | definitional | PASS |
| GI | band-reassembly 2.0e-18 (within v2's delta*||c||*R bound 5.6e-15); float-vs-mp 7.4e-14 | 1e-15 / 1e-6 | PASS |
| GS | 7x7 solve residual | 1e-30 | PASS |
| GT | S-symmetry / J-pair / J(0) | 1.2e-60 / 6.8e-17 / 3.4e-17 | PASS |
| GF | F(0) = ||h||^2 = +11.909471, |Im| 6.5e-19, npw-24 recompute | 1e-6 / 1e-5 | PASS |
| GD | all SEVEN node values end-to-end (targets 1, -1, five zeros) | 1e-6 | PASS |
| GR | 32/64/96 + Richardson agree to 7+ digits | 1e-5 | PASS |
| GQ | A(2h) = 4A | 1e-9 | PASS (exact) |

GV band: threshold 1.15e-4 -> tier-1 sits **1.5e5 tie-widths** below
zero; the eps-pair separation 1.2e-13 relative is itself ~ the band
term — F14-beta empirically confirmed (the taper lever is dead to
13 digits at the strongest-visibility cell of the family).

## 4. Census: A_beta by height and rr (all 25 cells, band=NEG)

| height im | A range | A/S range | |A|/GV-threshold |
|---|---|---|---|
| 14.134725 (FIRST ZERO) | -17.794 .. -17.343 | -0.151..-0.148 | 1.5e5 |
| 21.02204 | -3.9757 .. -3.8794 | -0.131..-0.130 | 1.3e5 |
| 25.010858 | -4.8008 .. -4.6247 | -0.142..-0.139 | 1.4e5 |
| 100 | -7.9071 .. -7.5030 | -0.287..-0.279 | 2.9e5 |
| 1054 | -14.4496 .. -13.7004 | -0.533..-0.506 | 5.3e5 |

Model-level readings (honest: these are properties of the natural
class, not of the Lean noncanonical correction):

* NEGATIVITY IS CONTENT-FIXED: within each height, A varies with rr by
  ~2% and stays negative; across heights, |A| is NON-monotone
  (17.3 -> 3.9 -> 4.8 -> 7.5 -> 13.7), unlike the alpha family's
  monotone growth — but |A|/S grows with height (0.15 -> 0.53): the
  anchor becomes more decisively negative relative to its own scale.
* Term decomposition at tier-1 (from the committed values):
  (log4pi+gamma)F(0) = +37.018, F(0)ln tanh(Rg) = -13.084, central
  integral = -41.277 -> A = -17.343. The central integral dominates;
  the boundary terms cannot save the sign. (Same geography as the
  alpha mechanism finding in 1399 section 6.)
* Comparison to history: 1084 §2 quoted the 1077-1079 surrogate
  measurement of this object as fl2 = -1.294 (different normalization,
  Gaussian-family surrogate); the exact complex 7-node computation here
  is negative at every probe point, at |A| = 3.9..17.8.

## 5. What this closes, what it does not (kill scope)

CLOSES (model level, by the prereg's locked semantics): the pillar-A
conjecture on the natural class — `0 < arch h.convSq` for the 7-node
root-window interpolant is false at every probed off-line candidate,
with margins up to 5.3e5 band widths. The 1081 root-supported exit is
therefore not a route: one pillar is measurement-dead and the other
is the wall (1402 sections 1-2, B0b iff). The last "different shape
class" named by 1401 §4 as escape from F14 is now measured — it chose
the same sign.

DOES NOT CLOSE (formal level, by law 65 and sup-law discipline): no
Lean statement is affected. `0 < arch h.convSq` remains formally OPEN
as a Prop in 1080-1085 (as it must: the Lean `correction` is
noncanonical — no committed construction carries a committed sign, and
a hypothetical PROVER of pillar A would not be refuted by a probe of
one natural class). Nothing in the tower changes: rungs 1-4 closed or
honestly frozen; rung 5 (the gate, B0b-iff-SourceRH) remains THE open
face; RH unclaimed in both directions.

CAMPAIGN STATEMENT (the sentence this wave existed to write): there is
no executable surface left on the rung-3 archimedean sign — not in
grid search (F14-alpha), not in a second shape class (F14-beta + this
25/25), not in a formal campaign (1402: the chain is landed, the exit
needs RH-strength input on pillar B). The 6-rung tower's remaining
work is one mathematical idea at rung 5, i.e. a proof input to the
Weil positivity gate. Rigs and bricks cannot supply it; this register
will say so in every direction it is asked.

## 6. Artifacts and register

Committed: this record; prereg 1403 v1 + v2 + rig (5885153); recon
1402 (ae6a12f). Artifacts (mirror -> repo):
`1403_rig_results.json` sha256
2108d38601b5d4249693ef4ba231e9e3e1f673eb2b2894907c1e9653a1580ece;
`1403_rig_cells.tsv.gz` sha256
88699c906b6bb43b9217e8a5dac72211b766744aa5d3342d7f975cd6fecaeaad;
`*.inv1.*` / `*.inv2.*` variants (sentinels quoted in section 2 and in
v2 section 1). The VALID log `1403_rig_run.log` follows the committed
repo convention: *.log is gitignored; the sentinels are reproduced
verbatim above and every number is in results.json. No Lean was
written this wave; harch/hJ1 stay as in the freeze card.

## 7. Next steps

1. Register closing pass for this wave (README items, project memory
   and law notes out of tree): F15 candidate (audit the NEW gate too —
   its failure numbers may sit in your own audit table), F12 fifth
   recurrence (checker-side resolution is part of gate
   satisfiability), supersession of the "route-beta formal prereq"
   phrasing per 1402 §5.
2. The campaign queue is empty by construction: state the remaining
   options to the owner (Peter) — a rung-5 proof idea is the only
   action that can change the tower; everything else this register can
   execute has now been executed and reported.
3. Keep the standing hygiene: RH not claimed; the 107-cell census is
   gate-consistent evidence, not a sign result for any formal
   statement.
