# 1399 — Rung-3 joint-witness outcome: VALID run, 0 of 41 candidate owner geometries carry (J1) PASS and A(g) > 0; all 41 are NEG by ~7 orders of the tie band; nothing is killed, the complex-owner family is now measured

Date: 2026-09-14. This is the outcome record of the
[1398 v3](1398_rung3_joint_witness_prereg_v3_precision_class_fix.md)
preregistration chain (v1 -> v2 -> v3, model VERBATIM throughout). Run
invocation 3 on WSL is the VALID one; invocations 1 and 2 were VOID by
their own gates and are disclosed in full below. The rung table being
consulted is
[1395 section 3](1395_009_contract_closed_ledger_state.md); rung 3 was
"THE OPEN SCIENCE, (a)". RH not claimed.

## 1. Verdict (up front)

The run is GOOD as instrumentation and BAD as campaign news:

* GOOD: the first-ever evaluation of the archimedean functional on the
  complex route-alpha owner family is complete, gate-certified, and
  internally consistent (scale-invariance exact, detector condition
  reproduced at 2e-7, solve residuals at 1e-56).
* BAD (honest reading): **jointWitness=NONE**. All 41 evaluated
  geometries — tier-1 = the 1394 witness geometry, then the next 40 by
  A-blind max-(J1)-ratio order — have `A(g) < 0` with margin
  `|A| / (1e-6 * S)` between `6.8e5` and `5.1e5`: nowhere near the tie
  band, at every tier, at every `rr` in the candidate head.
* Per the pre-committed kill scope (1398 v1 section 6, re-locked verbatim
  in v2/v3): a negative kills NOTHING. The 1087 sup-lower-bound law
  ("a negative value cannot prove that the full supremum is nonpositive")
  applies in reverse too: 41 negatives cannot prove the supremum is
  negative. Rung 3 remains open science. What this run ADDS is
  information: the negativity is no longer a real-slice artifact.

## 2. Protocol chain (what ran, in order)

```text
inv1  VOID  GS:FAIL,GF:FAIL,GD:FAIL, A=0 exactly
      cause: mpmath 3-arg mp.matrix(m,n,list) silent zero-fill (the same
             trap that voided 1393 inv1; it re-inflicted itself because
             the instrument rewrite did not re-grep the known-pitfalls
             list first). rhs -> 0 vector -> coeff 0 -> g = 0 -> A = 0.
             fix commit: nested mp.matrix([[v] for v in p]) + a local
             rhs-integrity assert so this class fails AT the site.
inv2  VOID  GF:FAIL (7.7e-7 vs 1e-8), GR:FAIL (6.3e-7 vs 1e-8) — the
      gates REFUSED to certify digits at an unachievable class; all
      structural gates (GI/G0/GS/GT/GD/GQ) PASSED at tier-1.
      telemetry: convergence probe A(24/32/64/96) fits error = C/npw,
      C ~ 3.6e-3 (first order) to within 2% — 1e-8 relative is not
      attainable by this instrument at ANY npw. v3 revision (prereg,
      new file; v2 never edited) re-locks model VERBATIM and moves only
      GF_RE_TOL/GR_TOL to 1e-5, adds a 1e-3 GV band margin, and scopes
      tier-2 integrity failures to per-cell BADCELL.
inv3  VALID  DONE gates=G0:PASS,GI:PASS,GS:PASS,GT:PASS,GF:PASS,
      GD:PASS,GR:PASS,GQ:PASS
      VERDICT jointWitness=NONE cells=POS:0,NEG:41,TIE:0,BAD:0
      wall time 204 s; no BADCELL occurred (v3 clause 4 armed, unused).
```

Acceptance was log-based (log-not-exit-code), sentinel strings above
quoted verbatim from `docs/proofs/1398_rig_run.log`.

## 3. Gate table (inv3)

| gate | what it owns | measured | class | verdict |
|---|---|---|---|---|
| G0 | admissibility `Rf+Ru <= log2/2` | all cells | exact | PASS |
| GI | positional decode of the 1393 tsv | every PASS row + every 1000th | 1e-9 rel | PASS |
| GS | mp Gram solve residuals | 5.2e-58 (f), 2.3e-56 (u) | 1e-30 | PASS |
| GT | tool identities S-symmetry / J-pairing / J(0) | 1.2e-60 / 6.8e-17 / 3.4e-17 | 1e-40/1e-10/1e-12 | PASS |
| GF | F(0) > 0, |Im F0|/F0, npw-24 recompute | 5.2e-18, 7.7e-7 rel | 1e-6 / 1e-5 | PASS |
| GD | detector condition \|lap g,rho + 1\| | 2.3e-7 (tier-1) | 1e-6 | PASS |
| GR | npw-32 vs npw-64 recompute of A | 6.3e-7 rel | 1e-5 | PASS |
| GQ | scale invariance A(2g) = 4 A | exactly 0.0 rel | 1e-9 | PASS |

The tier-1 sign margin `|A| / (GV edge)` = 6.8e5 dwarfs the certified
instrument error class (1e-5 relative, Richardson-consistent to 1.4e-5)
by roughly ten orders — the NEG classification is never band-edge
sensitive.

## 4. Tier-1 telemetry (1394 witness geometry Rf=Ru=0.02, eps=epsp=0.01, rho = 0.99 + 1054i, tier-1 of the 1394 PASS band)

```text
A(32) = -88.19525496875   A(64) = -88.19519960   A(96) = -88.19518121
A_R   = 2*A(64)-A(32)     = -88.19514424         (first-order extrapolation)
F(0)  = +17.21588899417838  (re; |Im F0| = 5.2e-17)
S     = 128.94242   GV edge (1+1e-3)*1e-6*S = 1.29e-4
lap(g,rho) = -1 + 2.3e-7j-ish magnitude error
alpha_f = 5.893e-12   delta_f = delta_u = 7.147e-33 (float64-invisible; see 6)
A_alpha2 = A exactly (delta sliver is below float64 resolution of rIn/rOut —
           informational: the alpha-SENSITIVITY probe has no lever at this tier)
```

## 5. The 41-cell census (all NEG; full rows in the committed artifact)

Cohort structure (the A-blind ordering grouped by geometry, not by sign):

| tier | Rf | Ru | eps,epsp | rr | Im rho | A range | A/S |
|---|---|---|---|---|---|---|---|
| 1 + 19 cells | 0.02 | 0.02 | all 4 combos | 0.55..0.99 | 1054 | -88.238 .. -88.195 | -0.684 |
| 20 cells | 0.05 | 0.02 | all 4 combos | 0.55..0.99 | 1054 | -44.812 .. -44.740 | -0.636..-0.637 |
| 1 cell | 0.08 | 0.02 | 0.01/0.01 | 0.99 | 1054 | -29.364 | -0.609 |

Two patterns in the data, stated as MODEL observations:

* `eps` and `epsp` (the taper epsilon parameters) move `A(g)` not at all
  — cells 0/5/6/15 agree to all printed digits. Mechanism: eps enters the
  shape only through `delta = min(R/2, eps*alpha/(4(1+eps)TB^2))`, and at
  these tiers `delta ~ 1e-33` is below the float64 resolution of
  `rIn = R - delta`; the epsilons are rung-2 (J1) levers (they move the
  ratio through alpha and TB), not rung-3 shape levers, on this grid.
* `A/S` sits in a narrow band `[-0.684, -0.609]` and `|A|` tracks
  `1/(Rf+Ru)` roughly — the functional value is dominated by a
  family-universal negative piece. Decomposing at tier-1: constant term
  `(log 4pi + gamma) F(0) = +53.51`, tail term `F(0) ln tanh(Rs) =
  -55.42`, so constant + tail = -1.91, and the CENTRAL integral
  `int_0^{2Rg} [e^{y/2}(F(y)+F(-y)) - 2F(0)] / (2 sinh y) dy` alone is
  about **-86.3**: the negativity is carried by the drop of `Re F(y)`
  below `e^{-y/2} F(0)` on the oscillation scale `1/(2 Im rho) ~ 5e-4`,
  against the logarithmically heavy `1/(2 sinh y)` weight. This is
  exactly the mechanism the classical Weil criterion fights, and it says
  the next rung-3 design must reduce the FORCED high-frequency content of
  the owner (the detector condition at height 1054 pins it in) rather
  than re-tune radii or epsilons — those levers are now measured dead or
  fixed-sign on this family.

## 6. What this decides and what it does not (kill scope, pre-committed)

DECIDES (MODEL layer only):
```text
- the 41-cell head of the (J1)-PASS candidate list contains NO joint
  witness; the (J1)-optimal geometries are arch-pessimistic for rung 3
  (max-ratio == best-tapered == most oscillation-pinned);
- the 1080-1087 "never seen positive" history now extends to the complex
  exactly-vanishing owner family on this grid — the real-slice excuse
  from 1397 section 3 is retired.
```
DECIDES NOTHING about:
```text
- the sign of A on ANY owner outside the 41 evaluated geometries or
  outside the 4-node route-alpha shape (sup-lower-bound law, 1087 s2,
  quoted verbatim in 1397 s3: a negative cannot bound the supremum);
- whether a POSITIVE owner exists at LOWER heights (the head is
  im = 1054 by A-blind ordering; the first zero of zeta is height
  14.1347 — this rig never evaluated im near the first zero because no
  such cell exists in the 1393 PASS band: the J1-optimal cells are
  high-frequency by construction);
- the formal gate (harch/hJ1 remain UNDISCHARGED in Lean — these are
  MODEL digits, law 65), detector data (rung 4), the Weil criterion
  (rung 5 — the classical wall, needing a PROOF, no rig substitutes),
  and RH in either direction.
```

## 7. Artifacts and hashes

```text
scripts/run_1398_rig.py                                (committed, inv3-calibrated)
docs/proofs/1398_rung3_joint_witness_prereg.md         (v1, superseded)
docs/proofs/1398_rung3_joint_witness_prereg_v2_gateS_fix.md            (superseded)
docs/proofs/1398_rung3_joint_witness_prereg_v3_precision_class_fix.md  (executed)
docs/proofs/1398_rig_run.log          sha256 of results.json =
docs/proofs/1398_rig_results.json          caf07e204b267f88b16f84da8ecf642fe225c81f1e9c2046b8e309d76a4f325c
docs/proofs/1398_rig_cells.tsv.gz                      f415dd641ae632fbf4e031cf5472076ac5eeb6fc223a7e0cd65fd9799ddb2298
(quarantined VOID telemetry: *.inv1.*, *.inv2.* — committed unmodified)
```

Note on the VALID log itself: the repo gitignores `*.log` by design (zero
committed run logs in history; precedent 1212 committed only its
invocation JSON), so `1398_rig_run.log` lives in the working tree, its
sentinel lines are quoted verbatim above, and every number in it is
reproduced with full precision in the committed `1398_rig_results.json`.
The two VOID logs escape the pattern only by their `.inv1`/`.inv2`
suffixes and are committed as audit telemetry.

## 8. Next executable surfaces the data itself points at

1. LOW-HEIGHT rung-3 rig: the J1-optimal head is pinned at `im = 1054`;
   a joint witness (if the family admits one) is more plausible at small
   heights where `delta ~ eps*alpha*TB^-2` is LARGER (TB ~ e^{|rho|R}
   shrinks) and the float64-visibility of the taper slivers returns —
   but the 1393 PASS band must be re-mined for `im` candidates below the
   current head before any such prereg (the census says: 1700 candidate
   geometries exist, only 41 were evaluated).
2. SHAPE-CLASS extension: 5+ node owners (route beta, the 7-node/orbit
   family of 1389) put more frequencies under the solve and give rung 3
   levers the 4-node family provably lacks; that is a formal (Lean) task
   before it is a rig task, and it is the only measured-live direction
   this run leaves for "positive at ANY owner".
3. HOLD: rung 3's campaign value is as a lemma to rung 4's detector
   data; with 0/41 NEG and the mechanism analysis of section 5 (forced
   high-frequency content against the 1/(2 sinh y) weight), the
   mainline recommendation is the same as 1395 s3's second honest
   reading: the wall is rung 5, and no rung-3 grid has been, or by the
   sup-law will be, a falsifier or a proof.

RH not claimed anywhere in this record.
