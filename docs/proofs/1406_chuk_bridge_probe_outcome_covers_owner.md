# 1406 — 1405 cross-term probe outcome: COVERS_OWNER by double structural kill; invocation ledger, transcription forensics, and the dictionary triangle escalation

Date: 2026-09-14. Model-level outcome record for the prereg committed at
`docs/proofs/1405_chuk_pillarB_bridge_recon_and_cross_term_probe_prereg.md`
(prereg file UNTOUCHED; gate classes UNCHANGED throughout; law 42).
No Lean was written. Nothing was falsified. RH not claimed, in either
direction.

## 1. Verdict up front

`scripts/run_1405_probe.py` rev2, invocation 5, is the first VALID
invocation. Sentinels, verbatim:

```
DONE gates=G0:PASS,G1:PASS,G2:PASS,G4:PASS
VERDICT chukBridge=COVERS_OWNER P_h=17.34310991158 P_r=0.68259145 P_m=16.660518 P_x=1.1646141e-16
sha256 docs/proofs/1405_probe_results.json = a1df2a7bc320402680dad0348e9e8d3b879a5273c928e3df12f201d483692990
```

The prereg's §3 prediction (cross terms do not vanish sectorwise ⇒
EXCLUDES_OWNER is the live risk) is DEAD for two independent structural
reasons (section 4 below), and both fired at the measured cell:
`P_x = 1.16e-16` is float64 rounding noise around an exact zero. The
prereg §5 dichotomy was therefore vacuous at lock time — the EXCLUDES
branch was not merely unfired, it was unreachable (disclosed as a prereg
design defect; law F16).

Per the prereg's COVERS reading, the output of this probe is an
escalation, not a consumption: section 5 states the triangle and prices
the one remaining executable item (a scalar dictionary double-evaluation,
1407 candidate). The bridge is NOT consumed and NOT dismissed: Chuk's
certificate reaches our owners at the level of psi's blind spots, but
"Q_Chuk = psi as functionals" is still an unverified convention identity,
and the chain is machine-verified, so if the dictionary held with sign
+, the combination would decide RH — which no two papers can be trusted
to do silently.

## 2. Invocation ledger (law 7j disclosure)

| inv | script state | outcome |
|-----|--------------|---------|
| inv1 | diagnostic `F_at(own, y)` call missing `npw` | crash: `TypeError: F_at() missing 1 required positional argument` (rig-only fix, commit `0af2172`) |
| inv2 | early adaptive-quadrature variant | killed mid-run, empty log (the documented mp.quad-over-float64 stall family; rig-only fix, commit `c2dd94d` fixed mp panels) |
| inv3 | float-mirror `A_trapz` | crash: broadcast shapes `(131070,) vs (131071,)` (rig-only fix, commit `8396e75`) |
| inv4 | fixed, completed 394.7 s | `DONE gates=G0:FAIL,G1:FAIL,G2:PASS,G4:FAIL` — VALID RUN OF THE WRONG FUNCTIONAL: `A_of` had been RECONSTRUCTED from the 1397 paper derivation instead of transcribed from `run_1398_rig.compute_A`, violating the prereg's own section 4 ("No reimplementation of the solve or the A-functional"). Artifact kept renamed: `docs/proofs/1405_probe_results.inv4.json` |
| inv5 | rev2: verbatim `compute_A` transcription with only the `F_at` call site substituted into an evaluator argument | VALID, 2.4 s (165x faster than inv4 because the 131k-point trapz mirror is gone; summation-class G1 replaced by mp-vs-float on the instrument's own grid) |

Root cause of the inv1-inv4 line: `A_of` dropped (i) the analytic tail
term `reF0 * log(tanh(Rg))` and (ii) the `owner.Cg` kink-breakpoint grid,
and integrated over `[0, 2*rOut]` with uniform 32x24-GL panels instead of
`[0, 2*Rg]` with the frequency-density rule. G0 is exactly the gate
designed to catch this and it caught its own host's bug for four
consecutive invocations before the transcription fix.

## 3. Forensics: attributing inv4's G0 gap

From the inv5 result JSON (`forensic_*` fields), with
`INV1/inv4 A_h = -42.7645220321604053` and the committed
`A_instrument = -17.34310991158192`:

| component | value | identity |
|-----------|-------|----------|
| total gap (inv4 - instrument) | -25.421412120576420 | = missing tail + grid residue |
| dropped analytic tail | -13.083884977568012 | `F0_re * log(tanh(Rg))`, F0_re = 11.909465 — this is the very "lntanh -13.084" line of the 1404 term decomposition: the reconstructed functional dropped a term the register had already committed |
| grid/domain residue | -12.337527143008408 | uniform panels + wrong domain vs the Cg kink grid on [0, 2*Rg] |

The residue is larger than expected for a smooth integrand — but it is
entirely inside `[Y0, 2*Rg]` quadrature geometry: the F evaluator itself
agrees with the instrument at all six sampled nodes to max 1.02e-12
(`probe_vs_instrument_F`), so the discrepancy is functional-level, not
data-level, exactly as the transcription diff predicts. The instrument
`A_instrument` and the verbatim-transcribed `A_h` now agree to 2.07e-12
with a 2e-4 tie class (G0 PASS at 8 orders of margin).

## 4. Measured cell + the double structural kill

Cell: tier-1 beta owner (rr, im) = (0.99, 14.134725), window Rg =
log2/2 = 0.3465735902799726, support of F exactly 2*Rg = log2.
`pole_terms_max = 5.44e-27` (pole ~ 0), `F_h(log 2) = 0.0` exactly
(prime sum invisible; endpoint of support), so `P = -A` is exact psi.

| quantity | value | note |
|----------|-------|------|
| P_h = psi(F_h) | +17.343109911584 | = -A; 1403 committed -17.3431099115819 |
| P_r = psi(F_r) | +0.682591448 | real sector |
| P_m = psi(F_m) | +16.660518463 | IMAGINARY sector carries 96.1% of psi |
| P_x = psi(cross) | +1.1646141e-16 | float noise around structural zero |
| G2 (identity) | 2.12e-14 | <= 1e-9 class |
| G1 (mp vs float) | 4.56e-16 | summation-class audit only |

Kill (a), blindness — for ANY complex h, the cross part is
`F_d(y) = 2i * odd(C)(y)` where `C(y) = int r(u) m(u+y) du`: pure
imaginary and odd. Every register readout of psi pairs y with -y:
`archimedeanNumerator F y = e^{y/2}(F y + F (-y)) - 2 F 0`
(`Dev/C1SameOwnerWeil.lean:48-52`); `poleTerm F = (laplaceAt F (1/2) +
laplaceAt F (-1/2)).re` (`:31-33`); `finitePrimeTermComplex =
Lambda(n)/sqrt n * (F (log n) + F (-log n))` (`:36-41`). Each kills
imaginary-odd inputs identically: the arch numerator reads the even part,
the pole pair-sum is `integral 2 F_d(y) cosh(y/2) dy` of an odd function,
primes read `F(log n) + F(-log n)`. So `psi(F_d) = 0` identically — a
three-line machine-checkable model lemma we did not write in Lean; the
measurement `P_x ~= 1e-16` is its float shadow. Consequence for M2:
Chuk's definition-by-sectors `Q(Re) + Q(Im)` AGREES with his full
Hermitian functional on anything psi can see. The parity objection that
motivated the probe is dead for all owners, not just this cell.

Kill (b), exact reality at F-level — bonus finding. The tier-1 solve
data is odd-equivariant: `nodes7 = [0, -1/2, +1/2, rho, -rho, -1, +1]`
is closed under negation and the committed targets `(1 at rho, -1 at
-rho, 0x5)` satisfy `target(-n) = -target(n)`; uniqueness of the 7-mode
interpolation forces `h(-x) = -h(x)` analytically. Measured:
odd-defects of both sectors are exactly 0.0 at sampled points;
`|F_d| <= 2.5e-14` at five y-samples (float rounding). So at this cell
F_h is itself real-even (`r, m` same parity kills `C(y) - C(-y)`
identically), NOT just invisible-to-psi. The owner is genuinely complex
(phase-degeneracy ruled out: min relative deviation of `m` from
`+-lambda r` is 0.23), yet it is a REAL function up to psi's blind
part, and its psi equals psi of the real-even function `(r~star r +
m~star m)`. Register-level corollary (model): on the EvenOddPair anchor
family, 1397's "untapped complex structure" does not exist — the
complexity lives entirely in the component no windowed readout can see.

## 5. Escalation per prereg reading: the dictionary triangle

The prereg: "COVERS_OWNER ... the register then has a genuine
chain-vs-preprint collision to escalate (highest-priority red flag, no
silent fix)." Escalated, in exact form. Three statements:

    +--------------------------------------------------------------+
    | T1  MACHINE-CHECKED CHAIN (register):                        |
    |     not-RH  ==>  exists owner g (smooth, supp g in           |
    |     +-(log2)/2) with  qw g = psi(g~star g) < 0               |
    |     [1081 exit; 1375 F3 producer; qw = psi by DEF            |
    |      C1SameOwnerWeil.lean:197/:204]                          |
    +------------------------------+-------------------------------+
                                   |  psi = Q? (M2 dictionary)
    +------------------------------v-------------------------------+
    | T2  EXTERNAL CERTIFICATE: Q_Chuk(f) >= 8.9e-18*||f||^2 for   |
    |     ALL complex L^2 f with supp in [-0.8,0.8]  [unrefereed]; |
    |     real case with supp in +-(log2)/2 classical, Yoshida     |
    |     1992 / Connes-Consani [peer reviewed; quoted via         |
    |     arXiv:2608.24827 abstract]                               |
    +------------------------------+-------------------------------+
                                   |
    +------------------------------v-------------------------------+
    | T3  INV5 (this record): psi(h~star h) = psi(r~star r) +      |
    |     psi(m~star m) identically  ==>  a sector-defined         |
    |     extension REACHES psi.  So if psi = Q_Chuk on real       |
    |     windowed tests (same functional, same sign), T1+T2 make  |
    |     not-RH contradictory, i.e. prove RH.                     |
    +--------------------------------------------------------------+

T1 is kernel-verified; the classical Yoshida result is 33 years peer
reviewed; RH is open. Therefore the dictionary `psi = Q_Chuk` CANNOT
hold as stated — some convention differs: pole-term bookkeeping (Chuk's
Lemma 6.1 pole is the indefinite `+2c^2 - 2s^2`; our poleTerm pairs
`laplaceAt` at +-(1/2) and is not manifestly nonnegative on complex
tests), normalization of the symbol, or the sign of the geometric side
against their spectral identity — or T1's owners fail T2's admissibility
hypotheses at a point the abstract does not show (their Q is defined on
f; ours on F = f~star f; the "Q >= 0 is a finite fragment of RH, not
equivalent to it" remark in their section 1 is exactly where such a gap
would live). This record does NOT choose; choosing silently is the
forbidden move.

What it does price: the bridge's residual content is now a SINGLE
scalar question — the sign-and-factor dictionary on real windowed tests
— answerable by one double-evaluation cell (1407 candidate): take one
real test, compute psi of its autocorrelation (instrument exists) and
Q_Chuk from his section-2 explicit formula (elementary, fully explicit,
"no anonymous constants" by their declaration); compare. If they match
up to a positive factor with sign +, the red flag becomes genuinely
sharp (chain vs 1992 theorem: one of the register's own class hypotheses
must be re-examined against Yoshida's actual statement — read Yoshida,
not the summary). If they differ (sign -, factor, or pole convention),
the species closes as a pillar-B supplier per prereg 1405 section 7
wording and the chain and both certificates coexist by convention.
Either way no Lean funding is implied, rung 5 stays the wall
(B0b-iff-SourceRH, law 65 stands: all numbers here are MODEL), and
neither branch touches RH.

## 6. Kill scope honored

One model cell, two structural lemmas argued at formula level (not
written in Lean), one literature-abstract quote. It cannot falsify the
chain, cannot falsify Yoshida or Chuk, proves no gate, funds no Lean,
claims nothing about RH. Cumulative pillar-A evidence (107/107 negative)
is untouched and, if anything, sign-consistent with a +dictionary (both
sectors here are psi-positive exactly where pillar A asked for arch >
0).

## 7. Laws (promoted to AGENTS.md section 7)

- (F16) A PREREG BRANCH THAT CANNOT FIRE IS A DESIGN DEFECT. 1405's
  EXCLUDES/COVERS dichotomy was audited for gate satisfiability (the
  F12 recurrence-4 direction) but not for branch reachability: psi's
  even-real kernel made |P_x| >= 1e-3 unreachable by construction.
  Before locking a dichotomy, derive which branch the instrument's
  FORMULA already decides; a probe whose outcome is implied by the
  evaluator's type is decoration.
- (F17) TRANSCRIBE, NEVER RECONSTRUCT. A helper functional inside a
  probe is a line-by-line copy of the committed instrument (only call
  sites parameterized), because a reconstruction from the derivation
  paper silently drops terms the instrument committed later (the tail
  `reF0*log(tanh(Rg))` was known to this register - 1404 printed it as
  its own decomposition line). A parent-agreement gate (G0-class) at a
  tie class above the evaluator noise is mandatory for any
  reconstructed quantity; here it fired correctly four times over four
  invocations before the transcription fix.

## 8. Next steps

1. 1407 candidate (paper + one cell, no campaign): scalar dictionary
   double-evaluation of Q_Chuk vs register psi on one real windowed
   test, per section 5; prereg first (law 42).
2. Register closing pass for this wave (map entry, root project log,
   frontier card, laws) — done in the same commit series as this
   record.
3. If (and only if) the dictionary survives 1407 with sign +,
   re-read Yoshida's actual theorem statement (class hypotheses) before
   any further escalation; the collision then constrains the register's
   own chain class, which is the expensive and interesting direction.
