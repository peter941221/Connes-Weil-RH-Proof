# Record 2721: analytic seed premise + ladder grid premise for the
2718 gate sign certificates

**Verdict: 2721 GREEN -- the observational seed premise of record 2718
(E_seed = 10 x observed GL-600-vs-GL-1200 spread) is RETIRED and replaced
by the fully computed-and-certified bound
B_seed_cert = D_float + 10 Lmax^9 B_tail = 3.5173e-06
(1.36x TIGHTER than the retired 4.7972e-06 assumption, with every leg
computed or certified: deterministic float difference 4.797e-07 over the
27512-point evaluation class, split-rule-bridged analytic GL-1200 tail
2.710e-13 at a* = 0.02, amplification 1.121e+07 at the tightened
Lmax = 4.7008).  The grid premise is NARROWED, not eliminated: the x10
inflation is gone and the premise is now a measured two-rung ladder
(0.02->0.01, 0.01->0.005) plus ONE named ratio-2 geometric continuation
premise at the pipeline float floor.  All four 2718 sign claims
re-certify GREEN at the new premises (worst margin ratio 1.92e+05); the
committed 2718 artifact reprices bitwise in the same run (0 drifted
fields, both rows).**

## Task card (bounded-progress gate)

```text
consumer    the four 2718 gate sign claims (C_negative, det_sign) at
            (14.134725141734693, N=4) and (21.022039638771556, N=5),
            each previously conditioned on the two observational
            premises E_seed and M_grid
owner       unchanged from 2718: the stored record-1980 trial owners
            (complete in-ball per record 2719); seed object = the
            GL-300 pipeline cardinal [int e^{(s/2)x} f(x) dx]^10
premise     E_seed: ELIMINATED (analytic replacement, this record);
            M_grid: NARROWED to ladder + one named premise
criterion   all four claims GREEN at the replaced premises, same-run
            bitwise reprice of the committed 2718 artifact
budget      one WSL run (28.0 s full, smoke pre-run green)
stop        verdict recorded (this record); 2721B = Lean absorption
```

## S1. The seed premise replacement

Old (2718): E_seed = 10 x max_sigma |L_600 - L_1200| (observed spread,
inflation factor assumed).

New (this record), evaluated over the full 2718 evaluation class
(27512 points; |Im s| <= 172.21 / 179.10 charged, |Re u| <= 1.0 -- the
mirror nodes are genuine, target Re in {0.45..1.5}):

```text
B_seed_cert = D_float + 10 * Lmax^9 * B_tail
            = 4.797184e-07 + 1.120856e+07 * 2.710078e-13
            = 3.517326e-06
```

+-----------------------+----------------------+----------------------+
| leg                   | value                | status               |
+-----------------------+----------------------+----------------------+
| D_float               | 4.797184e-07         | computed (bitwise    |
| (GL300 vs GL1200)     |                      | deterministic float  |
|                       |                      | diff, powered level) |
| B_tail (raw L1 level) | 2.710078e-13         | certified, split-    |
|                       |                      | rule bridge, a*=.02  |
| L1_sup = 2sinh(2r)/r  | 4.700805             | closed form, f <= 1  |
| (r = 0.5 remax = 0.5) |                      | pointwise           |
| Lmax = L1_sup + B_tail| 4.700805             | safe magnitude      |
| amplification 10 L^9  | 1.120856e+07         | powered difference  |
| B_seed_cert           | 3.517326e-06         | vs old 4.7972e-06    |
+-----------------------+----------------------+----------------------+

The crude |L1| <= 3 e^{remax} = 8.15 is replaced by the pointwise bound
f(x) in [0,1] => |L1(u)| <= int e^{0.5 Re(u) x} dx = 2 sinh(2r)/r =
4.7008 at r = 0.5 -- a 155x reduction in the amplification base.

## S2. Split-rule bridge for the analytic GL-1200 tail

The seed integrand f = T(x+2) T(2-x) (T the logistic transition) is NOT
complex-analytic on any domain containing [-2,2]: the logistic poles of
T solve the closed-form quadratic

  g(y) = 1/y - 1/(1-y) = i pi (2k+1)  <=>  c y^2 - (c+2) y + 1 = 0,
  c = i pi (2k+1),  y = [(c+2 +- sqrt((c+2)^2 - 4c)) / (2c)],

and ACCUMULATE at the interval endpoints: one root of each pair obeys
|Im y| = 1/(pi(2k+1)) -> 0 (binder pole k = 3199 at (2.47e-09,
4.97e-05)).  So no whole-interval Trefethen strip exists, and a panel
strip bound cannot be applied to the composite GL rule on [-2,2]
directly.  The certified tail is the record-2057 split-rule bridge:

  |GL_[-2,2](F) - I(F)| <= |GL - S| (computed) + |S - I| (per piece),

with S = fresh GL-600 sub-rules: closed-form middle [-1,1] (exact, no
rule error), two edge panels [a, 1-a] in y-space (Trefethen strip at
the measured pole distance d_min), and small-mass slabs charged by
measure at e^{-1/a} e^{remax}.

a-ladder over the evaluation class (per-leg values at each a):

+--------+----------+-----------+-----------+-----------+------------+
| a      | d_split  | round_al  | mid_strip | 2xpanel   | B_tail     |
+--------+----------+-----------+-----------+-----------+------------+
| 0.06   | 1.63e-09 | 4.69e-14  | 0         | 6.9e-69   | 1.65e-06   |
| 0.04   | 3.98e-13 | 4.69e-14  | 0         | 2.3e-43   | 3.90e-10   |
| 0.03   | 2.25e-13 | 4.69e-14  | 0         | 2.2e-31   | 3.65e-13   |
| 0.02 * | 2.24e-13 | 4.69e-14  | 0         | 7.6e-20   | 2.71e-13 * |
+--------+----------+-----------+-----------+-----------+------------+

The binding leg is the COMPUTED split difference d_split (float), not
the strip: d_min(panel [a,1-a]) ~ a for every k (poles hug the corners),
so the strip collapses geometrically as a -> 0 while d_split sits at
its own float floor.  a* = 0.02.  (The 2721A recon's planning-grade
2.2e-07 prediction applied the panel strip directly to the composite
rule; the bridge construction is the sound version and honestly reads
3.5e-06 -- still tighter than the retired premise.)

## S3. The grid premise: narrowed, one named premise left

Old (2718): M_grid = 10 x observed 0.02-vs-0.01 movement per channel.

New: measured two-rung ladder + named tail:

```text
M_ch = m(0.02,0.01) + 2 * m(0.01,0.005)     [M_det likewise]
named premise: e(0.005) <= 1.0 x m(0.01,0.005)   (ratio-2 continuation)
```

+---------+----------------------+----------------------+
| channel | m(0.02,0.01)         | m(0.01,0.005)        |
+---------+----------------------+----------------------+
| arch    | 8.574803e-06         | 1.491571e-09         |
| pr      | 1.318992e-01         | 7.078052e-06         |
| kp      | 7.155716e+01         | 1.971436e-02         |
+---------+----------------------+----------------------+

Rung ratios 5749 / 18635 / 3630 (>> the h^2-law value 4) mean the 0.005
rung sits at or near the pipeline float floor -- the geometric regime
(nearest digamma pole |Im xi| ~ 0.0796, h << pi d).  The named premise
is charged AT that scale with the measured collapse as its evidence;
adding finer grids cannot certify it (the oscillatory prime channel is
in the record-2278/2279 cancellation-floor class: an EM absolute-mass
route is vacuous there).  Net effect: M_ch_new ~ M_ch_old / 10 on every
channel and on det (9.745e+07 vs 9.744e+08).

## S4. Claims re-certified

+--------+-----------+----------+-----------+----------+-------------+
| row    | claim     | slack_old| slack_new | Ecrit_new| margin_new  |
+--------+-----------+----------+-----------+----------+-------------+
| A n=4  | C_neg     | 1.4522e05| 1.4522e05 | 19.2995  | 5.48e+06    |
| A n=4  | det_sign  | 1.2191e16| 1.2191e16 | 0.82852  | 2.35e+05    |
| B n=5  | C_neg     | 8.4911e03| 8.4911e03 | 2.9541   | 8.38e+05    |
| B n=5  | det_sign  | 6.0844e14| 6.0845e14 | 0.67598  | 1.92e+05    |
+--------+-----------+----------+-----------+----------+-------------+

margin_new = E_L_critical_new / B_seed_cert; every claim GREEN_new with
slack_new >= slack_old (the new premises are cheaper, so the slack
survives everywhere).  Branch corners re-derived at the new allowances
(row A corner window 1381.5316..1381.5360, branch "rays" robust).

## S5. Anchors and determinism

- a1: three-grid rebuild (0.02 / 0.01 / 0.005) reproduces the committed
  2718 rows BITWISE at the 0.02/0.01 tags -- 0 mismatched fields on
  both rows; W = W_direct asserted on all three grids.
- a3: seed0 (GL-300 powered transform at s = 0) bitwise; a4: gap to the
  exact 3^10 = 59049 is 1.412e-07 (quadrature error, matches the
  committed float).
- a5: SAME-RUN reprice of the committed 2718 artifact: 0 drifted fields
  both rows (E_seed_obs, premise, grid movements, per-claim value /
  nonseed allowance / A_seed / total).
- a6 (in-run assert): the raw-L1 mirror make_raw_l1(1200) (factory node
  / weight / chunk / sum order verbatim, power removed) is BITWISE equal
  to the factory transform's pre-power value at the probe points.
- Environment: WSL python3 (same class as the 2718/2720 artifacts);
  smoke pre-run green; full run 28.0 s.  Artifacts:
  results/2721_seed_premise_rig.json (+ _smoke); the recon artifact
  results/2721A_seed_premise_recon.json (1991cb95) stays as the
  planning-grade GO evidence.

## S6. What is and is not certified

Certified at model grade (pipeline-as-code on stored binary64 owners):

- the four 2718 gate sign claims at the REPLACED premises: seed premise
  analytic (computed + certified), grid premise narrowed to one named
  ratio-2 continuation premise;
- the split-rule tail bound B_tail = 2.71e-13 (a* = 0.02) with the
  closed-form pole geometry;
- bitwise identity of the whole pipeline with record 2718 on the
  committed grids.

NOT certified here (unchanged from 2718/2719/2720):

- the named grid premise e(0.005) <= m(0.01,0.005) remains a PREMISE
  (float-floor scale, cancellation-floor class);
- Lean absorption of any of this (2721B: pin 2720's C4*/C2*/q* and the
  2718/2721 corner as explicit hypotheses, proxy-tie per record 2657);
- P4 shell identification; any map-103 four-point reopening (route
  authority unchanged -- the freeze stands; reopening requires Peter);
- producer GO, SourceRH, any RH claim.

## S7. Instrument notes (record-local laws)

- Composite-rule strip bridging: a Trefethen panel bound is valid for
  the rule ON the panel.  A composite GL rule over [-2,2] whose
  integrand has endpoint-accumulating poles must be bridged
  (|GL - S| computed + per-piece analytic), never bounded by a strip on
  the whole interval -- no such strip exists (pole |Im| = 1/(pi(2k+1))
  -> 0 at BOTH endpoints).
- Pole-corner asymptotics: d_min(panel [a, 1-a]) ~ a for every k, so
  the strip term collapses geometrically in a and the binding leg of
  the bridge is the computed float split difference -- ladder over a
  and take the min rather than guessing one a.
- Float-floor rung: consecutive-grid rung ratios >> the h^2-law value
  mean the finer rung measures the pipeline float floor; charge the
  named tail premise at that scale (with the measured collapse as
  evidence) instead of adding grids -- the oscillatory-channel relative
  of the record-2046/2050 anchor-floor law.
- Pointwise-f <= 1 tightening of the amplification base: 2 sinh(2r)/r
  beats measure x e^{remax} by 155x here; check the pointwise envelope
  before charging a power-difference amplification.

## S8. Outcome addendum: 2721B Lean absorption (this commit)

Wired contradiction LANDED.
`ConnesWeilRH/Dev/C1FourPointRowBWired2721.lean` states
`fourPointContradictionRowBWired2721` (base correction : CompactLogTest)
(rho : sourceNontrivialZeroSet) ... : False, composing
`orbitWindowSemiLocalGate_iff` + `annihilator_span_gate_eq_parabola` ->
`annihilatorDetectorSpanVector_qw_nonneg_of_gate` against
`qw_neg_of_spectralHeightShellPrefix_and_coefficient_scaled_tail` ->
`false_of_qw_nonneg_and_neg`, with every numeric premise an explicit
hypothesis at the pinned row-B constants (proxy-tie 2657 pattern):
q = 26/10^17 (over the 2720 render 2.5248e-16, slack 1.34e14 ulp),
C4 = 61000000, C2 = 29000000, rhoNorm = 22, rhoIm = 421/20,
mult = 515 (over the 2354 cap 2573/20 = 128.65), lambda = 24 (branch
'all', above the 2718 gate floor 15.86). The two scalar acceptance
chains re-derive in exact Fractions: hsmall 2.305e-37 < 1, eta
13905/16384 = 0.8487 < 1, height chain 2 * 421/20 = 42.1 < 64.

Acceptance: `scripts/check_four_point_wired_2721.py` 35/35 PASS
(`results/2721b_wired_check.json` -- exact-rational pin binding to the
2720/2718/2354 renders, def-literal and consumer-name transcription
guards, mutation controls); Linux-native audit build green (3815 jobs,
zero `error:` lines, zero `uses sorry`); the three declarations
`wiredHsmallTailRowB2721`, `wiredEtaBudgetRowB2721`,
`fourPointContradictionRowBWired2721` each print exactly
[propext, Classical.choice, Quot.sound] (`results/2721b_axiom_census.json`);
Windows/WSL source md5 parity checked both modules.
`results/2721_seed_premise_rig_smoke.json` is kept as the S-rig smoke
evidence (2718 fork-smoke precedent).

Incident (record-local law): the first checker run FAILed on
`mutation_mult_514_fires` -- the control asserted that a pin of 514
would violate the multiplicity cap, but the cap is 128.65 and the live
pin 515: the rejection case was arithmetically impossible, so the
control could never fire. Fixed to pin 128 (strictly below 2573/20)
before any verdict was read; the FAIL artifact on disk was stale by 8
seconds (script mtime newer than artifact) -- caught only by the
standing re-run-on-fix law (trust the artifact mtime/content, never the
memory of the final run). Second instance of the control-premise family
(AGENTS 2ah "control hurdle copied from intuition is a bug").
Generalized check: every negative control's own asserted inequality must
be verified feasible (the perturbed value must actually fail the
predicate) before the control counts as coverage.

Residual obligations -- now the formal reopen-motion list, i.e. the
named hypotheses of one Lean statement rather than prose:
hNorm/hIm (2719-grade enclosing intervals into Lean pins),
hmult (instantiate the 2354 cap theorem at 515 -- check whether its own
hypotheses discharge it outright, the cheapest next strike),
hvanish/hsupport (g-construction obligations for
`(selectedOwner base correction 3).sourceTest`),
hcontract/hquartic/hquadratic (Lean re-proof of the three 2720 strip
envelopes ON the actual owner -- numeric enclosures are not Lean
theorems, and the 2ay slab/interpolation guard must be discharged from
storedWidth data, not stored floats; the 2720 instrument's fine cells
hugging every active height and the zero-fail coverage through h = 200
say the obstruction does not fire on this owner, at artifact grade),
hgate24 (owner-grade P5 sign certificate at lambda = 24 -- model grade
done with 5-7 orders of margin, owner grade open),
hprefix (P2 shell-prefix on the actual span vector).

Status unchanged by this absorption: the wired theorem is interface
packaging under the core-progress gate, not closure. No reopening, no
route ruling, no producer GO, no RH claim. Next strike per this list:
hmult probe, then the strip-envelope absorption lane (scope it under
the bounded-progress rule before any batch).
