# 2724 — the 2722E `explicitSeed` identification is FALSE (the wired C4/C2 pins are rigorously falsified at the object they quantify; the repair object is Lean `poweredSeed`; scoped NO-GO on the identification, map-103 freeze unchanged)

Verdict: the 2722E §4.4 residual "explicitSeed identification for the
model seed" is resolved **FALSE**. The wired row-B pins quantify the
cardinal sums of `explicitSeed storedRadius2722F storedHRadius2722F`
whose transform is `v ↦ S(87.0719873427753 · v)` with `L(0) = S(0) = 3`,
while every certified constant on this lane (2720 `C4*` / `C2*` / `q*`,
re-anchored by 2722B/2722C/2722E) was computed for the model seed
`v ↦ S(v/2)^10` with `L(0) = 3^10 = 59049` — the same object as Lean
`poweredSeed` (`C1ExplicitSmoothSeed.lean`,
`poweredSeed_laplaceAt`). The two transforms share the base profile but
differ by enormous factors at the named cells; the wired
`hquarticPin` and `hquadraticPin` are **falsified** there with rigorous
two-sided accounting:

```text
+----------+-----------------------------+-----------------------------+
| cell     | certified model lane        | wired explicit object       |
+----------+-----------------------------+-----------------------------+
| F1 base  | upper  2.6855613504873       | lower  1.15071925488087e+95 |
|  t=0.25  | (= 4.4025596e-08 of pin)    | (= 1.886425e+87 of C4 pin)  |
+----------+-----------------------------+-----------------------------+
| F2 corr  | upper  667295.233779406     | lower  9.02545872883296e+69 |
| t=Im rho | (= 2.301018e-02 of pin)     | (= 3.1122271e+62 of C2 pin) |
+----------+-----------------------------+-----------------------------+
```

The explicit lower bounds are rigorous (single cell; the pins quantify
over all `t`, so one point refutes them) and exceed the wired pins
`wiredC4 = 61000000` / `wiredC2 = 29000000` by 87 and 62 orders. The
model lanes reproduce the 2722E-certified margins in the same run
(anchors bitwise, section 3). Probe
`scripts/screen_seed_object_2724.py` (60/60 checks green, WSL python),
artifact `results/2724_seed_object_screen.json`, verdict
`SEED-OBJECT-MISMATCH`. This is a scoped NO-GO on the IDENTIFICATION
(and hence on proving the three pins against the current wiring), not
on the pins as obligations: re-seeded at `poweredSeed` the same
certified constants apply to the actual pins' object. Record 2725 is
the re-seed brick.

## 0. Binding-route audit (start-of-round declaration)

- Consumer: `fourPointContradictionRowBStored2723` (the wired row-B
  contradiction, premises `{hNorm, hIm, hcontractPin, hquarticPin,
  hquadraticPin, hgate24, hright, htarget, hzero}`), reached from the
  2722D/2722C/2721C chain; downstream: selected detector `qw < 0` ->
  same-owner `qw >= 0` -> `SourceRH` -> Mathlib RH.
- Premise acted on: none removed this round. The screen decides the
  OBJECT the three cardinal pins and their certified constants live
  on — a routing fact that determines what "prove the pins" can mean.
- Premise shape facts (verbatim from
  `ConnesWeilRH/Dev/C1RowBStoredCapture2722F.lean`, verified by the
  probe's S1 parser):
  - `hcontractPin`: `64 <= |t|` threshold, `||cardinalSum ...|| <=
    13/50000000000000000`;
  - `hquarticPin`: NO `|t|` threshold, `(t/(2*pi))^4 *
    ||cardinalSum storedTargets2722F (explicitSeed r hr) (fun _ => 1)
    (sigma + t*I)|| <= 61000000`;
  - `hquadraticPin`: NO `|t|` threshold, `(t/(2*pi))^2 *
    ||cardinalSum storedNodes2722F (explicitSeed r hr) storedY2722F
    (sigma + t*I)|| <= 29000000`.
- Failure criterion / stop: a fully green probe run and a verdict; no
  premise is claimed discharged. Used: one probe script (four
  disclosed first-run defects), one green production run.

## 1. What was tested and how (no oscillatory quadrature)

Both seeds share the base profile `smooth_seed_raw ≡ T(2-|x|)`
(`baseBump` inner instance, plateau 1 on `[-1,1]`; same-run pointwise
tie `6.939e-18`). The base integral `S(w) = int e^{wx} T(2-|x|) dx` has
the exact decomposition used as the ONLY transform evaluator:

```text
S = P + e^{+2w} Eval(+w) + e^{-2w} Eval(-w)
P    = (e^w - e^{-w}) / w                    (plateau, exact)
Eval(u) = int_0^1 e^{-u e} ramp(e) de        (transition, one-sided)
```

For real `w` all three pieces are positive and the lower bound is the
sum of certified positive piece bounds (no cancellation). For complex
`w`, `|S| >= max-piece-lower - sum(other-piece-uppers)`; piece lowers
use the ladder `2^{-j}` monotone-window scan (`|int| >= cos(|Im u| d2) *
ramp(d1) * int_{d1}^{d2} e^{-Re(u) e} de`), piece uppers use the
elementary integrals, and the global upper is `min(3 e^{2|Re w|},
2 e^{2|Re w|}/|w|)` (IBP from `|rho'| = 2`, TV = 2). Cardinal term
bounds are `|c_z| x |nodeProduct ratio| x` the transform bound, and the
channel lower is the dominance gap (max term lower minus the other
terms' uppers), with the projection scan (`|Sigma| >= |Re(e^{-i phi}
Sigma)|`, exact-rational angles plus per-coefficient arg angles) applied
wherever all channel values are real. No quadrature is trusted for any
bound; `mp.quad` appears only in the machinery-validation lane below.

## 2. The falsifier cells

`F1` (base channel, `sigma = 0`, `t = 1/4`, weight
`2.5063433239e-06`, 8 active terms): explicit-object lower
`1.15071925488087e+95` against `wiredC4 = 61000000` — a factor
`1.886425e+87` over the pin; the model object in the same run reads
upper `2.6855613504873` (`4.4025596e-08` of the pin). Cross-object
ratio: `explicit lower / model upper = 4.284836966e+94`.

`F2` (correction channel, `sigma = 0`, `t = Im rho` = exact stored
literal `5917178117733711/281474976710656` =
`21.02203963877155601380764`, weight `11.1941201647`, 3 active terms):
explicit lower `9.02545872883296e+69` against `wiredC2 = 29000000` — a
factor `3.1122271e+62` over the pin; the model object reads upper
`667295.233779406` (`2.301018e-02` of the pin). Cross-object ratio
`1.352543563e+64`.

Mechanism, stated once: at shifted arguments `v = s - z` with
`Re v = +-0.55` (the row-B node columns), the explicit transform is
`S(87.0719873427753 v)`, of size `~ e^{2 r |Re v|}/|r v|` — versus the
model's `|S(v/2)|^10 ~ e^{10 |Re v|}` — and the normalizations differ
by `L(0) = 3` versus `59049`; the split is the exponential of the
radius, not a sign or a cancellation effect.

Robustness arms (all same-run, all rejected by the pin): `t = 0.1`
lower `3.286748e+85` of pin, `t = 0.5` `4.4620051e+88` of pin, the
`ramp(e) = T(2-|x|)^2` transition variant `1.9822738e+84` of pin;
ladder refinement ratio across the two deepest ladders `0.0128` (the
lower does not collapse under refinement); the `r = 1` control object
(explicit seed with the model's radius) does NOT fire (`0.0` of pin) —
the falsifier is specific to the stored radius.

## 3. Same-run anchors and machinery validation

- Certified side re-anchored bitwise in the same run: `C4*`, `C2*`,
  `q*` against the committed 2722C tie, `rel = 0.0`; margins
  `0.780% / 2.892% / 2.892%` of the pins; the 2722C tail extension
  `[600, 1e7]` re-anchors bitwise (`base_quartic <= 1.95e-68`,
  `corr_quadratic <= 2.40e-17`, `base_contract <= 4.53e-53` of the
  pins, mp-strictly decreasing). D-table controls green.
- Transform machinery validated against `mp.quad` truth INSIDE the
  rigorous bounds at four points (real `0.5`, `1`, `-3.5`, complex
  `-1.2 + 0.3i`): containment `lo <= |S_true| <= up` green at all
  four; the committed engine `make_powered_seed` agrees with
  `S_true(w)^10` at `s = 1, 2` to `2.48028e-12` / `2.66155e-12`
  (engine quadrature accuracy, inside the `1e-9` bar).
- The model-side numbers are RECOMPUTED, not quoted: the model lanes
  evaluate the same accounting at the model seed transform; the
  artifact carries both lanes per cell.

## 4. The `q` pin: not directly falsified here

`hcontractPin` quantifies `64 <= |t|`, where the monotone-window lower
bound does not reach (oscillation regime; the window `cos(|Im u| d2)`
factor decays). The premise set is already unsatisfiable through C4
and C2; the `q`-pin falsification is deferred and is NOT needed for
the verdict. Recorded in the artifact as `q_pin_status`.

## 5. Honesty line and routing

- `wired_hypotheses_removed = 0`. This screen refutes an
  identification and re-routes a brick; it discharges nothing.
- The pins are quantified `forall sigma in [0,1], forall t` (no
  threshold on C4/C2); one falsifying point per pin is a complete
  refutation of that pin AS WIRED (explicit seed). The pins as
  OBLIGATIONS survive at the corrected object.
- Routing: the re-seed brick (record 2725) instantiates the stored
  row-B carrier and pins at `poweredSeed` (2722D pattern), where the
  2720/2722C constants apply by construction; support radius moves
  `5*(2r+1) ~= 875.7` -> `~105` (the 2722D `radius = (3+1)*(2r+1) +
  (2r+1)` law at the model seed's `r = 10`). The remaining reopen
  obstruction is `{hgate24, three cardinal pins, htarget/hzero bricks,
  rho caps}` exactly as after 2723, minus the identification duty.
- No producer GO; no RH claim; `DEAD_ON_CURRENT_FAMILY` freeze
  unchanged — this is premise-blocker accounting inside the frozen
  family's contradiction audit.

## 6. Evidence

- Probe: `scripts/screen_seed_object_2724.py`
  (sha256 `d6c3885ba69c3fffd12c7d623860ea87db6162eeb4ff0d57cb44c801aad840cb`,
  bound in the artifact's provenance under `checker`; any edit
  invalidates the artifact).
- Artifact: `results/2724_seed_object_screen.json` (schema-free, 60/60
  checks, `verdict = SEED-OBJECT-MISMATCH`), provenance sha256 for
  `p3_certified_strip_constants_2720.py`, `fourpoint_powered_seed_1981.py`,
  `fourpoint_actual_owner_1980.py`, `results/2720_p3_certified_strip_constants.json`,
  `results/2722c_strip_transport_tie.json`,
  `C1RowBStoredCapture2722F.lean`, `C1FourPointRowBWired2721.lean`.
- Wired pin literals re-parsed from the committed capture:
  `wiredC4 = 61000000`, `wiredC2 = 29000000`,
  `wiredQ = 13/50000000000000000`, `storedRadius =
  6127146402364553/70368744177664`, `storedRhoIm =
  5917178117733711/281474976710656`.

## 7. Instrument findings (first-run defects, disclosed)

Three of the four were found by the probe's own guards; the fourth
crashed the run. All fixed before the green run:

- `find()` sentinel law: `text.find("}", i)` returns `-1` on a miss,
  which passes an `is None` filter and is then the `min()` candidate —
  the def-block extractor swallowed the rest of the module (12 literals
  instead of 3). Sanitize `-1` to absent before `min`.
- Bound-vs-value tie law: the engine tie compared my certified UPPER
  `S_up(0.5)^10` against the engine's true value and read
  `rel = 8482.2` — the ratio carried the exact 10th-power signature
  `(S_up/S_true)^10`, identifying bound-vs-value confusion rather than
  engine error. Ties must compare like with like; bound validity is
  gated separately by containment (`lo <= |truth| <= up`), now green
  at four points.
- Pin-shape reading before falsifier design: two of the three wired
  pins carry no `|t|` threshold (falsifiable at `t = 0.25`) while the
  third is thresholded at `64`; the screening plan followed the actual
  quantifier shapes, not a memory of them.
- Heterogeneous recording dicts: a key-suffix filter
  (`endswith("_model")`) admitted a string-valued ratio into a loop
  that indexes `rec["lower"]`; filter on `isinstance(rec, dict)`.