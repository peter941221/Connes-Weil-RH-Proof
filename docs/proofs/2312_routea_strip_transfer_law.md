# 2312 — STRIP-TRANSFER-FORMALIZED: the record 2303 transfer law lands in Lean in exponential form, and the grid consumer wires it into the certified envelope

Record 2303 certified the centered-strip envelope on the corrected
width-a^2 owner as a grid maximum times a continuum-transfer factor
`e^(2 rmax h)`; the transfer half rested on the registered log-derivative
law `|d/dsigma log N| <= 2 rmax` for the strip min-product `N`, and record
2311's non-claims listed it as "only a registered derivation".  This
record makes the transfer half a Lean theorem.  The formalization is in
the exponential form — the form the envelope actually consumes:

    expWeightedIntegral_le_transfer_of_neighbor:
      g continuous, g >= 0, support g in [-R, R], |sigma - sigma_0| <= h
      ----------------------------------------------------------------
      integral e^(sigma x) g <= e^(R h) * integral e^(sigma_0 x) g

    min_stripProduct_le_transfer_of_neighbor:
      N sigma <= e^(2 R h) * N sigma_0     (four per-factor transfers)

    frozenStripHypothesis_of_certified_grid:
      hgrid (nearest certified node within h, node value <= stripGridMax2303)
      + tsupport bounds at R + the 2312 exponent pin
      ----------------------------------------------------------------
      the 2311 certified envelope, hence FrozenStripHypothesis

Verdict: **STRIP-TRANSFER-FORMALIZED** — the transfer inequality is
machine-checked (standard axioms only), the pinned radius / half-step /
transfer-exponent arithmetic is machine-checked by `Real.exp_bound'` plus
`norm_num` and cross-checked against the committed artifact in exact
rational arithmetic, and the residual trust is exactly the grid-existence
arithmetic, the grid maximum over the captured owner (artifact), and the
support-radius bound (owner bridge).  No Lean formalization of the record
2303 reduction itself, no grid-sampling proof, no owner bridge, no
producer GO, no RH claim.

## Why the exponential form

The registered law is an infinitesimal statement about `d/dsigma log N`.
The envelope only ever consumes the integrated consequence
`N sigma <= N sigma_0 * e^(2 rmax h)`, and that consequence has a direct
pointwise proof: on the support `|x| <= R`, so
`e^(sigma x) <= e^(sigma_0 x + R h)` and the inequality integrates
against `g >= 0`.  The exponential form is what is proved here because it
(a) avoids differentiating under the integral sign entirely, (b) is
per-point (not just infinitesimal), and (c) is exactly the hypothesis
shape the 2311 consumer takes.  The derivative form itself is not proved;
see Non-claims.

## The theorem chain (namespace `ConnesWeilRH.Dev`)

+-------------------------------------+----------------------------------+
| declaration                         | content                          |
+-------------------------------------+----------------------------------+
| expWeightedIntegral_le_transfer_    | core exponential transfer        |
|   of_neighbor                       | (integral monotonicity +         |
|                                     |  compact-support integrability)  |
| stripNorm_le_transfer_of_neighbor   | strip L1 weight, g = ||f||       |
| stripSecondNorm_le_transfer_        | second-derivative weight,        |
|   of_neighbor                       | g = ||deriv (deriv f)||          |
| min_stripProduct_le_transfer_       | min-product transfer at radius R |
|   of_neighbor                       | (four factor transfers +         |
|                                     |  min_mul_of_nonneg)              |
| frozenStripHypothesis_of_           | 2303 grid consumer -> 2311       |
|   certified_grid                    | certified envelope               |
| frozenStripHypothesis_of_           | corner at the pinned radius and  |
|   certified_grid_rmax               | half-step                        |
+-------------------------------------+----------------------------------+

Continuity of the tests and of their literal second derivatives is read
off the Schwartz structure with the established repo pattern
(`(f.test.smooth ⊤).continuous`, `ContDiff.deriv'` twice); the support of
`deriv (deriv f)` is fed through `support_deriv_subset` and
`tsupport_deriv_subset` from `tsupport f`.

The pins live in `C1RouteAItem5Arithmetic` (record 2312 additions):

    stripRadius2303 : Real := 6.5536001    (sound upper of owner.rmax)
    stripHalfStep2303 : Real := 0.005      (exact grid.half_step)
    real_exp_transfer_le_stripTransfer2303:
      Real.exp (2 * stripRadius2303 * stripHalfStep2303) <= stripTransfer2303

## Pin soundness and tightness (exact rational check)

The pin check `scripts/routea_strip_transfer_lean_pin_2312.py` reads the
Lean source, extracts the literals, and verifies in `Fraction`
arithmetic against `results/2303_corrected_strip_envelope.json`:

+-------------------+------------------------------+------------+---------+
| pin               | reference                    | slack      | ulp     |
+-------------------+------------------------------+------------+---------+
| stripRadius2303   | owner.rmax render            | 1e-7       | 1.1e8   |
|                   | 6.553600000000003            |            |         |
| stripHalfStep2303 | grid.half_step 0.005         | exact      | n/a     |
|                   | (= 1/(2*(101-1)) = 1/200)    |            |         |
| exp bound (n = 6) | e^(2*6.5536001*0.005)        | 2.3971e-8  | n/a     |
|                   | = e^0.065536001              |            |         |
+-------------------+------------------------------+------------+---------+

Rationale for the radius pin.  The committed `owner.rmax` render is
`6.553600000000003`, about 3.4 ulp above the exact window radius 6.5536,
so a pin at 6.5536 would strictly exclude the artifact's own radius —
the pin law for this lane demands Lean-side constants be sound uppers of
the render.  The pin 6.5536001 sits 1e-7 above the render (1.13e8 ulp,
far above the 100-ulp floor) and an order of magnitude inside the
failure frontier: the Taylor margin `S < 1.0677312` survives radius
slack up to ~2.25e-6, and the control at +5e-6 radius is rejected.

The order-6 Taylor bound `S(x) = sum_{m<6} x^m/m! + x^6*7/(720*6)` at the
pinned exponent `x = 0.065536001 = 65536001/1000000000`:

+--------------------------------+--------------------------------------+
| quantity                       | value                                |
+--------------------------------+--------------------------------------+
| S (exact rational)             | 1.0677311760289467                   |
| pin stripTransfer2303          | 1.0677312                            |
| margin S below pin             | 2.3971053178564005e-8                |
| S overshoot over e^x (dps 60)  | 1.7301049481943664e-11               |
| render dust control            | S(2*rmax_render*0.005) < pin (ok)    |
+--------------------------------+--------------------------------------+

Render consistency: `e^(2 * owner.rmax * grid.half_step)` at dps 60 is
`1.0677311749439145` against the committed `grid.transfer` render
`1.0677311749439153` (relative 8.3e-16), and the pinned transfer
dominates the render.  Every transcription guard passes (three def
literals, the theorem statement, the `Real.exp_bound'` order-6 call, the
`norm_num` list, the six core/consumer/corner declarations, the support
chain); controls: synthetic parse, radius-below-render rejection, +5e-6
radius overshoot rejection.  Verdict PINNED-TRANSFER-VERIFIED, failures
empty.

## Lean acceptance (record 2312)

+--------------------------------+--------------------------------------+
| artifact                       | reading                              |
+--------------------------------+--------------------------------------+
| C1RouteAItem5Arithmetic.lean   | +2 defs, +1 exp-bound theorem        |
| C1RouteAStripTransfer.lean     | new module, 6 declarations           |
| C1RouteAStripTransferProbe     | +6 #print axioms                     |
| C1RouteAItem5ArithmeticProbe   | +1 #print axioms                     |
+--------------------------------+--------------------------------------+

Targeted build log `build_2312_step1.log`: `Build completed successfully
(3573 jobs)`, zero `error:` lines, zero `sorryAx`, zero `declaration uses
'sorry'`, zero warnings from the touched files; post-cleanup confirmation
`build_2312_step2.log` (same acceptance; the only rebuilds are the
transfer module and its probe, the rest of the counted jobs are cached
replays).  All seven new declarations print the standard axiom trio
`[propext, Classical.choice, Quot.sound]`.

Two hygiene fixes were made between step1 and step2: the `ring` calls
after `congr 1` in the min-product reassociation were rewritten to the
suggested `ring_nf` (the subgoal is an equality of `Real.exp` arguments,
where `ring` sees the two applications as distinct atoms and only its
fallback closes the goal), and the module file gained its final newline
(the whitespace linter).

Root aggregate log `build_2312_root.log` (library plus the two changed
probes explicit): `Build completed successfully (4245 jobs)` — the 2311
root count 4244 plus the new module — 0 errors, 0 sorryAx, 0 warnings
from the touched files, and the replayed probe output carries the axiom
trio for all seven declarations.

## What this changes for the route

- 2311's non-claim narrows again: the envelope's transfer half is no
  longer "a registered derivation" — the inequality
  `N sigma <= e^(2 R h) N sigma_0` that the transfer factor feeds is a
  Lean theorem, and the pinned exponentiation
  `e^(2 * 6.5536001 * 0.005) <= 1.0677312` is machine-checked from
  Mathlib's Taylor bound (remainder ~1.7e-11 against a 2.4e-8 margin).
- The strip lane now reads: grid sampling (every centered sigma within
  the half-step of a node) + node values (artifact, as in 2311) + support
  radius (owner bridge) -> `henvelope` -> `FrozenStripHypothesis` ->
  producer.  The grid consumer is the new interface; the 2311 envelope
  conversion remains for callers that already have `henvelope`.
- The radius pin 6.5536001 deliberately leaves 1e-7 of room above the
  committed render so the owner bridge can prove any support radius at
  most the recorded `owner.rmax` without re-pinning.

## Non-claims

- The derivative form `|d/dsigma log N| <= 2 rmax` is not formalized;
  what is formalized is the integrated exponential inequality the
  envelope consumes, which is logically stronger per point.
- The grid-existence arithmetic is a named hypothesis (`hgrid`), not a
  Lean theorem; the record 2303 reduction (pavement, zero-count gate,
  coefficient inflation, grid, node values) remains artifact-grade.
- The owner bridge is not done: nothing here identifies the captured
  owner with the selected Lean test functions or proves the support
  radius bound; the corner theorem shows what the bridge must supply.
- The signed margin, the non-tail charge, and the certified gap split
  remain open; no producer GO, no gate sign change, no RH claim.

## Provenance

- Lean: `ConnesWeilRH/Dev/C1RouteAStripTransfer.lean` (new),
  `ConnesWeilRH/Dev/C1RouteAItem5Arithmetic.lean` and their probes.
- Check: `scripts/routea_strip_transfer_lean_pin_2312.py` ->
  `results/2312_strip_transfer_lean_pin.json` (verdict
  PINNED-TRANSFER-VERIFIED; controls: synthetic parse, negative
  shifted-pin rejection, radius overshoot rejection).
- Upstream certificate: `results/2303_corrected_strip_envelope.json`
  (record 2303, CORRECTED-STRIP-COVERED).

Next registered obligation: the grid-sampling lemma (Lean-side
nearest-node arithmetic for the 101-node sigma grid), then the owner
bridge (support radius and the grid maximum over the captured owner),
the signed margin, and the non-tail charge; the selected-owner signed
inequality remains the summit.