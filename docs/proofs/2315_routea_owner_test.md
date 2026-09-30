# 2315 — OWNER-TEST-PACKAGED: the corrected owner is a `CompactLogTest` for arbitrary coefficients and modulations via the flat-junction identity, closing the structural half of the owner bridge

Records 2312/2313 consume their strip-lane inputs as `CompactLogTest`s
(`test : SchwartzMap ℝ ℂ` plus `HasCompactSupport`), while record 2314's
owner support theorems live on the raw function
`correctedPhysical : ℝ → ℂ`.  This record closes that structural gap:

    widthBump radius x = expNegInvGlue ((1 - (x / radius)^2) / 30)
      (0 < radius)
    ------------------------------------------------------------
    ContDiff ℝ ∞ (correctedPhysical coefficients modulations)
    HasCompactSupport (correctedPhysical coefficients modulations)
    correctedPhysicalCompactLogTest coefficients modulations
      : CompactLogTest        (test = the owner, support at the pin)

Verdict: **OWNER-TEST-PACKAGED** — smoothness is inherited from
Mathlib's flat-junction glue `expNegInvGlue` (its one-sided junction is
`C^∞`), compact support from the record 2314 pin interval, and the
packaged test's support bound has the exact hypothesis shape of the
record 2313 node consumer.  The coefficient and modulation vectors stay
free.  The only remaining owner-bridge input is the 101 node values at
`stripGridMax2303`.  No producer GO, no gate sign change, no RH claim.

## The theorem chain (namespace `ConnesWeilRH.Dev`)

+--------------------------------------------------+---------------------------+
| declaration                                      | content                   |
+--------------------------------------------------+---------------------------+
| widthBump_eq_expNegInvGlue                       | bump = flat-junction glue |
| widthBump_contDiff                               | bump is C^∞ (0 < radius)  |
| familyTerm_contDiff                              | one term is C^∞           |
| physicalFamilySum_contDiff                       | family sum is C^∞         |
| physicalFamilySum_hasCompactSupport              | sum compact support       |
| storedWidth_pos                                  | widths positive           |
| correctedPhysical_contDiff                       | owner is C^∞              |
| correctedPhysical_hasCompactSupport              | owner compact support     |
| correctedPhysicalCompactLogTest                  | the packaged test         |
| correctedPhysicalCompactLogTest_toFun            | test = the owner          |
| correctedPhysicalCompactLogTest_tsupport_subset  | support at the pin        |
| correctedPhysicalCompactLogTest_compactSupport   | compact support           |
+--------------------------------------------------+---------------------------+

The new module `ConnesWeilRH/Dev/C1RouteAOwnerTest.lean` imports the
record 2314 module, the `CompactLogTest` definition module, and
Mathlib's `SmoothTransition`; it edits none of them.

## The flat-junction identity

`widthBump radius x = exp (-30 / (1 - (x / radius)^2))` on
`|x| < radius` and `0` outside; `expNegInvGlue t = exp (-t⁻¹)` on
`t > 0` and `0` on `t ≤ 0`.  With `u = 1 - (x / radius)^2` and
`0 < radius`:

* `|x| < radius` ⟺ `u > 0` ⟺ `u / 30 > 0` — the two guards agree
  exactly (`abs_div` + `div_lt_one` + `sq_abs` on one side,
  `one_le_div` + `one_le_pow₀` on the other);
* on the common support the arguments agree:
  `-30 / u = -((u / 30)⁻¹)` (`inv_div`, `neg_div`);
* at `|x| = radius` both sides are literally `0`.

Smoothness then does not need any boundary-flatness argument of our
own: `expNegInvGlue.contDiff` (Mathlib) composed with the smooth
rational map gives `widthBump_contDiff`; the family terms are
constant × coerced bump × unimodular phase
(`Complex.ofRealCLM` + `Complex.contDiff_exp`), the finite sum is
`ContDiff.sum`, and compact support is
`IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport _)` over
the record 2314 bound `tsupport ⊆ [-stripRadius2303, stripRadius2303]`.

## Pins and checks

The pin check `scripts/routea_owner_test_lean_pin_2315.py` verifies:

+-------------------------------+------------------------------------------+
| check                         | reading                                  |
+-------------------------------+------------------------------------------+
| 2314 module byte-frozen       | live md5 6fc7303d… == 2314 artifact      |
| CompactLogTest shape          | `test : TestFunction` +                  |
|                               | `compactSupport : HasCompactSupport      |
|                               | test` (md5 352c40fb… recorded)           |
| base-function guard           | `expNegInvGlue` present,                 |
|                               | `Real.smoothTransition` absent           |
| sampled identity witness      | dps 70 at the exact radius a_4^2;        |
|                               | 9 interior + 8 boundary/outside points;  |
|                               | max branch difference 2.778e-83          |
|                               | (< 1e-50); exact zeros at                 |
|                               | |x| >= radius; strict positivity inside  |
| dip at zero                   | e^-30 = 9.3576229688401746049e-14        |
+-------------------------------+------------------------------------------+

The witness is a sampled sanity check (the Lean theorem is the proof);
its predicates are exercised negatively: an argument offset `-1/50`
changes the sampled values by up to 9.357623e-14 and a halved radius by
4.1473394e-14, both far above the 1e-20 rejection bar.  The sample
split counts are pinned exactly (9/8) so a silent sample-list edit
fails the check.

## Lean acceptance (record 2315)

+---------------------------------+-------------------------------------+
| artifact                        | reading                             |
+---------------------------------+-------------------------------------+
| C1RouteAOwnerTest.lean          | new module, 12 declarations         |
| C1RouteAOwnerTestProbe.lean     | +12 #print axioms                   |
+---------------------------------+-------------------------------------+

Targeted build log `build_2315_step1.log`: `Build completed successfully
(3659 jobs)`, zero `error:` lines, zero `sorryAx`, zero warnings from
the two new files.  Root aggregate log `build_2315_root.log`: `Build
completed successfully (4330 jobs)`, 0 errors, the replayed probe
output carries the standard axiom trio `[propext, Classical.choice,
Quot.sound]` for all 12 declarations.  The plan-count figures are
reported verbatim (3658 → 3659 and 4329 → 4330 versus record 2314,
consistent with one added module; no per-module census delta is
claimed).

## What this changes for the route

- The strip lane's inputs are now both owner-shaped: the record 2313
  consumer takes `b c : CompactLogTest` plus node values, and for any
  coefficient/modulation vectors the owner supplies the test and the
  support bound (`correctedPhysicalCompactLogTest` +
  `correctedPhysicalCompactLogTest_tsupport_subset`).
- The owner bridge's structural half is closed.  The residual is
  exactly the 101 node values at `stripGridMax2303`, which is where the
  captured coefficient and modulation vectors enter bitwise.

## Non-claims

- The 101 node values at `stripGridMax2303` are not proved; the grid
  maximum over the captured owner remains an artifact-grade input.
- The 2303 reduction (pavement, zero-count gate, coefficient inflation,
  node evaluation) remains artifact-grade.
- No producer GO, no gate sign change, no RH claim.

## Provenance

- Lean: `ConnesWeilRH/Dev/C1RouteAOwnerTest.lean` (new, md5
  `b88ce3efc3132d0ce7ac76a6cea4920e`) and its probe (md5
  `00869162fddb53a9eff6206520605e62`).
- Check: `scripts/routea_owner_test_lean_pin_2315.py` (md5
  `f747974f4c438d95045be9ac2878aab4`) -> `results/2315_owner_test_lean_pin.json`
  (verdict PINNED-OWNER-TEST-VERIFIED, failures empty).
- Upstream artifacts: `results/2276_owner_scale_price.json` (exact
  radius), `results/2314_owner_support_lean_pin.json` (hash continuity
  and the tsupport bound the packaging consumes).

Next registered obligation: the 101 node values at `stripGridMax2303`
over the captured coefficient and modulation vectors (the value half of
the owner bridge, artifact-grade), then the instantiation of
`frozenStripHypothesis_of_certified_nodes` with the packaged owner;
then the signed margin and the non-tail charge; the selected-owner
signed inequality remains the summit.