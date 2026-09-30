# 2314 — OWNER-SUPPORT-FORMALIZED: the corrected owner's support radius at `stripRadius2303` is a Lean theorem for arbitrary coefficients and modulations, closing the first owner-bridge obligation

Records 2312/2313 consume a support-radius bound
`tsupport f subset [-stripRadius2303, stripRadius2303]` as the first half
of the owner bridge.  This record proves that bound for the actual
corrected width-a^2 owner family sum built by record 2276, in Lean,
with no hypothesis on the coefficient and modulation vectors:

    widthBump r x = exp (-30 / (1 - (x / r)^2)) on |x| < r,  0 outside
    ------------------------------------------------------------
    tsupport (correctedPhysical coefficients modulations)
        subset  [-a_4^2, a_4^2]  subset  [-stripRadius2303, stripRadius2303]

where `a_4 = 1441151880758559 / 562949953421312` is the unique largest
stored family width, so `a_4^2` is the exact support radius.

Verdict: **OWNER-SUPPORT-FORMALIZED** — the support chain and the exact
rational radius comparison are Lean theorems (standard axioms only), and
the pin check machine-verifies in exact rational arithmetic that the
Lean literals are bit-exact against the record 2275 owner capture, that
the exact radius equals the record 2276 `corrected_max_radius_exact`,
that its float64 render is bitwise the committed `owner.rmax`
`6.553600000000003` from the record 2303 envelope artifact, and that the
pin `6.5536001` dominates the exact radius with `1.1259e8`-ulp slack.
No owner bridge completion, no producer GO, no RH claim.

## The theorem chain (namespace `ConnesWeilRH.Dev`)

+---------------------------------------------+-----------------------------+
| declaration                                 | content                     |
+---------------------------------------------+-----------------------------+
| widthBump_eq_zero_of_not_lt                 | real bump vanishes off      |
| ofReal_widthBump_eq_zero_of_not_lt          | the radius (real, complex)  |
| widthBump_support_subset                    | bump support in [-r, r]     |
| familyTerm_support_subset                   | one term, c and theta free  |
| physicalFamilySum_support_subset            | sum support, radii <= R     |
| physicalFamilySum_tsupport_subset           | closed-support version      |
| storedWidth_nonneg, storedWidth_le_four     | width order facts           |
| storedWidth_sq_le_four                      | a_j^2 <= a_4^2              |
| storedWidth_four_sq_le_pin                  | a_4^2 <= 6.5536001 exact    |
| correctedPhysical_tsupport_subset_four      | owner support at a_4^2      |
| correctedPhysical_tsupport_subset_pin       | owner support at the pin    |
+---------------------------------------------+-----------------------------+

The new module `ConnesWeilRH/Dev/C1RouteAOwnerSupport.lean` imports the
record 2276 audit module and the arithmetic module and touches neither,
nor the 2312/2313 modules.

## The support argument

The bump is defined with an `if |position| < radius` guard, so off the
open radius interval it is literally `0` (`widthBump`, `if_neg`); the
coefficient and the unimodular modulation never change support
(`familyTerm_support_subset`).  For the finite sum it suffices that
every family radius is at most `R`: if `|x| < radii index` then
`x in Icc (-radii index) (radii index) subset Icc (-R) R`, so an
`x` outside `Icc (-R) R` forces every summand to vanish
(`Finset.sum_eq_zero`).  The closed support is then the closure of the
open support (`isClosed_Icc.closure_subset_iff`).

For the owner, the family radii are the squared stored widths
`storedWidth index ^ 2` (`correctedPhysical`), and the width block is
evaluated exactly: `fin_cases` over the 30 indices plus `norm_num` on
the definitional expansion of the vector literal, with the closed
right-hand side unfolded by `change` (the `norm_num [storedWidth]` pass
does not reduce the closed vector get on the right; the `change` to the
explicit literal mirrors the audit module's own idiom).  The final pin
comparison is exact rational arithmetic:

    a_4^2 = 2076918743413931858457251756481 / 316912650057057350374175801344
    pin   = 6.5536001 = 65536001 / 10^7
    slack = 2475880015520365766611298323 /
            24758800785707605497982484480000000   =  9.999999745341483e-08
          = 1.125899878170624e8 ulps of the pin (2^-50)

## Pins and the exact radius certificate

The pin check `scripts/routea_owner_support_lean_pin_2314.py` reads the
Lean sources and verifies against the committed artifacts in `Fraction`
arithmetic:

+---------------------------+--------------------------------+----------------+
| quantity                  | reference                      | value          |
+---------------------------+--------------------------------+----------------+
| 30 width literals         | 2275 capture families_hex      | bit-exact      |
| unique max index          | 2276 price artifact            | 4              |
| a_4 exact                 | 2276 legacy_max_radius_exact   | 1441151880758559/562949953421312 |
| a_4^2 exact               | 2276 corrected_max_radius...   | 2076918743413931858457251756481/316912650057057350374175801344 |
| float64(a_4^2)            | 2303 owner.rmax                | 6.553600000000003 (bitwise) |
| pin (Lean)                | design value                   | 6.5536001 = 65536001/10^7 |
| slack                     | pin - a_4^2                    | 9.999999745341483e-08 |
| decimal pin 6.5536        | would exclude the true radius  | rejected       |
+---------------------------+--------------------------------+----------------+

The capture comparison is bit-exact by construction:
`Fraction.from_float (float.fromhex ...)` converts each captured float64
to its exact rational value, and those equal the Lean literals; the
record 2276 price artifact's exact radius strings then pin `a_4^2`, and
the float64 render of `a_4^2` is bitwise equal to the rendered
`owner.rmax` measured by the record 2303 certification.  So the radius
the strip lane is certified against is exactly the owner's own support
radius, up to the recorded `1.1259e8`-ulp pin slack; and a decimal pin
at `6.5536` would have strictly excluded the owner (`a_4^2 > 6.5536`
exactly), validating the record 2312/2311 pin choice.

## Cross-record hash continuity

The record narrows the strip-lane input set without editing any earlier
file, and the check makes that mechanical:

+------------------------------------+--------------------------------------+
| file                               | continuity anchor                    |
+------------------------------------+--------------------------------------+
| C1RouteAItem5Arithmetic.lean       | md5 b3fb88c3...0376 (2312 pin)       |
| C1RouteAStripTransfer.lean         | md5 9bcd576a...f6c2 (2312 pin)       |
| C1RouteAGridSampling.lean          | md5 3581e512...7647 (2313 pin)       |
| C1RouteAOwnerScaleAudit.lean       | sha256 32fdbbc6...464b (2276 price  |
|                                    | artifact input hashes)               |
+------------------------------------+--------------------------------------+

## Controls

Controls run in the same pass and all pass:

+-----------------------------+--------------------------------------+
| control                     | observed                             |
+-----------------------------+--------------------------------------+
| synthetic parse             | fabricated 3-entry storedWidth block |
|                             | parsed back exactly (1/2, 3/4, 5/4)  |
| tie rejection               | raising family 6 to a_4 kills the    |
|                             | unique max, predicate rejects        |
| widened rejection           | a_4 + 1e-7 exceeds the pin           |
|                             | (slack ~1e-7), predicate rejects     |
| low pin rejection           | pin a_4^2 - 1e-8 below the exact     |
|                             | radius, predicate rejects            |
| widened render              | a_4 + 1e-7 changes the float64       |
|                             | render away from 6.553600000000003   |
| decimal strictness          | a_4^2 > 6.5536 exactly: a decimal    |
|                             | pin at 6.5536 excludes the owner     |
+-----------------------------+--------------------------------------+

The parse-guard-first-run rule from record 2313 fired as designed: run 1
of this check raised `ValueError` on the parenthesized storedWidth
literals (`(1441151880758559 / 562949953421312)`) instead of silently
mis-parsing; the parser now mirrors the record 2276 selftest's
normalization (`strip("()")` plus space removal, then `Fraction`).

## Lean acceptance (record 2314)

+------------------------------------+----------------------------------+
| artifact                           | reading                          |
+------------------------------------+----------------------------------+
| C1RouteAOwnerSupport.lean          | new module, 12 declarations      |
| C1RouteAOwnerSupportProbe.lean     | +12 #print axioms                |
+------------------------------------+----------------------------------+

Targeted build log `build_2314_step1.log`: `Build completed successfully
(3658 jobs)`, zero `error:` lines, zero `sorryAx`, zero warnings from
the two new files.  Root aggregate log `build_2314_root.log`: `Build
completed successfully (4329 jobs)`, 0 errors, and the replayed probe
output carries the standard axiom trio `[propext, Classical.choice,
Quot.sound]` for all 12 declarations.  The plan-count figures are
reported verbatim; the root count moved from 4245 (2313) to 4329 with
the added import closure, and no per-module census delta is claimed from
it.

## What this changes for the route

- The second strip-lane input named by record 2311 (support radius) now
  has a Lean proof for the actual owner family sum, uniform over the
  coefficient and modulation vectors — no identification of the captured
  coefficient vectors is needed for this half.
- The strip lane now reads: `CompactLogTest` packaging of the owner +
  101 node values at `stripGridMax2303` -> `FrozenStripHypothesis` ->
  producer.  Both residuals are owner-bridge obligations.
- The record 2303 radius render is confirmed to be the owner's exact
  support radius in float64, so the 2311/2312 pin chain is not merely
  conservative but bit-tight at the render level.

## Non-claims

- The `CompactLogTest` packaging of `correctedPhysical` (smooth bump,
  compact support as structure data) is not done: the 2313 consumer's
  hypotheses are about `b.test` for `b : CompactLogTest`, and the owner
  is not yet packaged as one.
- The 101 node values at `stripGridMax2303` are not proved; the grid
  maximum over the captured owner remains an artifact-grade input.
- The 2303 reduction (pavement, zero-count gate, coefficient inflation,
  node evaluation) remains artifact-grade.
- No producer GO, no gate sign change, no RH claim.

## Provenance

- Lean: `ConnesWeilRH/Dev/C1RouteAOwnerSupport.lean` (new, md5
  `6fc7303da399b90d79e2603a256d8b2b`) and its probe (md5
  `ac74c3b668f1b242094a944a4f7b2641`).
- Check: `scripts/routea_owner_support_lean_pin_2314.py` (md5
  `6af71e1b2fec50eb3532a6890e1aaaa7`) -> `results/2314_owner_support_lean_pin.json`
  (verdict PINNED-OWNER-SUPPORT-VERIFIED, failures empty).
- Upstream artifacts: `results/2275_gap_owner_audit.json` (capture),
  `results/2276_owner_scale_price.json` (exact radii, input hashes),
  `results/2303_corrected_strip_envelope.json` (owner.rmax), and the
  record 2312/2313 pin artifacts (hash continuity).

Next registered obligation: the value half of the owner bridge — package
`correctedPhysical` with the captured coefficient and modulation vectors
as a `CompactLogTest` (smoothness of the bump, compact support as
structure data, bitwise coefficient identification), then supply the 101
node values at `stripGridMax2303`; then the signed margin and the
non-tail charge; the selected-owner signed inequality remains the
summit.