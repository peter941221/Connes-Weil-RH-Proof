# 003 — signed pointwise cancellation at a 2560-cell grid

Status: `VIABLE DIAGNOSTIC; LEAN CERTIFICATE NOT STARTED`.

This terminal subtask reopens the blocked 640-cell wide-rectangle route with
one named representation change and one named grid change:

```text
2338 coefficient boxes
    -> midpoint + coefficient-radius charge
    -> evaluate the 30-family complex sum at each node
    -> take the norm only after the family sum
    -> evaluate the weighted second derivative with the same cancellation
    -> composite-trapezoid remainder on 2560 cells
```

The owner is unchanged. The support radius, family modulation, coefficient
balls, strip endpoints, and downstream `baseNormUpper2343` consumer are
unchanged. The change is only the order in which cancellation is preserved and
the production grid size used to make the trapezoid remainder small enough.

## Diagnostic result

Record 2528 uses the midpoint of each 2338 exact coefficient box and charges
its Euclidean box radius separately. Node values use 100-decimal mpmath.
The curvature maximum is a 32-subnode binary64 diagnostic, so it is not yet a
certified supremum.

```text
+--------+----------+----------------------+----------------------+----------------------+
| cells  | sigma    | node sum             | curvature remainder  | total                |
+--------+----------+----------------------+----------------------+----------------------+
| 640    | -1/2     | 2.675979660886877    | 0.348130782506138    | 3.024110443393015    |
| 640    | +1/2     | 2.663843813683129    | 0.343649647406399    | 3.007493461089528    |
| 1280   | -1/2     | 2.688816070888075    | 0.081974600319111    | 2.770790671207186    |
| 1280   | +1/2     | 2.677064065852956    | 0.080916396067128    | 2.757980461920084    |
| 2560   | -1/2     | 2.686887376406491    | 0.019653549551288    | 2.706540925957779    |
| 2560   | +1/2     | 2.675211462945179    | 0.019387894566168    | 2.694599357511347    |
+--------+----------+----------------------+----------------------+----------------------+
```

The base endpoint pin is `2.7790943782`. At 2560 cells the diagnostic
headroom is approximately `0.07255` for sigma = -1/2 and `0.08449` for
sigma = +1/2. At 1280 cells the narrowest headroom is only about `0.00830`,
so 2560 is the recommended certificate grid.

## What this proves and what it does not prove

The diagnostic proves a routing decision: the previous obstruction came from
taking a wide rectangle norm before the 30-family cancellation and from using
too coarse a grid for the curvature remainder. The replacement representation
has enough numerical room to justify a Lean certificate campaign.

It does not prove the node table, the cellwise curvature supremum, the exact
midpoint-to-owner identity, the signed C3' margin, `SourceRH`, or RH. The
sampled curvature maximum must be replaced by a directed interval or analytic
cell enclosure before this terminal can be marked complete.

## Next certificate work

1. Define an exact-point owner rectangle whose center is the 30-family sum and
   whose radius is the sum of the 2338 coefficient-box error terms. Generate
   2561 outward node payloads for both endpoint signs.

2. Derive a cellwise second-derivative enclosure for the weighted owner sum.
   The enclosure must retain the complex family sum before taking the norm and
   must cover the whole cell, not only sampled subnodes.

3. Import the node and curvature payloads through segmented finite-sum Lean
   lemmas. Gate the resulting total against `baseNormUpper2343` with a
   nonzero rational margin, then re-run the owner-identity and selected-owner
   signed-budget checks.

Evidence: `docs/proofs/2528_signed_pointwise_cancellation.md`,
`scripts/routea_owner_signed_cancellation_2528.py`, and
`results/2528_signed_pointwise_cancellation_probe.json`.

Record 2529 freezes one implementation detail inside the new terminal:
per-family complex rectangles followed by rectangle summation are too loose
(the directed-MPFR node term is about 3.35, above the base pin). The active
representation remains the 2528 center complex sum plus separate scalar error
charges. This keeps the route viable diagnostically while preventing a
rectangle-dependency payload from entering Lean.

Record 2530 is the current payload-generation milestone. The active terminal
now has 2561 center-plus-error node rows per endpoint sign, exported as upward
binary64 rationals. The payload is ready for a segmented import design, but it
is not a Lean certificate until transcendental enclosures and the cellwise
curvature table are proved.

Record 2531 adds the first Lean support brick for the active terminal. It
formalizes center complex sum plus scalar error, with the allowed standard
axioms only. The 2530 numerical payload is still not imported; node
transcendental bounds and whole-cell curvature remain the next gates.

The 2530 node payload now includes exact rational coordinates and has a
structural checker. All 2561 nodes per sign and the rational trapezoid sums
pass; this is still import material rather than a Lean transcendental or
curvature certificate.

Record 2532 selects the next curvature architecture: signed midpoint F'' plus
coefficient error plus half-cell familywise F''' variation. The sampled 2560
cell price fits the base endpoint pin with margins about 0.0411 and 0.0530.
The 17-point third-derivative maximum is diagnostic only; the next gate is a
whole-cell directed enclosure.

Record 2533 continues this representation under the new terminal
`004_signed_grid_refinement_2533/`. The 2532 midpoint-second plus sampled
familywise-third architecture was replayed on 5120 and 10240 cells. The
refined grids retain positive endpoint-pin margin, but the sampled third
supremum is still not a certificate.
