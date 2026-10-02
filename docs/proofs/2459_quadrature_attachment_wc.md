# 2459 - W-C attachment layer + sum-panel door + support glue landed in Lean

Date: 2026-10-02.

Verdict in one line: all three W-C-family seams of the quadrature
import lane are now Lean theorems on the standard three axioms - the
bump/phase box shapes (monotonicity + 1-Lipschitz + midpoint boxes),
the family and 30-family sum panel doors over the 2454 hull algebra,
the trapezoid-upper-bound attachment corollary of 2457, and the
support glue from full-line stripNorm to the interval integral - so
the discharge chain stripNorm = interval integral -> panel bound ->
trapezoid sum -> owner node balls is type-complete, with only the
producer data (2338 balls, per the 2456 ruling) left to instantiate.

## Statements (ConnesWeilRH/Dev/C1RouteAQuadratureAttachment2459.lean)

Bump box shape (the bump depends on the position only through the
square, so each half-line has a monotone envelope):

- `widthBump_antitone_right_2459`: antitone on Ico 0 radius;
- `widthBump_mono_left_2459`: monotone on Ioc (-radius) 0.

Phase box shape:

- `cos_lipschitz_2459`, `sin_lipschitz_2459`: |cos u - cos v| <=
  |u - v| and likewise for sin, via
  Convex.norm_image_sub_le_of_norm_deriv_le on the whole line;
- `cos_midpoint_box_2459`, `sin_midpoint_box_2459`: on a panel
  [t0, t1] the value at any point sits within (t1 - t0)/2 of the
  midpoint value - exactly the producer's rho = halfwidth + DELTA box.

Doors (generic in the panel data, owner-free by design):

- `familyPanelMem_2459`: with the bump box (required to straddle
  zero, as the producer's clamped boxes do), cos box, and sin box over
  a panel, the composed ComplexRect2427 hull
  coefficient * bumpBox * phaseBox contains
  externalFamilyValue2344 at EVERY panel point, inside and outside the
  family support alike (outside, widthBump = 0 and the hzero clause
  carries containment).
- `sumPanelMem_2459`: the 30-family composed hull bounds the full
  family sum - one line, via ComplexRect2427.mem_sumFinset.

Attachment and glue:

- `panelQuadrature_le_of_trapLe_2459`: an upper bound T on the
  trapezoidal sum turns the 2457 panel theorem into
  integral <= T + (b - a)^3 zeta / (12 N^2) - the interface the node
  balls and zeta bound must feed.
- `stripNorm_eq_interval_2459`: stripNorm sigma F equals the interval
  integral whenever the integrand is supported in [a, b], via
  integral_eq_integral_of_support_subset - the seam between the 2343
  consumer constants and the panel-integral world of 2457.

Build: green on the ext4 mirror; all ten declarations audited on
[propext, Classical.choice, Quot.sound]
(build-logs/2459_quadrature_attachment_audit.log).

## Producer timing micro-experiment (throwaway timing modules, not committed)

To size the future 2338-ball producer's Lean-side sum evaluation, a
List rat literal sum bounded by a constant via `norm_num [vals]` was
timed on the mirror (scratch modules, deleted after measurement):

```
+--------+---------------------------+---------------------------+
| terms  | wall (s, incl. ~2 s       | options needed            |
|        | Mathlib import baseline)  |                           |
+--------+---------------------------+---------------------------+
| 100    | 2.7                       | none                      |
| 1000   | 6.6                       | maxRecDepth 200000        |
| 10000  | 88.1                      | maxRecDepth 200000 +      |
|        |                           | maxHeartbeats 8000000     |
+--------+---------------------------+---------------------------+
```

Reading: ~4.5 ms/term at the 1000 scale, ~8.6 ms/term at the 10^4
scale (superlinear). Linear extrapolation puts a single monolithic
norm_num over ~1.2 x 10^5 node terms at 17-50 minutes per strip sum,
and the recursion depth of the List fold grows with N, so the route
is borderline-possible but fragile. Recommendation (matching the 2454
per-node lesson): the producer should attach per-node ball bounds as
O(1) containment theorems and close the sum with Finset.sum_le_sum
over the panel - one small proof per node, no deep recursion - with
the monolithic norm_num kept only as a fallback for small panels.
Elaboration traps recorded along the way: single-uppercase-letter
identifiers silently bind as auto-bound type variables (the `Q`
incidents: HDiv N N Q / OfNat Q nonsense - the rationals are `Rat`
and `Q` is not a Mathlib name); rational literals need the numerator
ascribed `(a : rat) / b`; a 1000-element List literal needs
maxRecDepth headroom in the def, and the simp inside norm_num needs
it again at the use site.

## Scope

Generic analysis layer, no owner data instantiated, no strip norm
discharged (the producer that supplies htrap / the per-node balls is
the next brick), no producer GO, no RH claim.

Evidence:

- `ConnesWeilRH/Dev/C1RouteAQuadratureAttachment2459.lean`
- `ConnesWeilRH/Dev/C1RouteAQuadratureAttachment2459Audit.lean`
- `build-logs/2459_quadrature_attachment.log`
- `build-logs/2459_quadrature_attachment_audit.log`
