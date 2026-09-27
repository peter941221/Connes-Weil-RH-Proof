# Record 2028 - Route-B Cut-1 coupling scan: pre-registration

Date: 2026-09-27.

Status: PRE-REGISTRATION. No theorem, no verdict, no RH claim. This file
fixes the instrument and the decision rules before the run.

Subordinate to `docs/map/103_four_point_same_span_three_cut_campaign.md`
(Cut 1), `docs/map/106_centered_signed_moments_joint_tail_execution.md`
(sections 3 and 6), `route/000_rh_mainline/002_b5_compactlog/002_route_b_fourpoint_span/README.md`
(R-B0..R-B4), and `docs/proofs/1957_plan_b_same_owner_joint_margin_reaudit.md`.

## 1. Owner, consumer, premise to remove, failure criterion

Consumer (unchanged, one owner throughout):

```text
same rho, same base/correction, same n, same lambda_n = b_n / C_n
    -> det_n < 0                        (gate side, Cut 2)
    -> beta_s * L_n < m_rho * lambda_n^2 (tail side, Cut 1)
    -> qw(h_n) < 0 and qw(h_n) >= 0 -> SourceRH -> Mathlib RH
```

Owner of THIS scan: exactly the record-1980/1981 under-approximation owner,

```text
rho  = 0.55 + 14.134725141734693 i
N    = 4
seed = powered seed, L_p(s) = L_smoothSeed(s/2)^10
```

i.e. the known-zero under-approximation, NOT the complete formal source owner.
Every reading this scan produces inherits that label.

Premise to remove (both halves are OPEN per record 1957, section "The shortest
joint acceptance test"):

```text
(i)   lambda_n >= ell_rho > 0 for arbitrarily large admissible n
(ii)  det_n < 0 at those same n
```

Failure criterion: a checked obstruction, or a reproducible trend that kills
the "the geometric tail closes along large n" form of Cut 1 on this owner.

## 2. What this scan decides, and what it does not

Cut 1 currently has two possible currencies:

```text
n  :  the (1/2)^n (or q^n) geometric decay of the high-shell tail, bought by
      pushing the convolution index
q  :  a contraction constant below 1/2 on the interpolation base
```

Record 1982 buys the tail with `q` at `n = 4`. The un-bought alternative is
`n`. This scan measures whether `n` is a *free* parameter on this owner, by
attacking exactly two questions:

```text
Q1  does lambda_n keep a positive lower bound as n grows?
Q2  does det_n keep its sign as n grows?
Q3  is n admissible at all far enough for the tail to close?
```

Q3 is not a numerical question. The visible-prime owner of the span is
determined by the support radius, and the rig convention (records 1959/1980/
1981) is `support_radius = 2 * (n + 2)`, so the finite visible-prime-power set
is `{k prime power : k <= exp(2(n+2))}`. Its cardinality is therefore a
*measurable, exact* function of `n`, and it is the same book that record 2020
identified. If that book empties the certified route set before the tail can
close, then `n` is not a currency and Cut 1 must be paid with `q`.

This scan does NOT decide the determinant sign for the actual formal owner,
does not interval-certify anything, and does not touch COVER or TAIL Lean
objects.

## 3. Measured object, per n

```text
support_radius          s_n = 2 * (n + 2)                       [exact]
prime_power_count       P_n = #{k prime power : k <= exp(s_n)}  [exact]
certified_route_set     {Ap, B, A} membership by P_n            [exact]
gate entries            C_n, b_n, D_n, det_n, lambda_n          [grid-limited]
tail proxy              L_n / lambda_n^2                        [proxy]
```

Route availability is fixed by the committed rig caps (record 1959,
`gate_entries`): `Ap` needs `P_n <= 4000`, `B` needs `P_n <= 60000`,
`A` needs `P_n <= 3000000`. `CERTIFIED_ROUTES = (Ap, B)`; route `A` is
recorded but excluded because its dual-spline interpolation costs
`1e-2..1e-1` relative on the prime channel.

Cancellation depth of the determinant (needed here, measured in P2):

```text
rho_det = -det_n / (C_n * D_n)      = 7.6e-04 at n = 4
```

so a route with `1e-2` relative prime-channel error cannot fix the sign of
`det_n` at `n = 4`. Gate entries are therefore reported per route and the
trend alone is read.

## 4. Registered decision rules

Evaluated on the measured range `0 <= n <= 7` (section 5):

```text
COUPLING-HOLDS
  lambda_n stays in a band [ell, L] with ell > 0 on every measured n that has
  a certified route, AND det_n < 0 on every such n.
  -> Cut-1's large-n form survives; q is optional.

COUPLING-COLLAPSES
  lambda_n crosses zero, or changes sign, or det_n becomes positive on some
  measured n that has a certified route.
  -> the "geometric closure along large n" form of Cut 1 is dead as stated.

CONDITIONING-BLOCKS
  the certified route set empties (P_n > 60000, hence no Ap and no B) at some
  n before the profile of (i)/(ii) can be read, and the measured budget
  `n_needed` for a `(1/2)^n` closure exceeds that n.
  -> n is not a currency here; Cut 1 must be paid with q, and R-B1 becomes
     mandatory rather than optional.
```

The three labels are not exclusive in their evidence: if COUPLING-HOLDS holds
on the readable range and CONDITIONING-BLOCKS holds on the range needed, both
are reported and the routing consequence is the CONDITIONING-BLOCKS one.

## 5. Registered instrument

```text
owner            rho, N, seed as section 1 (imported from record 1981's rig)
xi grid          [-25, 25], dxi = 0.02  (primary)
refinement grid  dxi in {0.05, 0.02, 0.01, 0.005, 0.002} at n in {2, 4}
n range          0 <= n <= 7
prime route      direct (B) for P_n <= 60000; route A above, labeled
quadrature       composite trapezoid on the uniform xi grid
primary quadrature order for the seed transform: 300 (as record 1981)
```

Registered reproduction anchor: the dxi = 0.05, n = 0..4 rows must reproduce
`results/1981_powered_seed_underapprox.json` on C, b, D, det, lambda. A
deviation above `1e-9` relative is an erratum against one of the two
artifacts, not a new reading.

## 6. Pre-registered aliasing risk (must be reported, not hidden)

The direct route evaluates `cos(2*pi*xi*log k)` on the uniform xi grid, so it
resolves only `log k <= 1/(2*dxi)` (Nyquist). At dxi = 0.05 that is `log k <= 10`,
while the n = 4 row carries `log k` up to 12. The n = 4 row of record 1981 is
therefore *pre-registered as suspect*: the refinement block exists to measure
whether its C, b, D move under dxi. Whatever the refinement block reports is
recorded as a reading on the 1981 artifact, with the deviation stated.

## 7. What this cannot decide

- No formal-owner statement: the source-zero set is the known-zero
  under-approximation.
- No interval certificate: floats generate data, Lean must verify the
  eventual constant.
- No statement about route A's precision beyond the committed exclusion.
- Nothing about COVER, and nothing about the correctness of the target
  detector construction.
- No RH claim.
