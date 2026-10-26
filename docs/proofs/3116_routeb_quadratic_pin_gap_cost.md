# Route-B quadratic pin and near-line cost (record 3116)

Status: kernel-checked necessary quadratic-pin cost and exact fixed-cap
parameter counterexample on the actual powered correction. No RH claim.

The owner is `explicitPoweredHealthyCorrection rho N routeNodes`, exactly
the raw correction used by the powered-seed detector construction. The
named premise under review is its all-strip quadratic cardinal pin, the
`hquadraticPin` input of the same-owner row-B consumer. This is a cost
theorem about that premise, not a replacement owner or positivity mechanism.

The target is a necessary lower price from the correction's proved values
`+1` at `rho` and `-1` at `1-conj(rho)`. Write `delta=abs(Re(rho)-1/2)`
and `t=Im(rho)`. Under `delta<=1/16` and `abs(t)>=1`, the proposed bound is:

```text
t^2 <= (16*(2*pi)^2*C2 + 4*t^2)*delta
```

The proof uses the Schwarz estimate on a complex disk of radius 1/4 about
`1-conj(rho)`. The disk remains inside the strip; its frequencies have
absolute value at least `abs(t)/2`. The quadratic pin bounds the transform
there by `4*(2*pi)^2*C2/t^2`, while the two target values differ by 2.
All analytic hypotheses must come from the actual compact-log Laplace
transform. A fixed stored capture is not used as an arbitrary-rho proxy.

Completion: Lean proves the necessary cost and an adapter for the actual
powered-seed correction, with exact axiom audit and Linux ext4 Lake build.
The result must retain its height/gap and pin hypotheses. It must not assert
that any off-line zero exists or that such zeros approach the line.

Budget: one focused analytic entry, at most 20 minutes of build wall time,
8 GiB resident memory and 2 GiB additional proof outputs; at least 8 GiB
free disk required. No numerical sweep, generated cell campaign or cold
certificate rebuild. Stop on an unavailable analytic interface or a failed
mathematical bound rather than changing the owner or hiding a premise.

## Proved statements and owner identity

`C1RouteBQuadraticPinGapCost3116.lean` proves the disk argument first for an
entire function with the two specified values. It then specializes it to
the actual `laplaceAt (explicitPoweredHealthyCorrection rho N routeNodes)`.
Complex differentiability comes from `C1XiResidue.differentiable_laplaceAt`;
the two values come from `explicitPoweredHealthyCorrection_targets` and
the healthy companion-value theorem. They are not assumed numerical data.

The theorem `powered_correction_cardinal_pin_cost3116` states the result
with precisely the cardinal-sum quadratic pin shape. The existing
`laplaceAt_correction` identity supplies the transform/cardinal bridge.
It retains the same nodes, powered seed and coefficient function. It is
the raw correction's pin, rather than an unidentified bound on the
assembled detector or its convolution square.

For `delta>0`, rearranging the proved inequality gives the necessary price:

```text
C2 >= t^2 * (1-4*delta) / (16*(2*pi)^2*delta)
```

Thus, at a fixed nonzero height and small positive gap, this particular
all-strip pin must grow at least at inverse-gap scale. This follows from
analyticity and the opposite target values; a different seed preserving
those conditions must obey the same generic analytic inequality.

The actual correction exists for every finite `N` and `routeNodes`; both
remain arbitrary in the specialized theorem. Increasing either does not
remove this necessary cost.

## Exact fixed-cap consequence

The theorem `powered_correction_fixed_pin_gap_floor3116` specializes to
`wiredC2RowB2721=29000000` and proves, without a small-gap premise:

```text
|Im(rho)| >= 1
rho off the critical line
actual correction satisfies the fixed all-strip C2 pin
             |
             v
abs(Re(rho)-1/2) >= 1/29696000004
```

For small gaps, the proof uses `pi<4`, `t^2>=1`, and the analytic cost.
For gaps larger than 1/16, the displayed floor is already smaller than
1/16. No floating-point or external numerical certificate enters the proof.

The exact point `tinyGapPoint3116` is
`(1/2+1/10^12)+i`. Its correction cannot satisfy the fixed C2 pin, for any
`N` or finite additional node set. The audit also proves that the point
satisfies the existing row-B norm and imaginary caps. Therefore those caps
alone do not remove the small-gap obstruction over parameter space.

This point is not asserted to be a zeta zero. The counterexample rejects a
fixed-pin assertion over all such complex parameters. For hypothetical
off-line zeros, the theorem is a necessary condition on any proposed pin
supplier. It does not establish that there are zeros below the floor, or
reject all parameter-dependent Route-B constructions.

## Verification

The Linux ext4 audit command is:

```text
LEAN_NUM_THREADS=1 python3 scripts/routeb_quadratic_pin_gap_audit_3116.py
```

The checker builds the source and audit modules with Lake, requires all
eleven exact declaration names, checks the success footer and return code,
and rejects errors, missing declarations, and unsupported axioms. The
result is `results/3116_routeb_quadratic_pin_gap_audit.json`.

```text
Build completed successfully (3899 jobs).
```

All eleven audited declarations have exactly
`[propext, Classical.choice, Quot.sound]`, with no `sorryAx`. The final
focused build takes about 69 seconds and peaks below 4 GiB resident memory;
most dependencies are cached. Ten parser controls pass, including direct
and Lake output formats, identifier substitution, missing footer, nonzero
exit, new/sorry axioms, weakened analytic footprint, and source errors.

The formal boundary checks include the exact tiny-gap parameter example,
its membership in the wired caps, exclusion of zero height from the stated
height hypothesis, and impossibility of opposite values at a point on the
critical line (where the two interpolation nodes coincide).

## Consequence for the RH direction

3115 remains a valid exterior theorem with an explicit node-degree guard,
and its stored-owner numerical margins remain model results. Certifying
that fixed capture's C4 bound can establish a local benchmark, but it does
not price the actual correction for an arbitrary hypothetical zero.
3114's prefix theorem also applies to its own rho-dependent owner, so
its identity cannot be replaced by the fixed capture.

The next universal Route-B argument must permit a rho-dependent C2 price
or independently prove the necessary gap restriction. Its tail budget must
then be re-evaluated with the actual C2, height, node set and convolution
parameters. The signed gate must still hold for that same assembled test.
No gate sign follows from the upper bounds in this record.

```text
actual opposite target values
              |
              v
rho-dependent necessary C2 cost             FORMAL (3116)
              |
              v
same-owner tail budget at that actual cost  OPEN
              |
              v
same-owner signed gate and zero coverage    OPEN
              |
              v
RH                                          OPEN
```

Route A remains the binding selected-detector producer; the pointwise
joint-symbol mechanism is closed under 3093-3094 and cannot supply the
missing sign. A Route-B continuation must preserve its own same-span
identity and the stated scope of the existing no-go records.

## Method and primary sources

The analytic method is the classical Schwarz estimate, implemented by
Mathlib v4.30 at revision `c5ea00351c28e24afc9f0f84379aa41082b1188f`:
`Complex.dist_le_div_mul_dist_of_mapsTo_ball` in
https://github.com/leanprover-community/mathlib4/blob/c5ea00351c28e24afc9f0f84379aa41082b1188f/Mathlib/Analysis/Complex/Schwarz.lean.
No originality claim is made for that method. This record specializes it
to the project's actual all-strip pin and owner.

Related project results are 3063/3096 (opposite-target inverse-gap L1
cost), 3105 (fixed-owner height boundary), and 3115 (the actual exterior
bound and its node-degree guard). The new conclusion concerns the C2
pin itself, rather than converting an unproved L1 ceiling into a pin.
