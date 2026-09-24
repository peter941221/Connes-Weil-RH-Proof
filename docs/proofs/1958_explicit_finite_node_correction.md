# 1958 — Explicit finite-node correction for map 106 R0

Date: 2026-09-24.

Status: constructive R0 work; the final validation status is recorded below.
The determinant sign, interval moment enclosure, and joint spectral-tail margin
remain OPEN. No RH claim and no numeric sign experiment.

## Exact consumer and scope

The leaf `C1ExplicitFiniteNodeCorrection.lean` supplies a concrete alternative
inside the finite-window interpolation class used by map 106. The owner is
`(selectedOwner base (correction nodes seed y) n).sourceTest`.
The source transform at `s-1/2` and the power `n+1` are retained exactly.
This is not asserted to equal the old arbitrary classical-choice correction.
Its adoption as a signed-gate producer requires the same-owner margin screen;
no narrow-root or plain-bump gate estimate is transferred to it.

The old selector exposes finite node values and support but no formula for its
transform away from those nodes. This construction proves interpolation and
gives that formula with explicit node-separation denominators. The remaining
estimate is on a specified transform, not on an unconstrained selector.
This is R0 producer preparation, not completion of a signed core round.

## Construction

Let `seed` have nonzero mass `m = laplaceAt seed 0`, and let Z be a finite set
of distinct complex nodes (deduplicated by Finset). Define

```text
A_z(s) = product_(t in Z, t != z) (t-s)
q_z = product_(t in Z, t != z) (D+t) [exp(-z*x)*seed(x)]
correction = sum_(z in Z) y(z)/(A_z(z)*m) * q_z.
```

The product is implemented by a list of derivative shifts, not a new
distribution or an axiom. The existing Laplace rule for `D+t` gives

```text
laplaceAt q_z s = A_z(s) * laplaceAt seed (s-z)
laplaceAt correction s =
  sum_z y(z)/(A_z(z)*m) * A_z(s)*laplaceAt seed(s-z).
```

At a selected node all other summands vanish and the remaining denominator
cancels. Every denominator is nonzero by distinctness and the seed mass.
Differentiation and exponential multiplication preserve the closed support
window; the finite linear combination therefore retains that support.

`explicitSeed r hr` is the existing concrete `bumpLogTest` compressed by
positive r. Its mass is nonzero and its support is contained in
`[-2*r,2*r]`. To fit any prescribed open window about zero, choose r with
`lower < -2*r` and `2*r < upper`, and apply the closed-support inclusion.
No positivity of the gate is encoded in the seed or the correction.

Computability guard discovered in R0: Mathlib's `ContDiffBump.toFun` uses
`someContDiffBumpBase`, defined by `Nonempty.some`. Thus the named seed is a
fixed formal bump with proved support/nonnegativity/mass properties, not a
certified evaluable elementary formula. The cardinal interpolation is explicit
relative to that seed. A numerical implementation must either supply its own
proved analytic seed to the generic construction or use rigorous bounds valid
for the entire seed class. Substituting `exp(-1/(1-x^2))` without that proof
would change the owner. This is a remaining R0 task, not a failed build.

For any target subset of Z, choose the base by the same formula with values
one on the target subset. The theorem
`selectedOwner_explicit_base_and_correction_target` then proves the desired
raw-to-centered values for every convolution index, without a base-value
premise. Z may additionally include the prefix nodes with target value zero.

## Quantitative output and its limitation

The proved pointwise transform majorant is

```text
abs(laplaceAt correction s) <=
  sum_z abs(y(z))/(abs(A_z(z))*abs(m))
        * abs(A_z(s))*abs(laplaceAt seed(s-z)).
```

The selected-owner version multiplies this by
`abs(laplaceAt base s)^(n+1)` at the centered argument `s-1/2`.
The exact sum formula is retained alongside this norm bound. The norm bound
is for evaluating error/tail costs; it must not replace the signed sum when
estimating the determinant.

Small node separations are explicitly priced by `A_z(z)`. No uniform bound
independent of those separations, the node count, or rho is claimed.
No estimate on the determinant follows from interpolation alone.

## Remaining R0/R1 work

1. Instantiate the source's full target/zero-node union and priority rule;
   verify all orbit values, triple vanishing and zero-prefix conditions,
   including collisions. The generic interpolation identities are proved;
   the complete healthy producer assembly is not yet instantiated here.
2. Supply usable C4/C2 and certified seed-transform enclosures, with node
   separation and seed width visible. Existing decay existence theorems do
   not themselves give a numerical budget for this formula.
3. Screen this actual constructed family against the complete centered
   determinant and relative-tail target. A synthetic parameter sample is not
   a source zero and a supplied finite zero list is not automatically the
   complete spectral prefix. Record those distinctions in probe provenance.
4. If it survives, prove signed interval moments and their complement bounds;
   otherwise record a scoped selector/estimate no-go. Do not change the
   selected coefficient or discard signed cancellation to force a pass.

## Provenance and verification

Method: elementary cardinal interpolation implemented by existing differential
Laplace shifts, with the repository's concrete bump. This is not a claim of
original interpolation theory. No new external theorem is assumed.

The pre-edit mainline freeze check passed. Edited Windows files alone were
synced to the WSL ext4 mirror, compared byte-for-byte, and hashed. Builds use
the resource runner. Final focused and integration validation: PENDING.
