# 1982 - Powered-seed contraction candidate

Date: 2026-09-25.

Status: CONTRACTION_CANDIDATE_ONLY. This record is not a GO certificate, a
complete-owner result, a determinant proof, or an RH proof.

The complete q-parameterized tail interface is now present in
`ConnesWeilRH/Dev/C1FourPointHighShellTail.lean`:
`convolutionIterate_convolution_vertical_sextic_bound_of_q` and
`selectedOwner_convolutionSquare_vertical_twelfth_bound_of_q` are audited in
the paired audit file, together with
`selectedOwner_fullOrbit_span_doubleDistance_bound_of_q` and
`selectedOwner_fullOrbit_span_fourthOrderSpectralTail_of_q`. The focused build
completed successfully with 3810 jobs, zero `error:` lines, zero `sorryAx`, and
only `[propext, Classical.choice, Quot.sound]`. The remaining gap is now the
analytic q bound and complete-owner certificate, not the Lean tail interface.

## Decision

The explicit assumption change is:

```text
old:  ||Laplace(base)(sigma + i*t)|| <= 1/2       for |t| >= T
new:  ||Laplace(base)(sigma + i*t)|| <= q          for |t| >= T
```

For the powered seed from record 1981, the proof-friendly candidate is:

```text
T = 28
q = 2^(-14) = 6.103515625e-5
```

The choice deliberately does not chase the smallest grid-fitting power. It
leaves a large contraction margin while retaining a very small same-index
tail proxy. T = 28 also remains in the same dyadic prefix shell as T = 22.

## Fixed owner and gate

The probe keeps the same owner, base, correction, and n as record 1981:

```text
rho              = 0.55 + 14.134725141734693 i
N                = 4
known zeros      = 19
owner cardinality= 27
n                = 4
lambda           = b / C = 1437.9886769624593
```

The n = 4 gate row is:

```text
C      = +3.0001193333906233e6
b      = +4.3141376309518780e9
D      = +6.1989414790621120e12
det    = -1.4196333983436800e16
```

Thus the under-approximation has the required gate signs. The source-zero
set is still only a known-zero under-approximation to the formal
`sourceNontrivialZerosInClosedBallFinset`, so this is not the actual-owner
claim required for GO.

## Contraction screen

The powered base was evaluated on a grid with `dt = 0.01`, sigma step
`0.025`, and height up to `64`. The largest observed values after the proposed
thresholds were:

```text
T = 18   max = 5.253375401047778e-4
T = 20   max = 4.429839218242408e-4
T = 22   max = 1.708808765120703e-6
T = 24   max = 1.3645458013049666e-6
T = 28   max = 3.131211046492847e-9
T = 32   max = 1.2339733117793015e-12
```

At `T = 28`, `q = 2^(-14)` has a grid margin of approximately
`6.1032e-5`, while the observed maximum is only `3.1312e-9`. This is
evidence for a candidate interval target, not a proof of the all-sigma/all-
height inequality.

## Exact all-strip target audit (2026-09-25)

The q premise is for the interpolation base, not for `poweredSeed` by itself.
The Lean object is

```text
explicitPoweredHealthyBase rho
  = correction (healthyUnscaledTargetNodes rho) poweredSeed (fun _ => 1)
```

The existing exact correction formula expands its transform into the finite
sum

```text
sum_z (1 / (P(z,z) * L(0))) * P(z,s) * L(s-z)
```

where `z` ranges over `healthyUnscaledTargetNodes rho`, `P` is the actual
`nodeProduct`, and `L = laplaceAt poweredSeed`. The powered-seed identity then
gives `L(s-z) = laplaceAt smoothSeed ((s-z)/2)^10`. Thus every summand carries
both an owner-specific node-product ratio and a frequency shifted by its
target `z`.

For the diagnostic row, the target set has eight elements. At `T = 28`, a
target with imaginary part `+14.1347...` can reduce the seed frequency to
`(28 - 14.1347...)/2 = 6.9326...`; the negative-height target gives the
matching case for negative `t`. Therefore a raw-seed estimate at frequency
`t/2 = 14` does not certify the required base bound. The existing grid does
evaluate the correct finite interpolation base, but it does not certify the
continuous sigma/height domain or the unbounded tail.

The recorded explicit smooth-seed derivative/L1 constants currently cover
orders 0 through 3. The powered-seed formalization gives its exact transform
and support, but does not yet give an interval-certified uniform bound for the
eight-term node-product-weighted sum above. This is a proof-boundary finding,
not a counterexample to the candidate: q remains analytically unproved and the
route remains `CONTRACTION_CANDIDATE_ONLY`.

A first-derivative integration-by-parts majorant was checked and is too weak.
Writing `S(u) = laplaceAt smoothSeed u`, `m = S(0)`, and
`D1 = integral ‖deriv smoothSeed‖`, compact support gives

```text
‖S(a + i*y)‖ / m
  <= exp(2*|a|) * (D1 + |a|*M) / (m*|y|),
```

where `M = integral ‖smoothSeed‖`. The committed bounds give `D1 = 2`,
`M <= 4`, and the plateau on `[-1,1]` gives `m >= 2`. For the closest
target-shifted frequency at `T = 28`, `|a| <= 3/4` and `|y| >= 6.932637...`;
the resulting upper bound is about `1.61616`, already above one before the
node-product ratio is included. This rules out this particular coarse
majorant as a contraction proof. It is not a lower bound on the actual
transform and does not rule out a sharper weighted estimate or an interval
certificate.

The base's eight healthy target nodes must not be confused with the full
`healthyCorrectionNodes rho N routeNodes` used by the actual correction and
its C2/node-separation costs. Both objects remain in their intended roles;
neither may be replaced by a hand-picked design set.

## Same-index tail proxy

Record 1981 gives, at the same `n = 4` and `lambda`,

```text
old proxy with (1/2)^n = 5.2196232589646985e25
```

Replacing the contraction factor by the candidate q gives:

```text
5.2196232589646985e25 * (q / 0.5)^8
= 2.573472955612212e-6
```

So the candidate is numerically strong enough to make the same-index tail
proxy less than one while preserving the gate witness. This is the first
strictly smaller quantitative obligation in this branch:

```text
prove the powered-seed all-strip q-bound for the complete actual owner,
then feed q^n into the existing tail theorem for the same n and lambda.
```

## Why this remains four-point SPAN

No route boundary changes:

```text
same healthy owner
    -> same base/correction
    -> same four-point orbit annihilator
    -> same determinant gate
    -> same spectral tail
```

Only the scalar contraction premise in the high-shell tail is generalized
from `1/2` to `q`. It therefore remains inside the four-point SPAN route, not
a ROOT-window B1 or fixed-prime route.

## Failure boundary

Do not call this GO until all of the following are upgraded simultaneously:

```text
1. complete sourceNontrivialZerosInClosedBall owner;
2. interval-certified C, b, det and lambda for that owner;
3. interval-certified all-strip q-bound;
4. same-index tail ratio < 1 using the same exact n and lambda;
5. exact visible-prime owner and Lean construction for the powered seed.
```

Reproduction:

```text
python scripts/fourpoint_powered_contraction_1982.py
```

The output is `results/1982_powered_contraction_candidate.json`.
