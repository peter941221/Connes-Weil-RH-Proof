# Epsilon-tunable price for the far joint-symbol tail (record 3064)

Date: 2026-10-19.

Status: ownerwise asymptotic tail reduction. It shows that the far-tail
allowance can tend to zero for each fixed hypothetical zero. It does not
bound the finite-core signed integral and is not a sign result or RH proof.

## Freeze the finite interpolation owner first

Fix one source nontrivial zero `rho`, the base test and its vertical
contraction threshold `T`. Write

```text
nStart = a dyadic index with
         T <= 2^(nStart+1),
         2*|Im(rho)| <= 2^(nStart+1),
k = max(nStart,1),
R = 2^(k+1) + 2 + dist(2,rho).
```

Let `Kmult = spectralMultiplicityConstant` and `m = xiMultiplicity(rho)`.
Since `m>=1`, any

```text
0 < epsilon < min(1, 1/sqrt(12*Kmult))
```

gives `4*epsilon^2*Kmult < 1/3 <= m`. As `(3/4)^k<=1`, the same fixed `k`
satisfies the geometry's tail-budget condition for every such epsilon.
Consequently the source-zero prefix radius `R` is fixed while epsilon varies.

The key quantifier order is already implemented by
`exists_nearbyZero_unscaled_targetValues_assembly_with_fixedCorrection`:
for the fixed finite node set and fixed base data, it chooses one correction
and one finite quadratic strip constant `C`, then proves its product-tail
bound for every orbit index `n`. Neither the correction nor `C` depends on
epsilon. The construction can therefore use

```text
C <= C_bump,
X = (6*pi)^2*C_bump/epsilon,
n = ceil(log_2(X))  (for X>=1).
```

The 3060 interpolation price makes `C_bump` finite for this fixed owner,
even if its node separation and hence its numerical value are poor. The
epsilon-independent radius is what lets that same finite constant be reused.

## Price the 3058 tail with the 3059 cutoff

The orbit support half-width is `L=n+2`. Record 3059 gives the same-owner
envelope `C_S <= 48*L*exp(L)`. Put

```text
T* = max(T,1,2*|Im(rho)|),
Q0 = K + 8 + log(2) + log(T*) + 1/3,
A0 = 16/(3*pi*T*^3),
q = 1/log(2).
```

Record 3058 then gives

```text
E_tail(T*) <= A0*epsilon^2*(Q0 + 48*L*exp(L)).
```

For `X>=1`, `n=ceil(log_2 X) <= log_2 X + 1`, so
`L<=log_2 X+3` and `exp(L)<=e^3*X^q`. Therefore

```text
E_tail(T*) <= A0 * (
  Q0*epsilon^2
  + 48*e^3*((6*pi)^2*C_bump)^q
      * epsilon^(2-q) * (log_2(((6*pi)^2*C_bump)/epsilon)+3)
).
```

Because `log(2)>1/2`, `q=1/log(2)<2`. With `rho`, `T*`, the node set and
`C_bump` fixed, both terms tend to zero as `epsilon` tends to zero. The
apparently exponential support price from 3059 is therefore beaten by the
tail's epsilon-squared factor: the convolution count only grows logarithmically
in `1/epsilon`.

This is an ownerwise statement. It does not give a uniform rate as `rho`
varies, because `C_bump` may diverge when the off-line distance shrinks, as
record 3063 proves is necessary for fixed-support interpolation.

## What this closes and what remains

For each fixed hypothetical `rho`, the absolute far-tail allowance in 3058
can be made smaller than any prescribed positive number while retaining one
fixed correction and increasing only the later convolution count. Thus the
coarse prime-symbol envelope is not, by itself, a permanent obstruction to
making the far tail small. This refines the pricing caution in records 3058-59
and the fixed-owner gap discussion in record 3061.

The remaining sign target does not follow: as `n` changes, the same-owner
transform on the finite interval `[-T*,T*]` also changes. No lower bound is
known for its signed core integral, and the selected detector's `qw<0`
contradiction cannot be recovered from a tail estimate alone. The next gate
is an explicit core estimate that tracks this same epsilon-dependent owner
and beats its negative-band deficit. A fixed-owner, epsilon-independent core
margin has not been proved.

Evidence:

- `ConnesWeilRH/Source/CC20YoshidaConvolution.lean` constructs the correction
  before choosing the convolution count and exposes the all-count tail bound.
- `ConnesWeilRH/Dev/C1G8R0OrbitGeometry.lean` uses `tailAccuracy` in the
  multiplicity budget and builds the prefix radius from `tailStart`.
- `docs/proofs/3058_joint_symbol_absolute_tail_reduction.md` gives `E_tail`.
- `docs/proofs/3059_visible-prime-symbol-envelope_price.md` gives
  `C_S <= 48*L*exp(L)`.
- `docs/proofs/3060_fixed_bump_interpolation_price.md` gives a finite
  parameterized `C_bump` for each fixed separated node set.
- `docs/proofs/3063_healthy_orbit_forced_near_collision_cost.md` records why
  that constant cannot be uniform as `rho` approaches the critical line.
