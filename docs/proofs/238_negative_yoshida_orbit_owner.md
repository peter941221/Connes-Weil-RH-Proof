# Proof 238: negative Yoshida orbit owner

Date: 2026-07-14

Status: axiom-clean Lean construction of one support-growing, half-density
centered selected owner whose actual functional-equation/conjugation orbit
sum is `-2`.  The owner also cancels every selected nearby source node outside
that orbit and retains the fourth-order square tail.  The construction needs
only the off-line condition `Re(rho) != 1/2`; it does not assume that `rho` is
nonreal.  The Burnol all-zero explicit formula and the finite-S same-domain
remainder sign remain open, so RH is unproved.

## 1. Arbitrary target values survive the power

The previous unscaled assembly normalized every target to `1`.  A negative
orbit needs one target value `-1`, but putting `-1` in the repeated base would
make the final sign depend on the convolution count.

The new generic theorem
`exists_nearbyZero_unscaled_targetValues_assembly_of_fixedThreshold` instead
uses

```text
Laplace(base)(w)=1
```

on every finite target node and puts the desired value in the final
correction.  Therefore, for every chosen count `n`,

```text
Laplace(base^(n+1)*correction)(w)
  =1^(n+1) targetValue(w)
  =targetValue(w).                                   (N.1)
```

The same theorem retains the growing support, zero values at selected nodes
outside the target set, and the fixed-threshold quadratic tail.

## 2. Collision-safe source orbit

Define the genuine source orbit as the `Finset`

```text
O_s(rho)={rho,1-conj(rho),conj(rho),1-rho}.           (N.2)
```

The target-value function is

```text
V_rho(z)=
  1   if z=rho,
 -1   if z=1-conj(rho),
  0   otherwise.                                     (N.3)
```

The priority in `(N.3)` matters.  Off the critical line, `rho` and
`1-conj(rho)` are distinct.  If conjugation fixes `rho`, the four displayed
expressions in `(N.2)` collapse to two points; `(N.3)` assigns one value to
each actual point instead of demanding both `1` and `0` at `rho`.

For a nonreal point, the four points are distinct and `(N.3)` is exactly

```text
H(rho)=1,
H(1-conj(rho))=-1,
H(conj(rho))=0,
H(1-rho)=0.                                          (N.4)
```

`exists_fixedWindows_nearbyZero_unscaled_negativeSourceOrbit_assembly`
constructs one raw compact log factor with `(N.3)`, cancels every other
selected node, and retains the same far-strip bound.

## 3. Actual centered orbit sum

The half-density translation maps the source orbit injectively by

```text
u=z-1/2.
```

The selected square at the centered point is

```text
Phi(z-1/2)=conj(H(1-conj(z))) H(z).                   (N.5)
```

At the two distinguished points, `(N.3)` and `(N.5)` give

```text
Phi(rho-1/2)=-1,
Phi((1-conj(rho))-1/2)=-1.                           (N.6)
```

In the nonreal case the other two values vanish, so the four-point sum is
`-2`.  In the real-degenerate case the source orbit is already the two-point
set in `(N.6)`, so its sum is also `-2`.

Lean theorem `selectedOwner_centeredOrbit_sum_eq_neg_two` performs this case
split and sums over

```text
centeredFunctionalEquationOrbit rho
```

as a real `Finset`.  It does not sum a four-term list that might count a
collided point twice.

## 4. One owner with the tail and cancellations

The final theorem
`exists_fixedWindows_nearbyZero_negativeOrbit_selectedOwner` returns one
`SelectedWeilSquareOwner` with all of the following facts:

```text
owner.sourceTest has the centered values V_rho;
sum_(u in centered orbit) Laplace(owner.square)(u)=-2;
owner.square vanishes at every selected source z outside O_s(rho),
  evaluated at z-1/2;
the source factor has the fixed-threshold quadratic tail;
the same selected square has the fourth-order companion tail.
```

The only geometric assumptions are a prescribed base/correction window,
`Re(rho) in [0,1]`, `Re(rho) != 1/2`, and `epsilon>0`.  There is no source-RH,
nonreal-zero, bad-space, trace-sign, or finite-prime positivity premise.

The finite-prime crossing wrappers continue to consume the same selected
owner.  Compactness and ordinary trace still require the explicit
`GlobalPrimePowerTraceBasisData` witnesses; Proof 238 does not erase them.

## 5. Lean evidence

```text
ConnesWeilRH/Source/CC20YoshidaConvolution.lean
  line 1010  exists_nearbyZero_unscaled_targetValues_assembly_of_fixedThreshold

ConnesWeilRH/Source/CC20YoshidaFullProduct.lean
  line 52   sourceFunctionalEquationOrbit
  line 59   negativeSourceOrbitValue
  line 627  exists_fixedWindows_nearbyZero_unscaled_negativeSourceOrbit_assembly

ConnesWeilRH/Source/CCM25Concrete/UnscaledYoshidaSelectedOwner.lean
  line 87   centeredFunctionalEquationOrbit
  line 148  selectedOwner_negativeHermitianPair_sum_eq_neg_two
  line 208  selectedOwner_centeredOrbit_sum_eq_neg_two_of_nonreal
  line 259  selectedOwner_centeredOrbit_sum_eq_neg_two
  line 366  selectedOwner_centered_source_distance_bound_lt
  line 387  selectedOwner_convolutionSquare_tail_of_source_tail
  line 602  exists_fixedWindows_nearbyZero_negativeFourPointOrbit_selectedOwner
  line 737  exists_fixedWindows_nearbyZero_negativeOrbit_selectedOwner
```

The WSL import-facing verification passed:

```text
ConnesWeilRH.Source.CCM25Concrete.UnscaledYoshidaSelectedOwner
ConnesWeilRH.Dev.UnifiedRemainingGapsYoshidaConvolutionAudit
ConnesWeilRH.Dev.CC20YoshidaFullProductAudit
ConnesWeilRH.Dev.UnscaledYoshidaSelectedOwnerAudit
```

The owning selected-owner build completed 3496 jobs.  Every new audited
declaration reports only

```text
propext
Classical.choice
Quot.sound
```

with no `sorryAx` or project axiom.  The printed final theorem type visibly
contains the adaptive centered values, the finite orbit sum `-2`, nearby-node
cancellation, and both tail bounds.

## 6. Route judgment

```text
arbitrary finite target values after unscaled powers: exact
source functional-equation orbit owner:               exact
nonreal four-point pattern 1,-1,0,0:                  exact
real orbit collision handling:                        exact
actual centered Finset orbit sum:                     -2
same-owner nearby-zero cancellation:                  exact
same-owner fourth-order square tail:                  exact
Burnol all-zero spectral identity in Lean:            open
finite-S post-Q remainder owner:                      mathematical evidence only
integrated sign of -2 Id+K_(S,I):                     open
Lean RH route rewire:                                  none
RH:                                                    unproved
```

The next step is not more finite interpolation.  Proof 113 rules out imposing
the compact bad-space conditions in a prime-free window and retaining a
negative Weil value.  Because this owner's support grows, the surviving route
must identify its visible finite-prime crossings with the same finite-S
positive trace and prove the sign of that complete same-domain remainder.
