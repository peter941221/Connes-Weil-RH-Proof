# Proof 736: Gate Physical Prefix Detector Functional

## Result

Proof 736 separates the genuine detector from the finite family-dependent
boundary data without taking a norm.

For ambient vectors `a,b`, define the continuous matrix-coefficient functional

```text
omega_(a,b)(A) = <a,A b>.
```

For the first `N` vectors of Proof 735's natural source Hilbert basis, set

```text
Phi_(S,N)(A)
  = sum_(i < N)
      [<J e_i,A(U_S e_i)> + <F_S e_i,A(J e_i)>].
```

Here

```text
J   = sourceInclusion,
U_S = sourceEndpointCancellationResidual,
F_S = sourceActualBandForwardCoframe.
```

Lean constructs `Phi_(S,N)` as a genuine continuous linear map

```text
B(finiteSCarrier) ->L[C] C
```

and proves the exact same-object identity

```text
sourceGatePhysicalPrefixCompressionTrace(S,N)
  = Phi_(S,N)(detectorOperator).
```

Thus Proof 735's remaining analytic input can be stated as

```text
forall N,
  norm(Phi_(S,N)(detectorOperator owner)) <= C,
```

with the existing pair data supplying fixed-family trace legality.

## Structure

```text
family S, source prefix N                  compact-root detector W
            |                                        |
            v                                        |
   finite physical functional Phi_(S,N)              |
            |                                        |
            +---------------- evaluate --------------+
                             |
                             v
                   complete signed Gate prefix
                             |
                             | Proof 735, N -> infinity
                             v
                    ordinary Gate trace
```

This is the first owner in the current physical chain where the detector is an
explicit argument rather than buried inside the Gate response.

## Guard

Do not estimate the operator norm of `Phi_(S,N)` and multiply it by the norm of
the detector.  That separates completed boundary coefficients by absolute
value and recovers the forbidden total-variation route.  Compact root support
must instead be used while evaluating the complete functional.

Proof 736 supplies no uniform bound.  Gate 3U, the finite-S sign, Burnol's
identity, and `_root_.RiemannHypothesis` remain open.

## Verification

The source, import-facing audit, and `CCM25Concrete` aggregate batch passed
with `4005/4005` jobs.  The final full-repository acceptance build after
Proofs 735--738 passed with `4087/4087` jobs.  All five audited Proof 736
theorems use exactly `[propext, Classical.choice, Quot.sound]`.  No `sorry`,
`admit`, user axiom, heartbeat increase, recursion-limit increase, overlong
line, or new linter warning was added.
