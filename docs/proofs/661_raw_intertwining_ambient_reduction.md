# Proof 661: raw intertwinement ambient reduction

## Result

Let

```text
I_(p,S)
  = T_(p,S) RawResponse_S
    - RawResponse_(p::S) T_(p,S)
```

be the recombined raw intertwinement from Proof 660. The existing covariance
identity is

```text
AmbientRawCovariance_(p,S) = oldFrame_(p,S) I_(p,S).
```

The old frame is isometric. Proof 661 first proves the generic operator-norm
fact

```text
||F A|| = ||A||
```

whenever `F` preserves every vector norm. Applying it to the actual old
suffix frame gives the exact equality

```text
||AmbientRawCovariance_(p,S)|| = ||I_(p,S)||.
```

The equality survives multiplication by the genuine ambient-loss scale
`s_p^(-1)`. Therefore the route-uniform raw and ambient statements are
equivalent with exactly the same bound, not merely comparable up to a
constant.

Combining this with Proof 660 gives

```text
exists a route-uniform scaled complete-target bound
  <->
exists a route-uniform scaled ambient-covariance bound.
```

## Why This Reduction Matters

The source operator and ambient column have different codomains, so a generic
composition estimate would only prove one inequality. The isometric readback
proves both directions and prevents a hidden frame-condition constant from
entering Bone 1A.

```text
source raw row
      |
      | old suffix frame (isometric)
      v
ambient covariance column

operator norm: exactly preserved
```

## Boundary

Proof 661 does not bound either side. It also does not identify the raw
response with Proof 658's adjacent projection commutator. It only moves the
same unresolved operator to the ambient carrier without loss.

## Lean Owners

```text
ConnesWeilRH/Source/CCM25Concrete/
  ...AntiresonantInteriorRawIntertwiningAmbientReduction.lean
ConnesWeilRH/Dev/
  ...AntiresonantInteriorRawIntertwiningAmbientReductionAudit.lean
```

Verification in the Ubuntu-24.04 WSL2 ext4 mirror used the shared Lake lock:

```text
+--------------------------------------+-------+--------+
| target                               | jobs  | result |
+--------------------------------------+-------+--------+
| Proof 661 focused audit              |  3448 | PASS   |
| Proof 661--662 combined audits       |  3450 | PASS   |
| CCM25Concrete aggregate              |  3937 | PASS   |
| full repository                      |  4018 | PASS   |
+--------------------------------------+-------+--------+
```

Every audited theorem uses exactly
`[propext, Classical.choice, Quot.sound]`. No `sorry`, `admit`, or user axiom
was added.
