# Proof 647: infinite-horizon coupled-tail decay

## Result

The result is good qualitative progress, but it does not close Bone 1.
Proof 647 proves that the one terminal tail left by Proof 646 converges to
zero on every fixed source vector at the actual unit Sonin scale.

For the whole-line logarithmic translation `U_a`, Lean first proves

```text
U_a^N u = U_(N a) u,
(-U_a)^N u = (-1)^N U_(N a) u.
```

If `a > 0`, every matrix coefficient of the translation orbit vanishes:

```text
<v, U_(N a) u> -> 0.
```

The complete coupled ambient target `C_(p,S)` is compact at unit Sonin scale.
It therefore turns the weakly escaping orbit into norm decay:

```text
Tail_(p,S,N)x
  = C_(p,S)(-U_(log p))^N newFrame_S x
  -> 0.
```

Combining this with Proof 646's exact endpoint identity gives

```text
H_(p,S,N)(L_p^dagger newFrame_S)x
  -> signedCompressedInteriorOwner_(p,S)x.
```

This is strong operator convergence: it holds after fixing `x`.

## Proof mechanism

The weak-escape proof does not assume a Fourier spectral theorem.  It uses
the concrete real-line geometry:

```text
arbitrary L2 vectors u,v
          |
          v  dense approximation
continuous compactly supported f,g
          |
          v  positive translations eventually separate supports
<g,U_(Na)f> = 0 for all sufficiently large N
          |
          v  translation isometry + approximation error
<v,U_(Na)u> -> 0
```

For a compact operator `K`, every bounded weakly null sequence `x_N` obeys

```text
||K x_N|| -> 0.
```

The proof takes compact closure of `K(range x)`, shows every cluster point is
zero by testing against `K^dagger y`, and then uses uniqueness of the cluster
point.  Applying this lemma to the actual compact coupled target keeps its
outer, reflected, second-support, and prolate branches recombined.

## Why this is not Bone 1

Bone 1 needs one bounded readout, equivalently a uniform same-vector bound.
Proof 647 supplies only a sequence of finite-horizon readouts.  The known
estimate is still

```text
||H_(p,S,N)|| <= N ||C_(p,S)|| / s_p.
```

The distinction is structural:

```text
+--------------------------------------+-----------------------------+
| statement                            | status                      |
+--------------------------------------+-----------------------------+
| Tail_N x -> 0 for every fixed x      | proved                      |
| H_N RawColumn x -> Interior x        | proved                      |
| ||Tail_N|| -> 0                      | not proved                  |
| sup_N ||H_N|| < infinity             | not proved                  |
| bounded factor Interior = H RawColumn| not proved                  |
| Bone 1 / Gate 3U / finite-S sign     | open                        |
| Burnol identity / RH                 | open                        |
+--------------------------------------+-----------------------------+
```

Strong convergence cannot be promoted to operator-norm convergence merely
because the target is compact.  Nor can the uniform boundedness principle be
applied to `H_N`: its pointwise action is controlled only after composition
with the raw column, not on every ambient input.

## Next target

The remaining quantitative question is whether the complete coupled target
has a bounded antiresonant quotient:

```text
C_(p,S) = Q_(p,S) (I + U_(log p))
```

with the required route-uniform control, or equivalently whether its action
on approximate `-1` spectral modes decays at the same rate as the raw loss
column.  Exact kernel compatibility and strong tail decay are already known;
the missing property is a uniform rate.

## Lean owners

```text
ConnesWeilRH/Source/CCM25Concrete/
  ...AntiresonantInteriorInfiniteHorizonTail.lean
ConnesWeilRH/Dev/
  ...AntiresonantInteriorInfiniteHorizonTailAudit.lean
```

## Verification

The Ubuntu-24.04 WSL2 ext4 verification copy passed under the shared Lake
lock:

```text
+--------------------------------------+-------+--------+
| target                               | jobs  | result |
+--------------------------------------+-------+--------+
| infinite-horizon tail source         |  3417 | PASS   |
| focused eight-declaration audit      |  3418 | PASS   |
+--------------------------------------+-------+--------+
```

All eight audited declarations use exactly
`[propext, Classical.choice, Quot.sound]`.  The source and audit contain no
`sorry`, `admit`, or user axiom.
