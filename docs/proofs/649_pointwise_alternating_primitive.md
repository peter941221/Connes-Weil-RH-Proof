# Proof 649: pointwise alternating primitives

## Result

Proof 649 applies the uniform boundedness principle (Banach--Steinhaus) to
the exact route family isolated by Proof 648.

One index packages all three moving parameters:

```text
i = (p, S, proof that (p :: S).Nodup, N).
```

Write `H_i` for Proof 646's canonical finite-horizon readout. The new
pointwise premise is

```text
for every fixed ambient u,
  exists M_u, for every route-valid i,
    ||H_i u|| <= M_u.
```

Banach--Steinhaus converts the input-dependent constants into one operator
constant:

```text
exists M, for every route-valid i,
  ||H_i|| <= M.
```

Proof 648 then constructs, for every route-valid `(p,S)`, the ambient loss
factor with the same shared bound. Restricting it to the suffix frame gives
the active raw Bone 1 domination. The existing raw/renewed column comparison
gives the renewed domination with bound `8M`.

The proved implication chain is

```text
pointwise bounded on every ambient u
                    |
                    v  Banach--Steinhaus
one operator bound for all (p,S,N)
                    |
                    v  Proof 648 + Douglas
route-uniform raw Bone 1 domination
                    |
                    v  Proof 634
route-uniform renewed domination, cost 8
```

Lean also proves the reverse implication from a route-uniform horizon bound
to pointwise boundedness, so the first two properties are equivalent.

## Exact remaining theorem

Proof 649 does not prove the pointwise premise. The active source theorem is
now exactly

```text
forall u : finiteSCarrier,
  exists M_u : Real,
  forall p S N,
    (p :: S).Nodup ->
    ||H_(p,S,N) u|| <= M_u.
```

Equivalently,

```text
sup_(route-valid p,S,N) ||H_(p,S,N)u|| < infinity
```

for each fixed ambient `u`.

This premise is substantially stronger than Proof 647's convergence after
composition with the raw loss column:

```text
H_(p,S,N)(L_p^dagger newFrame_S x) -> Interior_(p,S)x.
```

That convergence controls `H_N` only on a moving range and only after fixing
`(p,S,x)`. Banach--Steinhaus cannot extend it to arbitrary ambient `u`, nor
can per-step pointwise bounds be combined into a route-uniform result without
control of the moving prime and suffix.

```text
+------------------------------------------------------+------------------+
| layer                                                | status           |
+------------------------------------------------------+------------------+
| route-valid `(p,S,N)` index                          | constructed      |
| pointwise family bound -> uniform operator bound     | proved           |
| uniform operator bound -> pointwise family bound     | proved           |
| pointwise premise -> raw Bone 1 domination           | proved           |
| pointwise premise -> renewed domination, cost 8      | proved           |
| pointwise bound for every ambient input              | open             |
| Bone 1 / Gate 3U / finite-S sign / Burnol / RH       | open             |
+------------------------------------------------------+------------------+
```

## Lean owners

```text
ConnesWeilRH/Source/CCM25Concrete/
  ...AntiresonantInteriorPointwiseAlternatingPrimitive.lean
ConnesWeilRH/Dev/
  ...AntiresonantInteriorPointwiseAlternatingPrimitiveAudit.lean
```

## Verification

The Ubuntu-24.04 WSL2 ext4 focused audit passed under the shared Lake lock:

```text
+--------------------------------------+-------+--------+
| target                               | jobs  | result |
+--------------------------------------+-------+--------+
| focused seven-declaration audit      |  3422 | PASS   |
+--------------------------------------+-------+--------+
```

All seven audited declarations use exactly
`[propext, Classical.choice, Quot.sound]`.
