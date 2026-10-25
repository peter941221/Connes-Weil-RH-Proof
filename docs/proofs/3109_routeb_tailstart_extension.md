# Route-B tail-index extension and unconditional prefix transport (3109)

Date: 2026-10-25.

The previous 3108 interface required `5 <= tailStart` as an owner premise.
That premise is now discharged by the construction itself.  Starting with the
index supplied by the geometric tail lemma, the construction chooses

```text
tailStart' = max 5 tailStart.
```

The three estimates needed by the raw owner are preserved:

```text
T <= 2^(tailStart' + 1)
2 * |Im rho| <= 2^(tailStart' + 1)
4 * spectralMultiplicityConstant * (3/4)^tailStart' < xiMultiplicity rho.
```

The last inequality uses monotonicity of `(3/4)^n` and the nonnegativity of
the multiplicity constant.  The closed-ball zero certificate is rebuilt at
the enlarged radius before the `OrbitG8Geometry` object is created.  This is
essential: enlarging only the index field after construction would not enlarge
the zero-control ball and would be unsound.

New audited interfaces:

```text
exists_orbitG8Geometry_of_sourceNontrivialZero_right_tailStart_ge_five
  -> an owner geometry with 5 <= geometry.tailStart

exists_rhoOwnerPackage_tailStart_ge_five3108
  -> the same owner packaged with healthy detector data

exists_rowBSpanPrefix_owner3108
  -> same-owner row-B shell-prefix negativity under only
     off-line, right-half-plane, and wired imaginary-cap premises
```

Verification in the Linux ext4 mirror:

```text
lake build ConnesWeilRH.Dev.C1G8R0OrbitGeometryAudit
lake build ConnesWeilRH.Dev.C1RouteBPrefixOwnerTransport3108Audit
```

The combined run completed successfully with 3885 jobs.  The four new or
extended declarations report no `sorryAx` and exactly:

```text
[propext, Classical.choice, Quot.sound]
```

This closes the `tailStart >= 5` interface gap and transports the row-B prefix
on a genuinely same-owner construction.  It does not prove the fixed-24 gate,
the three cardinal pins, the high-shell tail closure, or RH.
