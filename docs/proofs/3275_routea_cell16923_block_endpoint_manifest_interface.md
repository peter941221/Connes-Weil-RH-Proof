# Route A cell 16923 block endpoint manifest interface

Record 3275 adds a small Lean interface for the six bump-correlated physical
blocks introduced by record 3272. The full rectangle is defined as the nested
sum of the six existing block rectangles. Its real upper endpoint is proved to
be exactly the sum of the six block real upper endpoints, and a second theorem
converts six independent block upper bounds into a full-rectangle upper bound.

```text
six block endpoint lemmas
          |
          v
full rectangle reHi = sum of block reHi
          |
          v
full endpoint upper bound
```

This is a proof-generation interface, not the missing numerical certificate.
The direct attempt to reduce all 30 families, all bump intervals, all phase
boxes, and all endpoint min/max branches in one `norm_num` invocation timed out
at Lean's 200000-heartbeat default. The 3275 interface therefore keeps each
future endpoint lemma small and independently auditable.

The focused WSL2 ext4 build used the repository toolchain:

```text
lean-toolchain: leanprover/lean4:v4.30.0
Lean: 4.30.0
LEAN_NUM_THREADS=1 lake build \
  ConnesWeilRH.Dev.C1RouteAConcreteOwnerBumpCorrelatedFullValue3275 \
  ConnesWeilRH.Dev.C1RouteAConcreteOwnerBumpCorrelatedFullValue3275Audit
```

The audit reports exactly:

```text
[propext, Classical.choice, Quot.sound]
```

The 40960-cell aggregate, the 16923 complete value membership bridge, the
derivative bounds, the full-line tail, the B5 readback, `producer_go`,
`SourceRH`, and RH remain open.
