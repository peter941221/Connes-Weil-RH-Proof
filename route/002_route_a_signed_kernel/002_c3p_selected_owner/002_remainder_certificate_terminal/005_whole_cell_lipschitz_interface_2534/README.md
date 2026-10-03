# 005 — whole-cell Lipschitz inflation interface

Status: `LEAN SUPPORT CLOSED; OWNER FOURTH-DERIVATIVE INSTANTIATION OPEN`.

This terminal subtask supplies the generic bridge needed to replace a sampled
third-derivative maximum by a whole-cell bound. For a function f on a cell
[a,b], if

```text
‖f(x) - f(y)‖ <= L * |x-y|
```

for all x and y in the cell, then every point satisfies

```text
‖f(x)‖ <= max(‖f(a)‖, ‖f(b)‖) + L * (b-a)/2.
```

Here L is intended to come from a certified fourth-derivative enclosure of the
third-derivative channel. The theorem is generic and does not assert that the
Route A owner already has such an L.

Formal support:

```text
ConnesWeilRH/Dev/C1RouteAWholeCellLipschitz2534.lean
ConnesWeilRH/Dev/C1RouteAWholeCellLipschitz2534Audit.lean
```

Build result:

```text
Build completed successfully (1490 jobs).
Axiom audit: [propext, Classical.choice, Quot.sound]
```

The remaining work is owner-specific:

```text
1. derive a fourth-derivative magnitude envelope with signed modulation;
2. prove its validity on every 10240-grid cell;
3. use the 2534 interface to export upward rational whole-cell third bounds;
4. assemble the 2533 curvature charge and import it through segmented sums.
```

This support theorem does not close the exact owner identity, the selected
owner signed C3-prime margin, Producer GO, `SourceRH`, or RH.
