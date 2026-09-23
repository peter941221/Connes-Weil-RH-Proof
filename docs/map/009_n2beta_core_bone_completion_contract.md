# 009 — N2beta core-bone completion contract

Status: retained legacy interface because Lean source cites it. The route-alpha
taper producer is inactive after a formal narrow-window no-go; this record is
not a current RH lane.

## Reusable formal core

The N2beta stack formalized a finite Mellin interpolation owner on a compact
window:

- a Gram matrix and minimum-cost interpolation constant;
- linear independence of the finite Mellin representers;
- a compactly supported taper owner realizing prescribed node values;
- exact convolution transport of the node values;
- same-owner L1/L2 cost bounds and support addition;
- a quantitative consumer separating the construction fit from the final
  scalar margin.

The main modules are `C1WindowMellinGram.lean`,
`C1WindowMellinIndependence.lean`, `C1WindowTaperCore.lean`,
`C1WindowTaperAssembly.lean`, `C1WindowTaperLift.lean`, and
`C1QuantitativeConsumer.lean`, with paired audits.

The reusable assembly shape is:

```text
choose finite node values y
  -> construct one compact taper f with those Mellin values
  -> assemble g = u * f
  -> laplaceAt(g,node) = laplaceAt(u,node) * y(node)
  -> control support and L2 cost on the same owner
```

This is interpolation infrastructure. It supplies no detector gate sign.

### Legacy component index

Lean source comments use the original component numbers; keep this stable:

1. finite Mellin Gram/minimum-cost owner (`C1WindowMellinGram`);
2. finite representer independence (`C1WindowMellinIndependence`);
3. taper construction and quantitative taper bounds (`C1WindowTaperCore`,
   `C1WindowTaperLift`);
4. convolution assembly, support addition, and value transport
   (`C1WindowTaperAssembly`);
5. route-alpha fit/margin consumer and its healthy-owner wiring
   (`C1QuantitativeConsumer`, `C1RouteAlphaOwner`).

## Historical route-alpha decision

Route alpha attempted to use an explicit upper norm budget to beat the
invisible-anchor floor. Its formal shape consumer separated:

- `hfit`: the constructed owner fits below a chosen ceiling;
- `hJ1`: that ceiling is below the required analytic margin.

The node target, cardinality bound, real-part taper envelope, and source-zero
strip transport were formalized. Numerical model runs showed feasibility for
the model contract, but did not prove `hJ1` or the selected gate in Lean.

The unremoved analytic premise was the positive selected-detector
Archimedean gate. It was inherited from the route, not produced by N2beta.

## Formal no-go and route status

`routeAlpha_realPart_gap_budget_impossible_of_interval_length_le_one` proves
that the current real-part strict taper budget cannot hold on any interval of
length at most one: the zero-node gap gives an upper ceiling while the target
and envelope factors force an incompatible lower threshold.

Classification: `FORMAL`, scoped to the current route-alpha taper consumer.
It is not a no-go for finite Mellin interpolation or for healthy B5.

Consequences:

- do not resume route-alpha taper optimization on the narrow ROOT window;
- reuse the interpolation stack only when a live producer names its cost and
  sign consumer explicitly;
- never treat model digits or the formal shape consumer as a detector sign.

Detailed per-component chronology is in proof records 1379, 1381--1394 and
1881--1886, and in Git history.
