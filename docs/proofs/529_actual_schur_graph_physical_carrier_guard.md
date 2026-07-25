# Proof 529: graph physical carrier guard

## Result

Proof 529 formally separates the graph cascade from the source-owned Julia
range readout.

The source step record permits changing only `fixedSourceReadout`:

```text
stepData.fixedSourceReadout -> arbitrary G -> G
stepData.rangeSine          -> unchanged
stepData.readout            -> unchanged
stepData.transfer_contract  -> unchanged
```

At the same time, the graph product is independent of the entire `stepData`
function:

```text
suffixActualSchurGraphPhysicalProduct(lambda, stepData, S)
```

has the same value for any two step-data functions with the same carriers.
Consequently its source coframe, graph endpoint, physical graph target, and
graph boundary residual are also independent of `stepData`.

## Why this matters

The existing `rangeSine_readback` constrains the field `readout`, but the
fixed-source Julia consumer reads `fixedSourceReadout`. Since the latter can
be changed without changing the graph product or the other constrained fields,
the physical Julia readout cannot be inferred from the graph cascade.

The valid dependency is therefore:

```text
graph product
    -> graph endpoint / graph target              (closed)

fixed-source Julia readout
    -> physical readout equality                  (separate producer)

graph target + endpoint residual
    -> actual boundary target                     (closed by Proof 528)
```

No graph-to-Julia factorization, family-uniform estimate, Gate 3U sign,
finite-S sign, Burnol identity, or RH conclusion is asserted.

## Lean owners

```text
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSActualSchurGraphPhysicalCarrierGuard.lean
ConnesWeilRH/Dev/
  CCM24FiniteSActualSchurGraphPhysicalCarrierGuardAudit.lean
```

The focused audit must remain at the repository baseline axiom set:

```text
[propext, Classical.choice, Quot.sound]
```
