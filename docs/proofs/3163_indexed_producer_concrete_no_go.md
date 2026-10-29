# 3163: concrete live source is not an indexed producer

Date: 2026-10-29
Status: CLOSED as a construction route; the no-go is proved.

## Result

The live object `Source.Dev.ConcreteP1SupportProbe.concreteWeilForm` cannot
satisfy the 3162 producer contract. This is not a failure of the contract
syntax. It is a semantic failure of the current common-only support data:

```text
common bump support       -> prime 2 only
arbitrary convolution     -> can expose prime 3
producer contract         -> must route every visible arbitrary prime
```

## Formal evidence

The proof is in `ConnesWeilRH/Dev/IndexedProducerConcreteNoGo3163.lean`.

1. `concrete_counter_term_three_ne_zero` proves that the concrete source
   finite-prime term at `3` is nonzero for a test bump with value `1` at `3`
   (`:42-78`). Therefore prime `3` is visible for the arbitrary pair
   `(counterBump, 0)` because the diagnostic concrete convolution is addition
   (`:80-100`).

2. `concrete_common_prime_three_not_visible` proves that prime `3` is not
   visible for the selected common bump. Its support is contained in
   `[3/2, 5/2]`, so both the value at `3` and the reciprocal value at `1/3`
   vanish (`:102-128`).

3. Any `IndexedFinitePrimeProducer` yields `finitePrimeDominance` through
   `indexedSourceTestCertificates`. Applying that dominance statement to the
   prime-3 arbitrary witness contradicts the common non-visibility theorem
   (`:130-138`).

The four printed axiom audits are exactly:

```text
[propext, Classical.choice, Quot.sound]
```

No `sorryAx`, new axiom, empty-set shortcut, or stored conclusion is used.

## Consequence

Do not replace the current root with a producer instance. The missing theorem
is an arbitrary-convolution support theorem, not another common-pair row:

```text
per-common support
       !=
arbitrary indexed producer support
```

The next admissible work item is to prove a genuine support restriction for
all `(f, g)` under the actual source algebra, or to redesign the live source
owner so its common support is mathematically compatible with that restriction.
A common-only certificate cannot close this gap.

RH is not claimed.
