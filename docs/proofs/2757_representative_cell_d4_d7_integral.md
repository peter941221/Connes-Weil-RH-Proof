# 2757 - Representative-cell D4/D7 integral envelope

Status: Lean-verified interior-cell integral envelope.

`representativeD4D7Cell_integral_bound2757` converts the pointwise D4 and D7 interval memberships into interval-integral bounds over the full representative cell:

```text
integral_cell ||smoothTransition''''||
  <= (cell.hi - cell.lo) * D4Box.endpointAbsMax

integral_cell ||smoothTransition'''''''||
  <= (cell.hi - cell.lo) * D7Box.endpointAbsMax
```

The proof uses continuity of the iterated derivatives, interval-integral monotonicity, and the elementary endpoint enclosure `abs x <= max(abs lo, abs hi)`. It introduces no floating-point assumption.

Verification: Linux-native audit build 3667/3667, zero errors; the theorem uses only `[propext, Classical.choice, Quot.sound]`.

This is one representative cell only. Full finite partition replay, numerical D4/D7 pins, carrier transfer, Producer GO, SourceRH, and RH remain open.
