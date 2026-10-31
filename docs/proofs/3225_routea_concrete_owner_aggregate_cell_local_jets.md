# 3225: Route A aggregate with cell-local jets

Status: verified conditional aggregate adapter.

The 3225 adapter supplies 3213 with:

```text
secondUpper = record2680CellSecondBound3224
fourthUpper = record2680CellFourthBound3224
sixthBound = record2680UniformSixthBound3220
```

The only remaining per-cell premise is the signed midpoint `valueUpper`:

```text
weightedExternal3201 (...) (record2680Center3212 index)
  <= valueUpper index
```

This is the correct interface for the final cancellation proof. The midpoint
value array remains open, and therefore the signed finite aggregate and
`producer_go` remain open.

Verification: WSL2 ext4, Lean `4.30.0`, focused build and axioms audit. The
adapter uses exactly:

```text
[propext, Classical.choice, Quot.sound]
```
