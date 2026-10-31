# 3227: Route A aggregate with endpoint values

Status: verified conditional aggregate adapter.

3227 inserts the already proved endpoint midpoint bounds from 3218 and 3226
into the 40960-cell aggregate. The remaining value hypothesis is now only for
the interior indices:

```text
forall index,
  0 < index -> index < 40959 ->
  weighted midpoint index <= valueUpper index
```

The endpoint-aware array sets both endpoint upper bounds to zero and leaves the
interior values supplied by the caller. This is an exact reduction of the
formal obligation, not an imported diagnostic row.

Verification: WSL2 ext4, Lean `4.30.0`, focused build and axioms audit. The
adapter uses exactly:

```text
[propext, Classical.choice, Quot.sound]
```
