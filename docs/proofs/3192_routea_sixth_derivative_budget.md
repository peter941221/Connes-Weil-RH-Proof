# 3192 Route A Sixth-Derivative Budget

Status: Lean sixth-order derivative budget verified; Taylor-6 integral panel
still open.

The existing bump derivative ladder was limited to orders zero through four.
This record extends the exact recurrence and polynomial absolute-value bounds
through orders five and six, with constants

```text
bumpConstant(5) = 962956800
bumpConstant(6) = 60020395200
```

The owner budget now proves the explicit sixth-order statement
`correctedPhysical_sixth_iteratedDeriv_budget2350`. This is the derivative
bound needed by the 3187 midpoint remainder formula. It does not yet prove
the integral identity or the cell-wise signed upper bound used by 3187, and it
does not import any numerical JSON data into Lean.

Validation used the repository Lean toolchain in a Linux-native WSL2 ext4
workspace. The focused build and axiom audit passed with exactly
`[propext, Classical.choice, Quot.sound]`.
