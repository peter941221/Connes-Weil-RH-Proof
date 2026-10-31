# 3231-3232: Route-A middle-point interval bridge

Status: verified enclosure bridge; aggregate sign remains open.

For the most negative diagnostic cell, `index = 17168`, the formal bridge now
proves:

- the midpoint is inside every one of the 30 owner family supports;
- each family bump value is enclosed by an owner-derived rational interval;
- each family phase is enclosed by the existing Taylor-and-squaring phase
  rectangle;
- each exact family contribution is contained in its corresponding complex
  rectangle;
- the exact 30-family physical value is contained in the finite aggregate
  rectangle.

The final independent axis-aligned aggregate rectangle is intentionally not
claimed to have negative real upper. Independent family rectangles lose the
shared phase and cancellation information needed by the observed approximate
value near `-38.016`. This is a formalization boundary, not evidence that the
owner value is positive.

Verification: WSL2 ext4, project toolchain `leanprover/lean4:v4.30.0`, Lean
`4.30.0`, focused builds and axioms audit. The audit must report exactly:

```text
[propext, Classical.choice, Quot.sound]
```
