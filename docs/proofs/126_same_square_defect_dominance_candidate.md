# Same-Square Defect-Dominance Candidate

Status: research candidate only. The endpoint/Sonin same-range implementation
is rejected by the one-prime test in proof 127. The abstract candidate remains
open only for a genuinely different noncompact range. This document is not a
Lean owner and is not part of the active RH route.

## Candidate statement

For one compact test `g`, one finite prime set `S`, and one common
support-square owner, seek operators `A_S` and `B_S` and a nonnegative
remainder `R_S(g)` such that

```text
QW(g,g) + ||B_S g||^2
  = ||A_S g||^2 + R_S(g).
```

The defect operator must be the same-object boundary/projection defect that
appears in the trace read-off; it may not be introduced after replacing the
test or the convolution square. The intended quantitative gate is

```text
||B_S g||^2 <= epsilon(S) * ||g||_X^2,
epsilon(S) -> 0,
```

on the codimension-three test space annihilating the pole nodes. This would
give the unconditional, finite-cutoff lower bound

```text
QW(g,g) >= -epsilon(S) * ||g||_X^2,
```

which is weaker than Weil positivity at every finite `S` but could feed an
RH consumer if the estimate were uniform on a dense common form domain.

## Why this is a genuinely new proposal

The proposal does not assume Weil positivity or a zero-location statement. It
tries to make the error term itself a measurable square on the same source
object, rather than asserting that a positive trace is already equal to `QW`.
The only desired input is a quantitative decay estimate for the defect.

## Immediate falsification tests

1. A decomposition that defines `B_S` as the square root of the negative part
   of an unknown remainder is circular and is rejected.
2. If the finite-prime translation channels are placed in `B_S`, their norm
   cannot be assumed to vanish with `S`; they contain the exact `p^(-m/2)/m`
   channels required by the Weil terms.
3. If `epsilon(S) -> 0` is proved uniformly on a dense common form domain,
   then taking the limit yields Weil positivity and therefore contains the RH
   conclusion. Such a proof would not be a lower producer; it would already be
   the central breakthrough.
4. The CC20 `-2 Id + compact` remainder shows that compactness alone cannot
   establish the required decay of `B_S`.

## Current verdict

This is a useful target for a new proof search because it separates the exact
same-object identity from the quantitative defect estimate. It does not yet
pass the lower-producer test: the only currently visible route to
`epsilon(S) -> 0` is RH-level, and the finite-prime channels obstruct a naive
cutoff decay argument.

No Lean declaration or route consumer should be added until an independent
bound for `epsilon(S)` is proved.

The first concrete implementation test is recorded in
`127_same_square_p2_defect_verdict.md`.
