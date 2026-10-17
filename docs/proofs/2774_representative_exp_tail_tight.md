# 2774 representative exponential tail tightening

The representative phase endpoint satisfies `0 <= -P.lo / 4 <= 1`, where `P` is the exact phase interval for `representativeCell2736`. Applying the exact tail formula bound on `[0,1]` gives `expTail (-P.lo / 4) <= 1/240`.

This is an exact Lean theorem, audited through the standard axiom trio only. It tightens the endpoint input used by the rational phase exponential box; it does not close the child box or establish RH.
