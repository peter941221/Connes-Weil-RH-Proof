# 1241 - G8 adjoint-shear Gram candidate

Date: 2026-09-09.

Status: `SCREENED-LIVE`; paper candidate only.  Consumer: the
healthy-`CompactLog`, selected-detector, same-owner B5 gate.

Record 1240 killed the direct completion `(I+N_S)^*W_g(I+N_S)` because the
right input factor sees `N_S J=0`.  The existing physical factorization gives
instead

```text
N_S = J L_S^*,
N_S^* J = L_S,
J^* N_S = L_S^*.
```

This suggests moving the adjoint shear to the input side:

```text
T_S := I + N_S^*,
G^+_{g,S} := T_S^* W_g T_S
           = (I+N_S) W_g (I+N_S^*).
```

The source-owner compression has the exact expansion

```text
J^* G^+_{g,S} J
  = J^*W_gJ
  + J^*N_SW_gJ
  + J^*W_gN_S^*J
  + J^*N_SW_gN_S^*J
  = J^*W_gJ + Response_S + Response_S^* + L_S^*W_gL_S.
```

The second term has the active target-response orientation already owned by
the oblique-shear reduction.  The third is its adjoint, and the fourth is an
internal positive leakage square.  Unlike G7, none of these terms vanishes
from the source owner merely by `N_S R=0`.

## Symbolic admission screen

G8 survives the first screen because it is a positive Gram kernel and its
same-owner compression contains the required signed response without an
external subtraction or a trace cycle.  It is not yet a positivity theorem:
the baseline, the real cross term, and the leakage square still need a literal
finite-visible-prime/archimedean ledger whose limit is `qw(g)`.

The next admissible work is therefore one owner-level algebraic lemma for the
displayed compression, followed by a trace-class/readback contract using the
existing `L_S` physical factorization.  Do not add a selector, wrapper, or
numeric prototype until that contract identifies the `qw` channel.  If the
cross term is found to require an adjoint or cyclic rearrangement not supplied
by the existing owner, G8 is killed at that point.

RH is not claimed.
