# 2773 - Tight exponential-tail bound

Status: Lean-verified tight remainder bound.

For every `0 <= y <= 1`, the explicit order-20 Taylor remainder satisfies `expTail y <= 1/240`. The proof unfolds the exact remainder formula and uses rational arithmetic plus `y^20 <= 1`.

Verification: Linux-native audit build 3665/3665, zero errors; standard axiom trio only.

This tightens the representative endpoint propagation input beyond the generic `expTail <= 1` bound.
