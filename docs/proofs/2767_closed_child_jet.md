# 2767 - Closed child transition jet containment

Status: Lean-verified closed-child replay interface.

For every point in `leftCell2740` or `rightCell2740`, including the shared midpoint, the corresponding rational transition jet contains the actual derivative at every order. This removes the midpoint exception from later interval-integral consumers.

Verification: Linux-native audit build 3675/3675, zero errors; standard axiom trio only.
