# 2879 Route B D4 derivative polynomial

For `r = 2q - 1 = t z`, the logistic differential equation gives

`z' = (2 t (1+t^2) (1-t^2 z^2)/(1-t^2)^2 - z) / t`.

Substituting this into the exact centred residual produces

`dH/dt = -2 P(t,z) / (t (1-t^2)^2)`,

where `P` is an exact polynomial of degree 15 in `t` and degree 4 in `z`.
The JSON artifact freezes `P`; certifying its sign on owner-coherent boxes is
the next formal monotonicity target.
