# 2874 Route B D4 centred factorisation

The exact D4 numerator is rewritten with

`t = 2u - 1`, `r = 2q - 1`, and `z = r/t`.

The numerator factors as `t * (t z - 1) * (t z + 1) * H(t,z)`. The remaining
polynomial `H` contains only even powers of `t` and the owner-coherent ratio
`z`. This extracts the zero at `u = 1/2` and removes the false requirement for
a uniform sign margin at that endpoint.

The logistic identity is
`z = tanh(2t/(1-t^2)) / (2t)`, with the continuous endpoint value `z = 1`.
The JSON artifact freezes the exact factorisation. It is an algebraic bridge,
not yet a sign or integral certificate.
