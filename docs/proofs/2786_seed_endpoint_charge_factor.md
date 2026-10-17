# 2786 seed endpoint charge factorization

The endpoint charge is factored exactly as `8 * transition coefficient * 4096^(2n) / 2^4096`. For orders 4 and 7 this rewrites with the pinned coefficients 5856 and 72179776. This exposes the coefficient-to-charge arithmetic without changing the endpoint owner.
