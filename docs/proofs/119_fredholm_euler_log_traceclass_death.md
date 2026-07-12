# 119 Fredholm Euler Log Trace-Class Death

Date: 2026-07-12

## Formal Attraction

The identity

```text
-log det(I-aT)=sum_(m>=1)a^m Tr(T^m)/m
```

would provide the missing Euler logarithm coefficient if `T=U_p` were a
trace-class operator.

## Operator Obstruction

The dilation translation `U_p` is unitary on an infinite-dimensional `L2`
space.  All its singular values equal one, so it is not compact, Hilbert--
Schmidt, or trace class.  The raw Fredholm determinant is undefined, and the
bosonic second-quantized partition trace has infinite multiplicity.

The half-line block `Q U_p P` does not repair this.  It restricts to a unitary
translation between two `L2` intervals of length `log(p)`, hence has infinite
rank and infinitely many singular values one.

After convolution smoothing one may obtain a Hilbert--Schmidt boundary
operator `K_h`.  The available regularized determinant then starts with

```text
-log det_2(I-aK_h)=sum_(m>=2)a^m Tr(K_h^m)/m.
```

The prime channel `m=1` is absent.  Moreover `K_h^m` inserts the test smoothing
at every multiplication, so its trace is not the raw single-crossing value of
the same square at `m log(p)`.

## Verdict

```text
raw determinant/Fock owner: analytically undefined
regularized determinant: wrong channel set and wrong same-object powers
noncompact cancellation supplied: none
RH: unproved
```

