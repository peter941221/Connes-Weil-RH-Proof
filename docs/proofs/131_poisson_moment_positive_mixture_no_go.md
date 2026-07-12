# Poisson-Moment Positive-Mixture No-Go

Date: 2026-07-12

Status: rejected by a finite-measure moment obstruction. RH remains unproved.

## Candidate F

For `0<=t<1`, the Poisson operator

```text
P_t=(1-t^2)(I-tU)^(-1)(I-tU*)^(-1)
```

is positive and has the exact Fourier expansion

```text
P_t=I+sum_(m>=1)t^m(U^m+U*^m).
```

Seek a finite positive measure `lambda_a` on `[0,a]` such that the positive
mixture

```text
M_a=integral_[0,a] P_t d lambda_a(t)
```

has Euler-log coefficients

```text
integral_[0,a] t^m d lambda_a(t)=a^m/m       for every m>=1.  (P.1)
```

This would preserve positivity and put the required `1/m` into one common
owner before the crossing length is read.

## Moment obstruction

Define the finite measure

```text
d mu_a(t)=t d lambda_a(t).
```

Equation (P.1) becomes, for every integer `n>=0`,

```text
integral_[0,a] t^n d mu_a(t)
  = a^(n+1)/(n+1)
  = integral_0^a t^n dt.                              (P.2)
```

Polynomials are dense in the continuous functions on the compact interval
`[0,a]`. Equality of all moments in (P.2) therefore implies equality of the
finite measures:

```text
mu_a = Lebesgue measure on [0,a].
```

Away from zero this forces

```text
d lambda_a(t)=dt/t.
```

But

```text
integral_(0,a] dt/t = infinity.
```

Hence no finite positive `lambda_a` satisfies (P.1).

An atom at zero cannot repair the result: it changes only the zeroth moment of
`lambda_a` and adds more identity bulk, while all positive moments remain
unchanged.

## Interpretation

The formal identity

```text
integral_0^a (P_t-I) dt/t
  = sum_(m>=1) a^m/m (U^m+U*^m)
```

is valid only after subtracting the divergent identity part before
integration. That subtraction is a renormalized signed operation, not a finite
positive owner. It is the continuous-moment form of the scalar-compensation
obstruction.

## Verdict

```text
exact a^m/m moments: force dt/t
positive mixing measure: infinite total mass
archimedean identity bulk: infinite
renormalized subtraction: not positive
finite positive Poisson mixture: impossible
```

This rules out every finite positive radial mixture of Poisson kernels, not
only one chosen density.
