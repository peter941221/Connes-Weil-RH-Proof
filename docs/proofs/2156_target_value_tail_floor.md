# 2156 — Target-value lower floor for the four-point high-shell certificate

Date: 2026-09-29.

Status: EXACT PARAMETERIZED NECESSARY CONDITION for the named `C4/C2`
high-shell certificate; scoped no-go for the registered unit proxy at low
convolution index. It is not a no-go for the actual shell consumer without
its `s,m` parameters, the true tail, another tail method, or RH.

## Owner, consumer, and failure criterion

The consumer is the same-index four-point contradiction: a negative
semi-local vertex gate for the span `h(lambda)` must be paired with a
strict spectral high-shell bound below its prefix anchor. The owner is
the actual `selectedOwner base correction n` with its exact finite
visible-prime set; this record uses only its interpolation targets, not
the prime book. The current certificate is
`selectedOwner_fullOrbit_span_fourthOrderSpectralTail_of_q` in
`ConnesWeilRH/Dev/C1FourPointHighShellTail.lean`, with global strip
constants `C4,C2` and contraction `q`.

Assume `rho=beta+i gamma`, `0<=beta<=1`, `gamma>0`, and the exact target
values `laplaceAt base rho = 1` and `laplaceAt correction rho = 1`.
The premise to discharge is the strict `hsmall` tail budget on the *same*
`n` and positive `lambda`. The failure criterion is a lower bound on the
required `hsmall` expression divided by the consumer's allowed budget at
or above 1, valid for every legal `C4,C2,lambda`.

## Exact lower bound

The formal global strip hypotheses evaluate at `sigma=beta,t=gamma`:

```
C4 >= (gamma/(2*pi))^4,
C2 >= (gamma/(2*pi))^2.
```

Write `H=3+|rho|`. The exact theorem's smallness expression is

```
H^4 (H^4+|lambda|)^2 (2*pi)^12 q^(2n) (C4*C2)^2 < epsilon^2.
```

In the record-2033 **unit proxy**, `epsilon^2=lambda^2`. For an actual
spectral-shell prefix `s` with zero multiplicity `m`, the next consumer
instead requires `beta_s*epsilon^2 < m*lambda^2`, where
`beta_s=4*spectralMultiplicityConstant*(3/4)^s`. Hence, for every
nonzero `lambda`, the required normalized ratios are strictly greater
than

```
F_unit(rho,n,q) = H^4 * gamma^12 * q^(2n),
F_actual(rho,n,q,s,m) = (beta_s/m) * F_unit(rho,n,q).
```

The factors of `2*pi` cancel *exactly*. Thus `F_unit>=1` rules out the
registered unit-proxy closure, and `F_actual>=1` rules out the actual
strict shell consumer for the named `s,m`. These conclusions are
independent of the correction family, vertex coefficient, and finite
prime book. They use the global `C4/C2` hypotheses of the named theorem;
they do not lower bound the actual spectral tail.

## Consequence for the 2151–2154 numerical owner

That model has `beta=0.945`, `gamma=39.25244858548658`, `n=0`, and the
registered `q=2^-14`. Since `gamma>39` and `H>42`, for every `n<=3`:

```
H^4 gamma^12 q^(2n)
  > 42^4 * 39^12 / 2^84
  = 2407977714414158733957201 / 1208925819614629174706176
  > 1.
```

The final strict comparison is integer arithmetic:
`42^4*39^12 - 2^84 = 19184830316792472948016400 > 0`.
So every `n<=3` row fails the **registered unit proxy** before its gate is
evaluated. In particular, the sampled `n=0` vertex rows of 2151–2154
cannot pass the record-2033 proxy under these target values.
At the stored model value the floor is about `4.27e25, 1.59e17,
5.92e8, 2.21` for `n=0,1,2,3`; only `n>=4` is *not excluded by this
lower bound*. The bound is a necessary condition, not a tail enclosure.

For the actual formal consumer, multiply by `beta_s/m`. The exact
no-go condition is `m <= beta_s*H^4*gamma^12*q^(2n)`; no simplicity of
zeta zeros or unit shell factor is assumed. The 2151–2154 numerical
owner at `N=0` has not supplied the complete prefix required by any
particular `s`, so the unit-proxy failure is **not** by itself a formal
no-go for every actual-owner tail choice.

## Eliminating multiplicity for bounded shell indices

For an actual source zero `rho` covered by shell prefix `s`, the formal
height condition `2*gamma <= 2^(s+1)` implies
`gamma <= 2^s < 2^(s+2)`. The definition of
`finiteHeightMultiplicity` therefore gives

```
m <= finiteHeightMultiplicity(2^(s+2))
  <= spectralMultiplicityConstant * 3^s.
```

The second inequality is the existing theorem
`finiteHeightMultiplicity_dyadic_le s` in
`C1SpectralSummability.lean`. Since `m>0`, this yields

```
beta_s/m >= 4/4^s,
F_actual >= (4/4^s) * H^4 gamma^12 q^(2n).
```

Thus, under the **changed named hypothesis of an actual source zero**
with `gamma>39`, the specific `n=0`, `q=2^-14` certificate cannot pass
its strict spectral-shell consumer at **any `s<=43`**:

```
(4/4^s) * H^4 gamma^12
  > 4 * 42^4 * 39^12 / 4^43
  = 154110573722506158973260864
      / 77371252455336267181195264
  > 1.
```

This is an exact conditional no-go for the named `n,q,s` certificate,
independent of the unknown multiplicity and correction selector. The
trial-162 height is not asserted to be an actual source zero. Shells
`s>=44`, other indices, and other tail estimators remain open; a shell
change also changes the complete prefix and its owner obligations.

## Decision

`TARGET-VALUE-TAIL-FLOOR`: the 2151–2154 `n=0` auxiliary gate fails the
registered unit tail proxy before any gate certification. A formal route
at `n=0,q=2^-14,gamma>39` must use `s>=44` for this certificate, or
change `n,q` or the tail method. More generally it must supply its real
`s,m` and check `F_actual`; changing `s` also changes the complete prefix
owner. Reopen with a different tail estimate that
beats the global-`C4/C2` floor, or with a same-owner gate at an index where
the actual multiplicity-aware budget closes. This is a selector-independent
necessary condition under the named theorem, not a producer Go.
