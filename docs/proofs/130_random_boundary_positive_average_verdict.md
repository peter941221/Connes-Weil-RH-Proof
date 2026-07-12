# Random-Boundary Positive-Average Verdict

Date: 2026-07-12

Status: two positive averaging variants rejected exactly. RH remains unproved.

## Candidate D: average the half-line boundary

Let `P_s` project onto `[s,infinity)` and average positive owners against a
probability measure `mu`:

```text
B_mu = integral_s B(P_s) d mu(s).
```

For a translation-invariant same-square convolution `C_h`, the trace of one
`m log(p)` crossing is independent of the boundary location. Translating both
half-lines by `s` gives

```text
Tr(C_h* C_h J_(m log p,s))
  = m log(p) F_h(m log(p)).
```

Therefore

```text
integral_s Tr(C_h* C_h J_(m log p,s)) d mu(s)
  = m log(p) F_h(m log(p)) * mu(total).
```

Preserving one archimedean bulk forces `mu(total)=1`. Boundary randomization
does not change the factor `m`, so it cannot manufacture the required `1/m`
before crossing length.

## Candidate E: average the crossing scale

Next average translations by `tau log(p)` with a positive probability measure
`nu`:

```text
integral_tau m tau log(p) F_h(m tau log(p)) d nu(tau).
```

To equal the Weil atom

```text
log(p) F_h(m log(p))
```

for every compact smooth square `F_h`, the measure-valued evaluation identity
would have to be

```text
integral_tau m tau delta_(m tau log p) d nu(tau)
  = delta_(m log p).                                   (R.1)
```

Distinct point evaluations on compact smooth functions are linearly
independent. Equation (R.1) therefore forces `nu` to be supported at
`tau=1`, with mass `1/m`. A single probability measure cannot have total mass
`1/m` simultaneously for every `m>=1`.

Allowing an `m`-dependent measure would assign a different owner to every
prime power and destroy the common same-object trace. Allowing a signed measure
could cancel masses but loses positivity.

## Verdict

```text
random boundary location: coefficient unchanged
random crossing scale: incompatible masses 1/m for all m
signed averaging: loses positivity
prime-power-dependent averaging: loses one common owner
```

Positive geometric averaging cannot supply the Euler logarithm coefficient.
The `1/m` must be present in one common noncompact operator before the
half-line crossing trace is taken.
