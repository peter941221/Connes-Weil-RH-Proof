# Plan 022 Final Rejection

Date: 2026-07-11

Verdict: **rejected as an executable RH route.** The fixed double-Mobius
convolution is a genuine scale-stable numerical direction, but it is not an
independent producer. Its correlation with the optimal residual is created by
the full last dyadic shell of the old projection.

## 1. Constraint-Depth Test

For fixed `h_N`, compute the optimal residual only against `V_m`, with `m`
increasing toward `N`. At `N=4096`, `m=N/2` gives normalized angle about
`0.00269`; the full `m=N` gives `0.12684`. Most signal accumulates while adding
the high-dimensional shell `(N/2,N]`.

The exact update `u_N=r_(N/2)-r_N` contributes 46--84 percent of the final
correlation over tested dyadic scales. Its cosine with `h_N` stays around
`-0.25` to `-0.43`. The fixed direction tracks an unknown optimal shell update;
it does not generate that update.

## 2. Standalone Dictionary Test

Use only the explicit approximation space

```text
V_16 + span(h_16,h_32,...,h_N).
```

The squared distance stabilizes near `0.014256` through `N=65536`. It does not
tend to zero, while `distance^2*log N` increases. The fixed convolution family
is therefore not dense enough to prove RH on its own.

## 3. Rejection Mechanism

```text
fixed divisor convolution
  -> genuine positive numerical angle with r_N
  -> angle appears only after the complete optimal shell projection
  -> explicit fixed dictionary still has positive limiting distance
  -> any proof must recover the growing Schur/inverse-Gram geometry
  -> Plan 020 bottom returns
```

The numerical angle inequality itself is not disproved. The route is rejected
because it does not lower the mathematical dependency. No Lean API or RH root
change results.
