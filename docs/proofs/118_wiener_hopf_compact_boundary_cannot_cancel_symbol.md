# 118 Compact Wiener--Hopf Boundary Cannot Cancel The Prime Symbol

Date: 2026-07-12

## Weyl-Sequence Test

Consider on the positive half-line

```text
A=P(cI+V(D))P+K,
```

where `V(D)` is a bounded translation multiplier and `K` is compact after the
same smoothing used to define the trace owner.  Let `phi_R` be a normalized
wave packet of increasing width, frequency `t_0`, and support translated to
distance tending to infinity from the boundary.

Then

```text
||(P-I)phi_R|| -> 0,
<phi_R,V(D)phi_R> -> V(t_0),
<phi_R,K phi_R> -> 0.
```

The last limit follows because the translated packets converge weakly to zero
and compact operators send weakly null bounded sequences to norm-null
sequences.  Hence `A>=0` implies

```text
c+V(t_0)>=0
```

for every frequency `t_0`.

## Prime Consequence

For the finite-prime symbol in proof 115,

```text
inf_t V_S(t)
  =-sum_(p in S_f)2log(p)/(sqrt(p)+1).
```

Therefore no compact half-line correction reduces the sharp scalar
compensation.  In particular, a Toeplitz Schur complement or Hankel boundary
term may change discrete eigenvalues but cannot change the offending essential
symbol.

## Scope

This rejects compact boundary repair of a direct prime multiplier.  It does
not reject a noncompact pre-read-off identity that changes the principal
symbol and separately assigns its noncompact channel to the Weil main term.

```text
compact Wiener--Hopf repair: rejected
finite-section evidence: unnecessary
Lean owner: forbidden
RH: unproved
```

