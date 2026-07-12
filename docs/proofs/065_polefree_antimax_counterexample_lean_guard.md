# 065 Pole-Free Anti-Maximum Counterexample Lean Guard

Date: 2026-07-12

Result: the pole-free anti-maximum candidate remains rejected as a lower
producer. The finite countermodel is now checked by Lean, independently of
the numerical Arb probes.

```text
route obligation:
  justify the sign of <C, A_tilde^-1 C> at zero energy

old weak path:
  Dirichlet form + positive simple ground state + Morse index one
  -> A_tilde^-1 C < 0

new mathematical owner:
  none; the implication is false under these hypotheses

consumer to rewire:
  none

forbidden circular inputs:
  RH, a principal-pole anti-maximum theorem applied across the first gap,
  or an assumed continuum sign for the pole-neutral Weil scalar

smallest verification target:
  ConnesWeilRH.Dev.PolefreeAntimaxCounterexample

focused axiom audit:
  ConnesWeilRH.Dev.PolefreeAntimaxCounterexampleAudit
```

## Exact Countermodel

Use

```text
A    = [[-4,-1],[-1,1]]
A^-1 = [[-1/5,-1/5],[-1/5,4/5]]
C    = (1,1)
v    = (1,-1)
```

The checked identities are:

```text
A * A^-1 = I
A^-1 * C = (-2/5, 3/5)
<C, A^-1 C> = 1/5 > 0
<C,v> = 0
<v,A v> = -1 < 0
```

Thus the inverse scalar is positive even though the quadratic form is
negative on the `C`-orthogonal direction. This directly defeats the proposed
inference from a negative `C-perp` form to a negative pole-free resolvent
scalar.

## Lean Evidence

`PolefreeAntimaxCounterexample.lean` proves every displayed identity by
finite extensionality and `norm_num`. The import-facing audit reports only
`propext`, `Classical.choice`, and `Quot.sound`; it reports no `sorryAx` and no
project theorem premise.

The exact matrix is therefore a reusable guard against reopening the route
with the same abstract hypotheses. It does not assert anything about the
actual continuum operator beyond rejecting that implication.

## Consequence

The remaining continuum requirement is a genuinely new arithmetic/operator
identity proving the pole-neutral sign. Standard anti-maximum principles near
the principal spectral pole, Perron positivity, and index-one information do
not provide it. No Lean route owner or RH consumer is authorized.
