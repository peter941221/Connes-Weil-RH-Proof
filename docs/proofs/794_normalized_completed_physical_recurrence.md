# Proof 794: Normalized completed physical recurrence

## Result

Write

```text
c_S = finiteEulerLowerFactor(S)
N_S = c_S^2 K_S.
```

For a prepended visible prime with `a_p = p^(-1/2)`, Lean proves the exact
stable recurrence

```text
N_(p::S)
  = (1-a_p)^2 N_S
    + c_(p::S)^2 [
        - Re Tr(C_(p,S))
        + Re Tr(R_(p::S) - R_S)
      ].                                                (794.1)
```

The forcing term is still the full completed Markov/remainder combination.

## Why It Matters

`N_S` is the lower-factor-square physical scalar appearing in the Gate 3U
contract.  Equation `(794.1)` avoids dividing by `c_S` and exposes a genuine
one-step contraction `(1-a_p)^2`.

```text
N_S -- multiply by (1-a_p)^2 --> N_(p::S)
                                      ^
                                      |
                           completed forcing only
```

The remaining analytic theorem is a support-first, detector-specific bound
for this complete forcing term.  A uniform norm of the normalized endpoint,
or separate bounds on its physical branches, is still insufficient.

## Lean Owner

```text
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSCausalMarkovCompletedPhysicalDifference.lean
```

Key declaration:

```text
normalizedCompletePhysicalHermitianTrace_cons_eq_contract_add_forcing
```

## Scope

The recurrence gives a correct coordinate for the open analytic estimate.  It
does not supply that estimate or close Gate 3U, the finite-S sign, Burnol's
identity, or RH.
