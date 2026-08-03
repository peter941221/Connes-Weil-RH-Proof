# Proof 796: Scaled-forcing recurrence guard

## Result

Proofs 794 and 795 give the exact recurrence

```text
N_(p::S) = (1-a_p)^2 N_S + c_(p::S)^2 F_(p,S),
```

and bound only the scaled forcing `c_(p::S)^2 F_(p,S)`. Proof 796 proves an
axiom-clean scalar counterexample showing that those two facts, even together
with positivity of the lower factor and a uniformly bounded normalized
endpoint, cannot imply a uniform bound for the raw endpoint.

Take

```text
c_n = 2^(-n),
K_n = 4^n,
N_n = c_n^2 K_n = 1,
F_n = K_(n+1) - K_n.
```

Then every `c_n` is positive, and exactly

```text
N_(n+1) = (1/2)^2 N_n + c_(n+1)^2 F_n,
|c_(n+1)^2 F_n| = 3/4 <= 1.
```

Nevertheless `K_n = 4^n` is unbounded.

```text
bounded normalized endpoint + bounded scaled forcing
                         |
                         v
                  recurrence is stable
                         |
                         X
                         |
                 uniform raw endpoint bound
```

## Why It Matters

The recurrence coordinate in Proof 794 is correct, and Proof 795 is a valid
support-first estimate for its exact completed forcing. The counterexample
shows that one cannot divide the recurrence by the lower factor, apply a
discrete Gronwall argument, and claim lower-factor-square trace decay.

The missing result must constrain the raw completed forcing through the actual
CCM24 real-line Hardy/prolate kernel. It must provide a source-specific
cancellation or a genuine raw summability theorem before an absolute value.

## Lean Owners

```text
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSCausalMarkovScaledForcingRecurrenceGuard.lean

ConnesWeilRH/Dev/
  CCM24FiniteSCausalMarkovScaledForcingRecurrenceGuardAudit.lean
```

The audited declarations are:

```text
scalarNormalizedEndpoint_succ_eq_contract_add_scaledForcing
scalarScaledForcing_abs_le_one
scalarRawEndpoint_not_uniformly_bounded
scaledForcingRecurrence_has_unbounded_raw_witness
```

## Boundary

This is an abstract scalar guard. It does not model the CCM24 completed
outer/reflected-second-support/prolate kernel, and therefore does not refute a
source-specific Gate 3U proof. It proves only that Proof 795 cannot close
Gate 3U by recurrence bootstrap alone.
