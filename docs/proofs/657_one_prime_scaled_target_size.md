# Proof 657: one-prime scaled target size

## Result

Proof 638 gives `||C_(p,[])|| <= 244 q_p ||detector||`. Proof 657 proves the
exact scalar comparison

```text
q_p / s_p = sqrt(q_p) (1 + q_p) <= 2
```

and therefore closes the Proof 655 size gate for the empty suffix:

```text
||s_p^(-1) C_(p,[])|| <= 488 ||detector||.
```

The bound is uniform in every visible prime.

## Boundary

This is only the one-prime subfamily `S=[]`. It says nothing about arbitrary
suffixes, and it does not construct the Proof 656 two-step factor.

## Lean Owners

```text
ConnesWeilRH/Source/CCM25Concrete/
  ...AntiresonantInteriorOnePrimeScaledTargetSize.lean
ConnesWeilRH/Dev/
  ...AntiresonantInteriorOnePrimeScaledTargetSizeAudit.lean
```

The focused audit passed with `3442` jobs; the combined Proof 650--659 audit
also passed with `3454` jobs. Audited declarations use exactly
`[propext, Classical.choice, Quot.sound]`.
