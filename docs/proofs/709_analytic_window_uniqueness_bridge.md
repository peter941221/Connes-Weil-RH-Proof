# Proof 709: Analytic Finite-Window Uniqueness Bridge

## What is established

The finite-window premise in Proof 704 is reduced to a precise analytic
representative contract.  If `f` is analytic on the real line and is zero
almost everywhere on a nontrivial interval, then continuity upgrades the
interval statement to pointwise vanishing and the analytic identity theorem
gives `f = 0` globally.

The carrier conversion is also proved:

```text
globalL2ToKernelInterval a c b u = 0
        -> u = 0 a.e. on Icc (a-b) (c+b)
```

Combining both statements, an analytic representative of
`cc20GlobalLogConvolution h u` turns an exact kernel-interval zero into
`cc20GlobalLogConvolution h u = 0`, provided the interval is nontrivial.

The declarations are

```text
analytic_eq_zero_of_ae_eq_zero_on_Icc
globalL2ToKernelInterval_zero_implies_ae_zero_on_Icc
cc20GlobalLogConvolution_eq_zero_of_analytic_representative_of_kernelInterval_zero
```

## Remaining source obligation

Proof 709 does not construct the analytic representative for the actual
translated Sonin input.  It therefore does not yet instantiate Proof 704's
finite-window uniqueness premise, and it does not close Gate 3U, the finite-S
sign, Burnol's identity, or `_root_.RiemannHypothesis`.

## Verification

The Windows source was synchronized to the Ubuntu-24.04 WSL2 ext4 mirror.
The focused source target passed with `3288/3288` jobs.  The import-facing
audit passed with `3289/3289` jobs and all three declarations reported exactly
`[propext, Classical.choice, Quot.sound]`.  The `CCM25Concrete` aggregate
passed with `3982/3982` jobs, and the full repository build passed with
`4063` jobs.  No `sorry`, `admit`, or user axiom was added.
