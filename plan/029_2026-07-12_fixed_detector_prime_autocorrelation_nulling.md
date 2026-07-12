# 029 Fixed-Detector Prime Autocorrelation Nulling

Date: 2026-07-12

Status: rejection-first research candidate.

## Objective

Complete Plan 028's full-QW sign without treating finite-prime translations as
a compact operator. Construct one Xi/M4 detector whose genuine convolution
square vanishes at every visible prime-power translation.

## Execution order

1. Derive the exact finite matrices `A_n` for a translated-bump frame.
2. Test the smallest support windows for positivity/definiteness obstructions.
3. Prove or reject simultaneous quadratic nulling on the kernel of the linear
   orbit, triple-zero, and M4 rows.
4. Only if the finite systems survive, study growth as the Xi cutoff expands.
5. Do not create a route owner before a uniform construction is proved.

## Decision rule

Reject immediately if one visible prime matrix is positive definite on every
linear-constraint kernel retaining the target orbit sign. Otherwise continue
to the growing-cutoff dimension/count gate.

Stronger gate: autocorrelation is continuous under the Xi quotient's `L2`
cutoff convergence. Exact prime nulling along the cutoff sequence forces the
noncompact quotient itself to have zero autocorrelation at every prime log.
No such structural identity is known. See proof 101.
