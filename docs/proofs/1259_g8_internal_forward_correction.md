# 1259 - G8 internal forward correction

Date: 2026-09-10.

Status: `FORMAL-STRUCTURAL-CANDIDATE`; no `qw` sign or RH claim is made.  The
consumer remains the healthy-`CompactLog`, detector-specific B5 route.

## 1. Exact construction

Let `M` be the finite Euler metric coframe, `F` the actual-band forward
coframe, and `W_g` the selected positive convolution detector.  The physical
endpoint coframe is definitionally `E = F + M`.  The G8 leaf now defines

```text
P_g,S       = E† W_g E
K_forward   = F† W_g M + M† W_g F + F† W_g F
```

and proves the exact identity

```text
P_g,S = M† W_g M + K_forward.
```

The first summand is the existing G8 metric Gram; every compensating term is
inside the positive endpoint kernel.  No external subtraction is introduced.

The same leaf also proves `P_g,S` positive by `adjoint_conj` from detector
positivity.

## 2. Formal evidence

The declarations are `g8PhysicalEndpointGram`,
`g8InternalForwardCorrection`,
`g8PhysicalEndpointGram_eq_metricGram_add_internalForwardCorrection`, and
`g8PhysicalEndpointGram_isPositive` in
`ConnesWeilRH/Dev/C1G8AdjointShearGram.lean`.  The paired audit prints exactly
`[propext, Classical.choice, Quot.sound]` for all four declarations; the
focused retry-4 log has 3922 jobs, zero `error:` lines, and zero `sorryAx`.

## 3. Remaining obligation

This is the first formal internal-correction candidate, not the finished
readback.  No theorem yet identifies `K_forward` (or the positive endpoint
trace) with the finite visible-prime Euler boundary or proves its cutoff
remainder tends to zero.  The next mathematical step is to derive that trace
identity for this concrete `E`, not to add another wrapper.

RH is not claimed.
