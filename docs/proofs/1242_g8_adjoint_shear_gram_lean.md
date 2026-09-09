# 1242 - G8 adjoint-shear Gram compression (Lean)

Date: 2026-09-09.

Status: `FORMAL-ALGEBRA`; no positivity-to-`qw` theorem yet. Consumer: the
healthy-`CompactLog`, selected-detector, same-owner B5 L4 gate.

The Dev leaf
[`C1G8AdjointShearGram.lean`](../../ConnesWeilRH/Dev/C1G8AdjointShearGram.lean)
defines the concrete ambient Gram candidate

```text
G^+_{g,S} = (I + N_S) W_g (I + N_S^*),
```

proves the ambient detector positivity and G8 positivity before any trace, and
proves the source-owner compression identity

```text
J^*G^+_{g,S}J
 = J^*W_gJ + J^*N_SW_gJ + J^*W_gN_S^*J
   + J^*N_SW_gN_S^*J.
```

The same leaf proves, without a trace cycle, that the second term is exactly
`finiteEulerTargetCommutatorResponse`. The existing physical leakage
factorization identifies the intended owner of the fourth term; no duplicate
wrapper was added after a Lean defeq recursion screen.

Audit evidence: build log
`/home/peter/rh/build-logs/1242_g8_adjoint_shear_retry22.log`. The log has
the success footer and zero `error:`/`sorryAx` lines; the audit prints only
`[propext, Classical.choice, Quot.sound]` for all five declarations.

This brick does not prove trace-classness, the `qw` limit, a sign, SourceRH,
or RH. The remaining task is the same-owner four-channel trace ledger, not
another interface.

RH is not claimed.
