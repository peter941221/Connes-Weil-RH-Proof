# Proof 1245 — G8 adjoint cross channel

Status: FORMAL-ALGEBRA (Lean), 2026-09-10.

Taking the adjoint of the already-owned second G8 channel gives the third
channel without a trace cycle:

```text
J† W_g N_S† J = (J† N_S W_g J)†
               = (finiteEulerTargetCommutatorResponse)†.
```

The proof uses only `W_g† = W_g`, `adjoint_comp`, and the existing exact
target-response theorem.  The four source channels now have the exact
structural labels `baseline`, `response`, `response†`, and
`leakage-square`.

Audit evidence: `/home/peter/rh/build-logs/1245_g8_adjoint_cross_retry1.log`.
The owning module and audit build successfully with standard axioms only and
no `error:` or `sorryAx`.

This is still not the L4 producer: no finite-visible-prime trace identity,
uniform bound, cutoff limit, or `qw` readback has been proved.
