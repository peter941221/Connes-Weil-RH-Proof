# 1508 — the gate as an ambient Hilbert–Schmidt normal form (WO-S3, 1503 §2)

**Status: FORMAL, GREEN first content try.** `C1G8R3GateAmbientNormalForm.lean`
(+ paired Audit) lands the ambient column-sum surgery promised by record
1503 §2. Acceptance: `build-logs/0916_gate_ambient_try3.log`, 3956 jobs,
zero `error:` lines, both audited declarations print
`[propext, Classical.choice, Quot.sound]`, zero `sorryAx`.

## What is proved

The gate `(★) Summable i, ‖(J† ∘L C ∘L J)(e_i)‖²` on the source Sonin
carrier is equivalent to the Hilbert–Schmidt column square-sum of the
ambient projection-conjugate on the global logarithmic carrier:

```text
(★)  Summable i, ‖(J† ∘L C ∘L J)(sourceBasis i)‖²
  ↔ Summable j, ‖(P ∘L C ∘L P)(globalBasis j)‖²
```

for any named source basis and any named ambient basis
(`gateAmbient_iff_sourceGate_squareSum`). Since record 1498 identifies
`hSurvivor` with (★) and record 1502 identifies the endpoint gate with (★),
this theorem makes the single remaining square-sum a statement about one
explicit ambient operator: **the gate is HS of `P C P` on the ambient** —
the sharp normal form 1503 §2 preregistered.

Supporting lemmas: the pointwise projection identity `P(Je) = Je`
(`gateAmbient_projection_apply_inclusion`), the pointwise norm identity
`‖Pw‖ = ‖J†w‖` (`gateAmbient_norm_projection_eq_norm_adjoint`), and the
operator identity `P C P = (J ∘L (J† ∘L C ∘L J)) ∘L J†`
(`gateAmbient_projectionConjugate_eq_lifted_comp_adjoint`).

## How (no analysis)

Both directions are single applications of the committed square-sum
transfer `PositiveTrace.summable_normSq_precomp` plus pointwise algebra:

* gate → ambient: lift the detector by the isometric `J`
  (`Summable.congr` via `‖Jz‖ = ‖z‖`), then precompose by the bounded `J†`;
  the composed operator is definitionally `P C P` by `JJ† = P`
  (`sourceInclusion_comp_adjoint`).
* ambient → gate: precompose `P C P` by `J`; the inner projection dies
  pointwise (`P(Je) = Je`), and the remaining projected norm equals the
  adjoint readout `‖J†(C J e)‖` — exactly the gate summand.

No estimate for the gate is claimed; the openness is structural
(1503 §1–§2). RH not claimed.
