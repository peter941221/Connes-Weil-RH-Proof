# Record 3137: Route-B adaptive-owner prime-index readback

Date: 2026-10-27.

Status: Lean-verified canonical readback; no numerical manifest and no gate
claim.

Record 3137 pins the exact 3117 powered owner used by the adaptive route and
exports the membership rule for its actual prime-power index set:

```text
q in globalPrimeIndexSet(owner.convolutionSquare)
    iff IsPrimePow q
       and finitePrimeTermComplex(owner.convolutionSquare, q) != 0
```

It also proves equality with the canonical selected-owner support data. A
future JSON certificate may therefore be consumed only after its listed prime
indices are checked against this exact Lean owner; a support cutoff or a larger
prime-power closure is not an acceptable substitute.

The declarations do not enumerate the set for a numerical `rho`, do not prove
omitted-term bounds, and do not establish a gate margin, `fullWeilPositivity`,
Producer GO, SourceRH, or RH.

Evidence:

- `ConnesWeilRH/Dev/C1RouteBAdaptiveOwnerReadback3137.lean`
- `ConnesWeilRH/Dev/C1RouteBAdaptiveOwnerReadback3137Audit.lean`
- `scripts/routeb_adaptive_owner_readback_audit_3137.py`
- `results/3137_routeb_adaptive_owner_readback_audit.json`

The 3136 certificate contract is a downstream consumer of this anchor. A
manifest may not be marked ready merely because its prime list is sorted: the
owner identity and the exact selected-owner index-set readback must be checked
first.
