# Proof 317 metric wall: the outer channel `(I−R)∘T†∘R` and how to break it

Date: 2026-08-05
Status: gate analysis — no new closing theorem, one dead-end reverted
Branch: `proof/gate3u-completed-readout`

## 1. The single open hypothesis behind every Gate-3U closer

The finite library already contains two full completions of the canonical Gate,
and both unpack to the **same** hypothesis:

```
hcancellation :  sourceActualBandForwardCoframe + sourcePhysicalCoframeLeakage = 0
```

| Gate-3U closer | Contract | Unpacks to |
|----------------|----------|-----------|
| `canonicalRealGate3UAt_of_completedKernelRightEnergy` (adjoin energy gate) | `rightEnergy ≤ majorant` | via `…_le_of_forward_add_physicalLeakage_eq_zero` ⟹ `hcancellation` |
| `lowerFactorGauged_trace_norm_le_of_forward_add_physicalLeakage_eq_zero` (cancellation gate bridge) | `‖trace‖ ≤ 2·majorant` | direct ⟹ `hcancellation` |

And `hcancellation` is exactly the Proof-317 midpoint `‖endpoint‖ ≤ 1` through
`norm_sourceActualForwardEndpointCofactor_le_one_iff_forward_add_physicalLeakage_eq_zero`.

> **Conclusion: every closing of `canonicalRealGate3UAt` is one hypothesis short,
> and that hypothesis is the off-Sonin cancellation `(I−Q)(forward + M) = 0`.**

## 2. Why the "bound-the-participant" route was a dead end

I had pursued
`canonicalRealGate3UAt_of_lowerFactorSq_completePhysicalHermitianTraceBound`, whose
premise `hbound` bounds the diagonal sum `Σᵢ Re(pairing(bᵢ,bᵢ))`. The target object
`finiteEulerCausalHardyProlateCompletePhysicalBoundaryPairing` is a per-point recoil
`−⟨row(D b) , transported(K b)⟩`. The Cauchy–Schwarz split
`norm_completePhysicalBoundaryPairing_le_row_mul_kernel` bounds one term as
`‖row∘D b‖ · ‖transport∘complement∘kernel∘inclusion b‖`.

That lemma is true but **disposable** for the Gate:

- It bounds a per-pair **real scalar**; the Gate needs the **adjoint-operator trace**.
  Different invariants.
- `rho` indexes an infinite L² source basis, so the diagonal is a genuine infinite
  sum. Turning the per-pair bound into an infinite-sum bound needs an l²–CS bridge
  whose input `Σᵢ‖…‖² ≤ …` is exactly the norm bound we do not have.
- The pre-existing rightEnergy route already performs that infinite-sum trace bound,
  with all inner machinery written.

So I reverted the lemma and its audit line. The library is now a clean, minimal,
honest bundle: **the whole Gate stays open unless `hcancellation` closes.**

## 3. What `hcancellation = 0` actually is

Unfold the addends (each a done, axiom-clean library identity):

```
forward = (I−Q)∘(N∘J)        N = normalized finite-Euler inverse, J = source inclusion
M       = T†∘D              D = (F∘G) dual frame, F radial (R∘F = F)
Q = source-Sonin projection, R = radial-support projection, B = R−Q
```

The library isolates channels but never annihilates the residual; the off-Sonin sum
splits orthogonally:

```
forward + M =  (I−R)∘M      +   ( forward + (R−Q)∘M )
            =  (I−R)∘T†∘D   +   ( forward + B∘M )       outer channel   +   source-band channel
```

With `R∘D = D` the outer channel collapses to the single honest operator
`(I−R)∘T†∘R` — whether the transport adjoint drags a radial input out of the radial
subspace. There is no loop-free identity forcing it to 0; only the `R(Rx)=Rx` auto
tautology holds. That operator and its annihilation *is* the wall.

```
      radial input x → R → stays in radial subspace
        │
        ▼  T† (adjoint transport)
      does it leave the radial subspace?
        │
        ▼  (I−R)
       non-trivial content
```

## 3. Why a norm-only bound cannot close it

The in-library transport controls are one-sided only:

| arrow | bound |
|-------|-------|
| `T`       | `‖T‖ ≤ upperFactor(family)` |
| `lowerFactor • T†` | `‖lowerFactor•T†‖ ≤ 1` |

`hcancellation` needs the transport adjoint to *preserve* the radial subspace. The
available bound sits on the **scaled** arrow; it yields only

```
‖(I−R)∘T†∘R‖ ≤ ‖T†‖ ≤ upperFactor(family)
```

which is live, not 0. So `hcancellation` cannot be derived by norm algebra alone.

## 4. Actionable routes to actually break the wall

1. **Transport-adjoint radial behavior (vanilla).** Prove a quantitative
   `‖(I−R)∘T†∘R‖ ≤ decay` and push the outer channel into the budget; then split
   `hcancellation` into two cancelling factors. Requires a new estimate on the
   prolate adjoint — not in-library.

2. **Footprint + trace (no `=0` needed).** Show both factor sums
   `Σ‖(row∘D)(bᵢ)‖²` and `Σ‖kernel∘K(bᵢ)‖²` are **finite** (not merely bounded to 0)
   from Sobolev decay of the basis. If true, the infinite diagonal of
   `Re` is summable, `hbound` is a real finite `bound`, and the Gate closes *without*
   ever needing the metric collapse. This is the only option that avoids asking for `=0`.

3. **The theorem (honest).** Prove `(I−R)∘T† = 0` on the radial image — the transport
   adjoint maps radial to radial. That alone makes `hcancellation` true and the Gate
   closes.

## 5. Status of the library after this change

- Reverted: the per-pair micro-bound `norm_completePhysicalBoundaryPairing_` and its
  audit entry (wrong invariant for the Gate).
- Kept: the probe theorem bundle that pins the wall, all axiom-clean
  `[propext, Classical.choice, Quot.sound]`:
  - `radialSupportProjection_comp_finiteEulerDualFrame`  (`R∘D = D`),
  - `sourceOuterCoframeLeakage_eq_radialComp_comp_transportAdjoint_comp_dualFrame`
    (outer channel = `(I−R)∘T†∘D`),
  - `norm_finiteEulerTransportAdjoint_le_upperFactor` (`‖T†‖ ≤ upperFactor`).
- Decision: the open frontier is `hcancellation`, not a missing bound lemma. All
  ongoing work targets options 1–3 above.