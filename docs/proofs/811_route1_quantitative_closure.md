# Route 1 (quantitative) closure: `||S∘T†∘R||` needs a genuinely new estimate

Date: 2026-08-06
Status: closed (analytic bottom located, not a library-assembly task)
Branch: `proof/gate3u-completed-readout`
RELATED: `docs/proofs/808_metric_wall_outer_channel_budget.md`,
`docs/proofs/810_strong_route_index_survey.md`

## Result

Route 1 proposes to close the real Gate by a quantitative decay of the
transport-radial off-diagonal block,

```
‖ S ∘ T† ∘ R ‖ ≤ δ
```

where `R` = radial-support projection, `S = I − R` = its complement, and
`T†` = adjoint of the finite Euler transport
`T = ∏_p (I − p^(−1/2) U_{−log p})`.

This bound is **not present in the library**, and it is not obtainable by
re-assembling existing facts. All three "borrowed" routes (2, 3, and this one)
reduce to it.

## 1. The four transport blocks

Writing `P = R` (radial) and `S = I − P` (complement), the transport adjoint's
action on the whole carrier splits into four cross-blocks. Two are already
closed:

```
matrix form of T† on (radial ⊕ complement):

          radial      complement
radial     [   *         0    ]   ←  P∘T†∘S = 0   (committed, 67c4fe1)
comp       [   WALL       *    ]   ←  S∘T†∘R = ??  (the open wall)
```

- `P∘T∘S = 0` and the mirror `P∘T†∘S = 0` are done (library + committed).
- The other two diagonal blocks `R∘T†∘R`, `S∘T†∘S` are bounded by `‖T†‖`
  (finite, = `upperFactor`).
- The open content is exactly `S∘T†∘R` — whether the adjoint transport drags a
  radial input out of the radial subspace.

## 2. Why no library identity bounds it

- The transport is a Mellin-place product of `I − p^(−1/2) U_{log p}` (coordinate
  shifts by `±log p` in the logarithmic `t = log lambda` coordinate, see
  `CCM24EulerTransport.lean:94-98`). Its cross-block behavior against the
  Sonin–prolate radial subspace is genuinely oscillatory.
- The two in-library facts pin the blocks *around* the wall:
  - `S∘T∘R = 0` (forward preserves radial),
  - `R∘T†∘S = 0` (adjoint preserves complement).
  Neither touches `S∘T†∘R`.
- `tsum_normSq_precomp` (route-2) only ever bounds the *diagonal* series from
  `‖T‖`, not this cross-block.

So a `‖S∘T†∘R‖ ≤ δ` estimate is a new statement about the spectral interaction
of coordinate translations with the Sonin–prolate closure. It is not derivable
from the assembled library.

## 3. Judgment

- **Closed as a library task.** No Lean reassembly yields it; it is an analytic
  estimate (prolate-adjoint decay) not present in the repository.
- This is the same conclusion as `gate3u-right-energy-leakage-norm-bottom.md`:
  the only closures are (a) Proof 717 forward+physical cancellation, or (b) a
  genuinely new band-limited/operator estimate.

## 4. Handoff

- RH status: conditional (Gate 3U open).
- Declarations: none changed in Source.
- Next safe action: route-1 needs new analytic input; otherwise the frontier is
  the Proof-717 cancellation `forward + M = 0` (the RH equality itself).