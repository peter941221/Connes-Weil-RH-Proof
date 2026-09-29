# 2230 — Operand provenance convention and complete-owner transfer preflight

Date: 2026-09-29

Consumer: the healthy `CompactLog` B5 selected detector, actual
`sourceNontrivialZeroSet` owner, same-owner `qw >= 0` producer.

This is a desk record. It fixes the operand-convention question that every
numeric artifact 2217--2229 already relies on, and it inventories the
complete-owner transfer ladder with the exact quantitative facts already on
the shelf. It adds no numeric claim of its own and makes no RH claim.

## Decision 1 — discrete-defined operand convention (A)

The finite construction evaluated by the numerical terminal is defined on the
stored binary64 operand tuple

```text
K = 30 (exact integer), a, theta, node, x, c, w   (binary64)
```

Convention A: those stored binary64 values are *exact* operands. Every
interval and rounding certificate (2225--2229) bounds the finite sum
`sum_f c_f sum_x w_x exp(q(K, a, theta, node, x))` for exactly that tuple.
The ideal-object-to-stored-tuple gap is a separate construction ledger, listed
below as ladder item 2; it is not zero and it is not contained in the
exponent-radius charge.

Why A and not B (ideal operands with the cast error charged into the
interval): B needs a cast-radius ledger per operand kind (`a`, `theta`,
`node` from the owner definition, `x`, `w` from the quadrature rule, `c` from
the coefficient solve). That is the same ledger as A's construction error,
but with the accounting smeared into every one of the 1.944360e6 terms.
Convention A keeps the discrete referent unambiguous, reproducible, and
pinnable, and concentrates the unpaid work in one visible place.

The pin is real, not verbal:

```text
results/2229_operand_cache.npz   md5 c78a0342fad8ac0166c23d01f653f666
size 18434906 bytes              built once via MODE=build
call chain identical to the 2225 evaluator:
  nodes, fam, A0, _b, b_corr = parent.v.r.matrices(parent.v.r.M_REF)
  coeff = np.linalg.solve(A0, b_corr)
  xw    = phi_weights(a, panels=6, m=parent.M)
```

Drift control: under the cache path, node 2 family 0 reads
`3.60315281153439503e-09`, versus the 2228 in-process reading
`3.603152811534377e-09`. The cache value is larger by `5.0e-16` relative,
which matches the designed outward inflation (the Simpson panel factor is
inflated by 4 binary64 steps, `4.4e-16` relative), so no material operand
drift is visible between the two builds at this resolution.

## Decision 2 — transfer ladder inventory

| item | status | record | number |
| --- | --- | --- | --- |
| 1. all-30-node outward envelope | executed as 2229 | 2229 | max node charge (see 2229) |
| 2a. operand construction ledger | OPEN | 2199, 2200, 2201 | solve/grid generation error unpaid |
| 2b. finite-sum accumulation | closed per-term; stitch priced | 2229 | MPFR RNDU per term; family stitch outward to first order |
| 3. uniform charge vs budget | priced | 2231 | vs `6.2550323e-05` |
| 4. complete-owner transfer | OPEN | 2119, 2134, 2157, 2197 | see below |
| 5. strict signed margin | OPEN | 2197 | `1.675397327895099e12` anchor |

Item 2a in detail, operand by operand:

- `K = 30` exact integer; no error.
- `a`, `theta`: family literals from the owner construction chain
  (2187/2196). Exactness of the stored literals against their definition is
  unaudited paper work, not floating-point error.
- `node`: the 30 owner node positions come from the same
  `matrices(M_REF)` call; their exactness against the owner definition is
  the 2119 transfer question, not a rounding question.
- `x`, `w`: quadrature abscissas and weights from `phi_weights`/`leggauss`.
  Record 2200 refined the *rule* error; the binary64 generation error of the
  abscissas/weights themselves is uncharged.
- `c`: the `np.linalg.solve` coefficient vector. The solve-error budget
  interfaces exist (2199) and the enclosure preflight is 2201; neither is a
  certified outward coefficient box yet.

Item 2b in detail: the per-term chain is MPFR RNDU into per-family
accumulators and is outward. The node-level stitch
`total = UP(total + gl + sim)` uses two binary64 roundings (each at most half
a spacing down) followed by one `nextafter` step up, so the stitch is
outward to first order; the artifact carries the honest nonclaim instead of
a proof, and a one-line strengthening (three-step up-inflation, or MPFR
family accumulation) is available for the successor record.

Item 4, complete-owner transfer, four named obstructions with their numbers:

- cardinality (2119): formal owner upper bound `3002.5554464806` nodes vs the
  largest screened compact family of `62` nodes, ratio `48.43x`, at
  `rho = 0.945 + 39.25244858548658 i`, `N = 0`. The current Jensen/growth
  interface does not justify any 30--62 node ladder for the complete owner.
- near-pin derivative floor (2157): support plus interpolation targets cannot
  give a separation-free uniform derivative budget;
  `derivativeCost >= 4 exp(-X S)/(delta X L^2)` diverges as the pin-target
  distance `delta -> 0`. An owner-dependent separation bound or a signed
  mechanism avoiding the derivative seminorm is required.
- evaluator horizon (2134): the `m = 6400` sampled tail is trusted only to
  the measured horizon; the `500..550` band reading `2.2280960477922288e30`
  is the alias regime, not a tail estimate. A transfer must prove the trust
  horizon exceeds the required shell boundary or replace the sampled tail by
  an analytic vertical-decay bound.
- low-shell side (2197): the direct-product screen gives high-shell budget
  upper `3.691230708643563e9` `= 0.0022031972041408675 x` the candidate
  signed-margin anchor `1.675397327895099e12`; the mechanism retains signed
  cancellation, but the outward enclosure of the base/correction functions,
  their second derivatives, and the coefficient solve is still unpaid. The
  sampled lower screen (2195) gives `B_lower = 91406.0190223267` and
  `1.103564355e8 = 6.58688e-5 x` the same anchor, so both sides are live but
  only as screens.

## Status

`OPERAND-PROVENANCE-CONVENTION-RECORDED / OWNER-TRANSFER-OPEN`.

The convention A statement is the one that 2217--2229 artifacts cite in their
nonclaims; the transfer ladder above is the complete list of what a Go would
still have to pay. No producer or RH claim follows from this record.

Artifacts and provenance:

- `results/2229_operand_cache.npz` (local pin; md5 above; not committed)
- `scripts/routea_weighted_zero_q_mpfr_all_nodes_2229.py`
- predecessor evaluator `scripts/routea_weighted_zero_q_mpfr_interval_binding_2225.py`