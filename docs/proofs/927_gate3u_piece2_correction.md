# 927 - Route correction: carrier re-point (Piece 2) cannot close the infinite-carrier Gate

Date: 2026-08-10. Type: route-judgment correction (source-verified). No `sorry`, no new `axiom`. RH NOT claimed.

## 0. What this corrects

docs/925 and 926 listed two independent remaining pieces: the analytic operator
identity (Piece 1, `(I-P)F = -(I-P)D`) and a "carrier re-point / trace-seam"
(Piece 2). This memo records the sharper fact discovered this session:
**Piece 2 is necessary but not sufficient - a perfect carrier swap alone cannot
close the infinite-carrier Gate.** The infinite loop requires Piece 1 (real
analytic control of the leakage). Spending a large refactor on the carrier only
will not close the Gate; this is a convergent correction to avoid wasted effort.

## 1. Why a carrier swap cannot close it (in-repo structure)

The Route-A finite closure (`Dev/RouteATailBandBound.lean`, axiom-clean) proves:

```
|Re Tr_rho (Tail)| <= (card rho) * ||Tail||
||Tail|| <= C0 * exp(-B/4) * prod          (closed op-norm, TailBound:751)
=> |Re Tr_rho Tail| <= (card rho) * C0 * exp(-B/4) * prod
```

On the **infinite** carrier `rho` is the whole (non-Fintype) basis, so
`card rho = infinity` and the bound diverges unless every term decays. The
split is exact (`inverseLowerFactorPhysicalRenewalResponse = Support(B) + Tail(B)`):

- **Tail**: `||Tail||` decays as `exp(-B/4)`; on the natural band `rho = {D <= B}` (index count polynomial in B - a product over `Bool x Nat` per prime with displacement `(exponent)*log p`), the `card * exp(-B/4)` tail product tends to 0 as B grows, so the tail term is controllable.
- **Support**: `||Support||` does NOT decay in B. The support piece sums exactly
  the indices with `displacement <= B` with a finite fixed operator norm, so
  `(card rho) * ||Support||` diverges as the band extends to the full carrier.

Separately, the middle of every atom is an L2 Fourier multiplier
(`detectorOperator = A^+ A`), which is neither compact nor Hilbert-Schmidt nor
trace-class on the uncompressed carrier. So no `IsTraceClassAlong` certificate
can be granted on the infinite carrier by a carrier-only change (docs/860)
without new analytic input.

## 2. What would actually close it

1. An analytic identity for `L = 0` (Piece 1): a genuine bound/cancellation that
   yields `|D_S| <= 1` on the whole carrier. No in-repo mechanism forces it and
   numerics oppose it (probe 884), so this is the real, load-bearing, open step.
2. A trace-class / effective-summability structure on the support piece so
   `|Tr(Support)|` is finite on the infinite carrier; no such certificate exists.
3. The finite (route-A) gate is already closed (any finite band).

## 3. Recommendation update

- Do NOT lead with a 31-file carrier re-point to close the infinite Gate: it
  structurally cannot (this memo).
- The only genuinely closing investment is Piece 1: give the exact analytic
  statement/deposit for `(I-P)F = -(I-P)D`, or find a counterexample/refute.
- If Piece 1 has no mechanism and numerics oppose it, the honest conclusion is
  the infinite-carrier Gate is out of reach of the current definitions - a
  design-level blocker, not a Lean leaf.

RH NOT claimed. Decision-support, not a proof.
