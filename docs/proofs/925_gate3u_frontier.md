# 925 — Gate-3U frontier reset: what is closed, what remains, and the exact next lever

Date: 2026-08-10. Type: route-state convergence record (repo-verified source reading,
numeric reproduction performed this turn). No new axiom, no `sorry`. RH NOT claimed.

## 0. One-line answer to "3U 还剩多少"

The **finite-band (route-A) Gate is CLOSED axiom-clean**; the **infinite-carrier Gate is
OPEN**, and it splits into exactly two independent pieces — (1) the analytic operator
identity `(I-P)(F+D)=0` on non-empty finite-prime families, and (2) the carrier/trace-layer
seam that would let the tail's closed operator-norm bound feed a trace bound at the gate
carrier. Neither is constructible on the current carrier without (1) a genuinely new
analytic bound or (2) the authorized Hilbert/trace-class carrier re-point.

## 1. Numeric reproduction (this turn, fresh env)

Fresh `numpy 2.5.2` / `scipy 1.18.0` venv. Ran the committed probe
`docs/proofs/884_outer_sonin_scale_sweep_probe.py` verbatim:

```
regression anchor logla=0:
  n=600  L=8   outer=0.6245   (matches 824's 0.6245 exactly)
  n=1200 L=8   outer=0.6182

Sonin-scale sweep (logla in [-2,+2]):
  min 0.6090 (logla=-2.0)   max 0.6199 (logla=+2.0)
```

Reading (unchanged from 884): the outer leakage channel `(I-P)D` is pinned ~0.61–0.62
across the whole physical scale line and never decays; this is a **robust case-weighted
negative** for the outer channel alone, but it is **not** a proof and **not** the full
`L = F + (D-J)` (the F‑term is not reached; see §3).

## 2. What is CLOSED (source-verified, axiom `[propext, choice, Quot.sound]`, 0 sorry)

- **Route-A finite-band Gate** (`Dev/RouteATailBandBound.lean`): `bandTerminalGate` bounds
  the diagonal real trace by band cardinality times closed operator-norm bounds (support
  piece + tail `rawRenewalTailNormConstant * exp(-B/4) * prod`), assembled via
  `inverseLowerFactorPhysicalRenewalTrace_split_bound`, consumed via
  `canonicalRealGate3U_at_of_tailNormBound`. WSL green, zero sorry.
- **Nil-side dichotomy** (`Dev/Gate3UDichotomyProbe.lean`, 2026-08-09): `visiblePrimes=[]`
  → leakage `=0`; `gate3UDichotomyObligation` is the OPEN converse (nonempty → non-zero).
- **Biorthogonal algebra** (all axiom-clean, in `CCM24FiniteSEndpointContractionGuard` +
  `...PhysicalLeakage`): `J†D_S = I`, `P D_S = J`, the sharp equivalence
  `‖D_S‖≤1 ↔ leakage=0` via `‖D_S‖=1 ⟺ L=0`, and the identity
  `L = sourceActualBandForwardCoframe + sourcePhysicalCoframeLeakage`.

## 3. Exactly what remains (the two-piece reset)

**Gate 3U infinite-carrier / canonical form** is the single premise
`‖sourceActualBandForwardEndpointCoframe λ (canonicalFamily owner)‖ ≤ 1`.
By the proven `‖D_S‖≤1 ↔ L=0` reformulation this is exactly:

```
L = sourceActualBandForwardCoframe λ fam + sourcePhysicalCoframeLeakage λ fam = 0
  = (E-band)∘T⁻¹∘J + (D - J) = 0        on every u in the source-Sonin carrier.
```

Decomposed (Proof-717 / 872):
- **P-component**: `P·(F+D-J) = 0` — closed. (P = sourceSoninProjection.)
- **(I-P) component**: `(I-P) F = -(I-P) D` — **OPEN**; the single analytic identity.

**Piece 1 — operator identity (the hard bottom).** `(I-P)F = -(I-P)D` on the off-Sonin
column. Numerics show `(I-P)D ≈ 0.61` robust, so the F‑term would have to cancel exactly.
The F‑term `F = (E_radial − sourceSonin R0) ∘ T⁻¹ ∘ J` contains the **exact Sonin
intersection** `R0` (AGENTS 818/819), which a finite grid cannot realize. Hence no honest
numeric probe reaches the deciding quantity; this is a genuine analytic operator identity,
not a merely-large constant artifact.

**Piece 2 — trace/seam layer.** Even with the op-norm + exponential tail decay
(`norm_...TailProg_le_const_exp`), turning it into `|Re Tr(tail)| ≤ bound` at the Gate
carrier `sourceSoninCarrier` requires an `IsTraceClassAlong` certificate there; the
library trace-class bundle lives on `globalBasis`/`finiteSCarrier`, and the `LegacyTestEquiv`
full-bijection seam (A1/A2) blocks the transfer (docs/860). This is the architectural
"carrier re-point" front, now authorized under AGENTS §3b (2026-08-09).

## 4. Route judgment

- **Route is NOT closed; it is refuted-at-grid for the outer branch, but not structurally
  closed nor refuted in Lean**: the deciding `(I-P)F` term is not numerically reachable and
  the exact identity remains OPEN.
- No non-empty finite prime family is proven annihilating (`|D† (F+D-J)|=0`).
- The honest close condition: prove **or formally refute** `(I-P)F = -(I-P)D`. Absent
  new analytic input, the route should be treated as a real open bottom, not a winnable
  Lean-assembly leaf.

## 5. Next safe actions (ordered)

1. Establish whether `(I-P)F` and `-(I-P)D` are confirmable at any reachable concrete family — needs either the exact `R0` (beyond grid) or a genuinely new band-limited
   analysis of the forward term.
2. If no identity is reachable, formally restate Gate-3U as the two-part obligation and
   pursue the **carrier re-point** (authorized) so the finite-band closure + a trace
   certificate covers the infinite-carrier tail.  This is the concrete, large-but-manned
   path to actually *advance* (not merely exit) the Gate.
3. Keep `Gate3UDichotomyProbe` as the nil-side reference; only add a nonempty verdict if
   a genuine proof (or refutation) lands.

RH NOT claimed. No new axiom, no `sorry`.


