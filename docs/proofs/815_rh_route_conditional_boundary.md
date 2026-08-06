# Proof-717 / Gate-3U conditional boundary: the machine reduces the whole RH to one open operator identity

Date: 2026-08-06
Status: verdict — the entire RH route in this repo is conditional on exactly one
open analytic identity, now pinned to its two orthogonal channels. Numeric probe
settled the outer channel *in isolation*; the live identity is unchanged.
Branch: `proof/gate3u-completed-readout`
RELATED: `810`, `811`, `813`, `814` (all under `docs/proofs/`).

## 1. The single open identity (one same-object cancellation, two channels)

The whole Proof-717 front — and therefore, in this repo, RH — reduces to one
operator equation on the metric dual coframe
`D = finiteEulerMetricCoframe = H·J·G⁻¹` (`CCM24FiniteSCoframeResponse.lean:37`):

```
‖endpoint‖ ≤ 1  ⟺  forward + physicalCoframeLeakage = 0
                ⟺  OuterChannel + BandChannel = 0
```

where, by the in-library channel split
(`CCM24FiniteSPhysicalCancellationChannelSplit.lean:80-101`):

```
OuterChannel = sourceOuterCoframeLeakage        = (I−R)            ∘ D
BandChannel  = forward + bandMetric              =  B·N·J  +  (R−R₀)  ∘ D
```

with
- `R   = radialSupportProjection` (support in `t ≥ log λ`),
- `R₀  = sourceSoninProjection`, and `sourceBandProjection = R − R₀` (so `D` splits as `R₀ + (R−R₀)` behind two orthogonal channels, `BandJetOrientation.lean:312`),
- `forward = sourceActualBandForwardCoframe = sourceBandProjection ∘ normalizedInverse ∘ J`,
- `G⁻¹ = restricted inverse Gram`, `H = T·T†`, `J = sourceInclusion`.

The two channels live on orthogonal subspaces (`(I−R)` vs `(R−R₀)`), so the
equation can only cancel if **each channel vanishes separately** — it is not a
free re-distribution across them.

## 2. What is already proved (the load-bearing lattice)

All of the following are proven (axiom-clean) in `Source/`; the sharpest is that
`forward + physical = 0` is a *single* same-object equation, not a branchwise
estimate:

| Object | Statute |
|--------|---------|
| `‖endpoint‖ ≤ 1 ⟺ forward + physicalLeakage = 0` | ContractionGuard:192-252 (proved) |
| Outer + Band channel split of the RHS | ChannelSplit:84-101 (proved) |
| `R₀ + (R − R₀)` orthogonal decomposition of radial | `JetOrientation:312` (proved) |
| `secondSupport + prolate = (R−R₀)∘D` (the rest of physical) | `ChannelSplit:42-60` (proved) |
| `forward + physical = 0` iff `endpoint = J` | (going inside Guard equivalence) |
| `forward + physical = 0` for `visiblePrimes = []` only | `MarkovRawBase:92-100` (proved) |

The empty-family case is fully closed. The **logically next case — any non-empty
finite prime set — is open**: no theorem in `Source/` gives `OuterChannel = 0`
or `BandChannel = 0` for a family with at least one visible prime. That is the
entire remaining gap.

## 3. Numeric probe: only the outer channel, in isolation

`814_wall_estimate_numeric_probe.py` measured the outer channel
`(I−R)∘T†∘R` (a stand-in for `(I−R)∘D`) on a uniform grid:

```
primes  OuterChannel operator norm
 {2}          0.70711
 {2,3}        1.30138
 {2,3,5}      1.98716
```

- value is logλ-independent (0.0 / 1.0 identical).
- on a decayed prolate-like radial `e_k`, `‖OuterChannel e_k‖` rises to the flat
  norm → the outer channel alone does not decay.

Two full-gate grid reconstructions bracketed the *second* channel but did not
decide it:
- naive `G⁻¹` (full grid) → `~3×10¹⁴` (Gram near-singular; off-carrier blow-up,
  not a fact);
- carrier-truncated `G⁻¹` with grid band `= I−R` → `0` (**annihilates `D` by
  construction**, since the exact `R−R₀` band is not reproduced on a uniform
  log-t grid).

**So the numeric state**: outer channel is genuinely not a decaying estimate;
the second channel is not numerically reachable without the exact `R₀`. Neither
channel is machine-proven `= 0` for a non-empty prime set. Both conclusions
agree.

## 4. Honest status: RH in this repo

- The route is **conditional on one open analytic identity** (the right channel
  `forward + (R−R₀)∘D = 0` for a non-empty finite prime family). It is not
  machine-proved.
- There is **no** branchwise norm/trace/HS estimate that supplies it: all
  intended such routes were swept (810, 811, 812, 813) and reduce to this one
  identity. `left`/`right` (Dev) skeleton is inconsistent and quarantined.
- Role of the numeric probe: it is a **first brick of evidence**, not a proof.
  It settles only that the outer channel is not a decay operator; the real
  question is the second-channel cancellation, which is an analytic (Sobolev /
  prolate) statement, not a grid number.

## 5. What would actually close it (actionable, Lean-shaped)

A `=0` proof for a non-empty `family` of **either** is required:

1. **Outer channel**: show `(I−R)∘(H·J·G⁻¹) = 0` uses that `(I−R)` kills `H·X`
   for all `X` in `range(G⁻¹·J)`. Equivalent to `range(J·G⁻¹) ⊆ range(T)`
   perpendicular to `(I−R)` — a genuine support/orthogonality statement on the
   transport's range.
2. **Band channel**: show `B·N·J + (R−R₀)∘D = 0` — i.e. the normalized-inverse
   forward cancels the metric/band leakage on the same frame. This is the
   canonical prolate correction; it is analytic, not algebraic.

Either one closes Gate-3U. Both are new content; neither is an empty-syntax
fill. Numeric grid probes cannot settle them without the exact `R₀`.

## Handoff

- RH status: **conditional** — the whole route reduces to one open identity in
  two orthogonal channels; non-empty-prime cancellation is unproved (and the
  numeric outer-channel is a non-decay).
- Files: read-only finding + this verdict; no `Source/`/`Route/` declaration
  changed.