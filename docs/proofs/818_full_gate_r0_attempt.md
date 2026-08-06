# Proof-717 / Gate-3U: 818 attempt — numeric R0 fails (alternating-projection degenerates); outer channel re-confirmed

Date: 2026-08-06
Status: honesty verdict — the exact-Sonin `R0` **cannot be materialized on the
finite grid by alternating projection**: it degenerates to rank 0 (the OK
projector) or fails idempotence (rank-1 non-converged).  So the "second channel"
and "band channel" numbers in 818 (0.85–0.98) are **not trustworthy** and are
NOT reported as a gate verdict.  The only robust number is the outer channel,
again non-zero and growing in the primes — re-confirming 815/816/817 on the
same toolchain.  The honest methodological takeaway: you cannot numerically
"reach" `R0` by a generic subspace-intersection on a finite grid; it is a
continuous object.
Branch: `proof/gate3u-completed-readout`
RELATED: `815_rh_route_conditional_boundary.md`, `816_outer_channel_nonzero_numeric.md`,
`817_outer_channel_slepian_verdict.md`

## 1. What 818 tried (the creative object)

Prior probes could not reach the nested gate channels because `R0` (the Sonin
projection) was not numerically available.  818 *tried to build it* as the
orthogonal projection onto the intersection:

```
range(R)  ∩  range(Q0),      Q0 = HT† R HT,   HT = spectral-reflection isometry
```

using **von Neumann alternating projection** (`v ← Q(Rv)` iterated), with
`range(R)` = radial support `t ≥ logλ` and `range(Q0)` = orth-projector onto
`range(H†R)`.  Grounding: `ccm24ArchimedeanSoninClosedSubspace =
LogRadialSupport ⊓ FourierSupport`, `Q0 = HT† R HT`, `HT = F·m(scattering)·
Rf·F` (`CCM24HardyTitchmarsh.lean:330-380`).

## 2. Result: the projection DEGENERATES

Sweep over three pure-phase HT clones (|m|=1, my proxy since the repo's
`archFactor` closed form isn't exported):

```
logl=0  kind0: OK projector  rank(R0)=0/80   → R0 = 0 (empty intersection)
        kind1: FAIL idempotent=1.9e-4        rank=1 (not converged → not a proj)
        kind2: FAIL idempotent=1.4e-2        rank=1 (not a proj)

logl=1  kind0/1/2: all OK as projectors, ALL rank=0 → R0 = 0
```

**Why**: on a finite `80`-pt grid, `span(R)` and `span(H†RH)` (with my proxy
pure-phase H) intersect only at `{0}` — the two finite subspaces are nearly
transversal. The analytic Sonin space is infinite-dimensional (prolate); the
finite discretization + arbitrary phase clone collapses the genuine positive
intersection to a phony rank-0. This is a **numerical-geometry artifact**, not
a statement about Gate-3U.

## 3. What is actually trustworthy

The **outer channel** `outer = ‖D(u)[t<logλ]‖/‖D(u)‖` on single radial probes
(uses no `R0`, no `Q0` choice):

```
logl=0     {2}=0.16    {2,3}=0.22    {2,3,5}=0.26
logl=1     {2}=0.17    {2,3}=0.27    {2,3,5}=0.32
```

Non-zero, growing in the primes, logλ-stable — consistent with 815/816/817.
The "second" `=R(I-Q0)RD` and "band" `=(R−R0)D` columns (0.85–0.98) are
DISCOUNTED: they depend on the degenerate `R0` and on my proxy `Q0`, so they
carry no gate meaning.

## 4. Verdict — honest

```
818 did NOT decide the second/band channel.
What it did decide: the equal that "numeric R0 by subspace intersection" is
NOT reachable on a finite grid.  To measure the gate's inner channel one needs
the ACTUAL archimedean phase `m(ξ) = archFactor/conj(archFactor)`
(CCM24HardyTitchmarsh.lean:104-106) and its transported Sonin frame — which is
exactly the analytic/prolate structure 815 named as "not a grid number."
```

The outer channel keeps its 816/817 status (non-zero, non-decaying). The
second/band channel **remains numerically unreachable** — not decided for or
against.

## Discipline

This is a methodological negative: "alternating-projection materialization of
R0 fails on the grid" is the recordable fact. It is **not** a Gate verdict and
**not** an RH statement. It re-pins the honest wall: the gate's inner channel
cannot be reached numerically without the true analytic Sonin/Prolate frame
(or the real arithmetic-prime family), and the outer channel stays non-zero.