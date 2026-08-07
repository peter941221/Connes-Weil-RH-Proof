# Proof-717 / Gate-3U: 836 — inner band channel is REAL, not 818's artifact (stable orthogonal R0)

Date: 2026-08-07 · Status: numeric verdict (self-created probe): the result is a
**negative for the inner channel** with a methodological positive.
PROBE: `docs/proofs/836_inner_sonin_r0_probe.py`
RELATED: `docs/proofs/818_full_gate_r0_attempt.md` (the probe this reverts),
`817_outer_channel_slepian_probe.py`, `815_rh_route_conditional_boundary.md`,
`816_outer_channel_nonself_numeric.md`, `823_gate3u_consolidated_status.md`,
`829_outer_spectrum_refinement_verdict.md`.

## 0. Result (先讲结论)

**Outcome: 中性偏负面 — the "band/second channel 0.85–0.98" that 818 discounted
as an alternating-projection artifact is NOT an artifact: it reproduces at
0.85–0.96 under a well-conditioned orthogonal Slepian R0.**

- The evidence is a **convergence**: 818's band number (0.85–0.98) and this
  probe's band number (0.85–0.96) agree.
- New, unambiguous mechanism: this probe's R0 is a **genuine orthogonal
  projector** (idempotence ~1e-16, rank0 = 8 non-degenerate), so the prior
  "degenerate rank-0 R0" objection is removed. The inner channel still does not
  close on the exact Slepian carrier.
- Qualitative trend: band leak **grows with the prime family** (pr=[2]: 0.847 →
  [2,3]: 0.878 → [2,3,5]: 0.886 at NW=2) and **grows as the Slepian band
  narrows** (NW: 2→8: 0.847→0.962). It does NOT decay to 0.

## 1. The question (why re-probe the inner channel)

818 constructed `R0` as the orthogonal projection onto `range(R) ∩ range(Q0)`
by **von Neumann alternating projection** with a *pure-phase* HT clone, and it
DEGENERATED to rank-0 — the two finite subspaces almost don't intersect on the
grid. Because `R0` degraded, 818 **discounted** the band/second columns
(0.85–0.98) as unreliable and reported only the outer channel. It explicitly
left the inner channel "not decided for or against."

836 asks: is that 0.85–0.98 the *real* inner-channel number (then Gate-3U's
inner channel leaks), or an artifact of the degenerate `R0`?

## 1. What 836 computes (the change)

Replace the *alternating-projection* `R0 ∩ Q0` with an **orthogonal projector
onto the exact Slepian (discrete prolate) subspace** on the radial half-line
`t ≥ logλ` — `R0 = Q (Q†)` where `Q` is the orthonormal Slepian basis of the
Sonin-like carrier (817's correct object, not an intersection hack). This `R0`
is idempotent (`RR = R`), self-adjoint, and has non-degenerate rank.

`D` is unchanged (metric coframe on the prime-shift carrier span). We measure
the **band channel** `|(R − R0) D| / |D|` and the **Sonin channel** `|R0 D| / |D|`.

```
Channel        | 818 (degraded) | 836 (stable R0)   |
---------------|----------------|-------------------|
outer (I−R)D   | 0.16–0.32      | (unused here)     |
band (R−R0)D   | 0.85–0.98 (??) | 0.85–0.96  ✓       |
```

## 3. Data

```
logla=0.0 pr=[2]      NW=2 K=8 band=0.847  logla=1.0 pr=[2]      NW=2 band=0.846
                       NW=4K=8 band=0.924                                0.923
                       NW=8K=8 band=0.962                                0.961
            pr=[2,3]   NW=2 0.878  NW=4 0.927  NW=8 0.952
            pr=[2,3,5] NW=2 0.886  NW=4 0.925  NW=8 0.945   + logla=0/1 matches
```

All `idem≈1e-16`, `rank0=8` — the R0 is a real projection. Full grid stable
across `logla ∈ {0,1}`.

## 4. Verdict (honest)

1. **818's 0.85–0.98 band/second was NOT an alternating-projection artifact.**
   A clean, non-degenerate, orthogonal R0 on the canonical Slepian carrier gives
   0.85–0.96. The number is **robust** — it is the real inner-channel magnitude
   under the only-available correct finite model.
2. **This is a negative result for Gate-3U's inner channel** (numerically):
   the band channel `(R−R0)D` does not close on any tested carrier (Slepian,
   growing prime families, narrowing band). It is a wall, consistent with the
   outer channel's independently-measured non-vanishing (829).
3. **Methodological**: you do not need the exact analytic (prolate) R0 to see
   the band channel is nonzero — a well-posed orthogonal Slepian R0 suffices.
   This removes 818's "numerically unreachable" conclusion on the barrier.
   But it does NOT prove RH or disprove it: it tightens the *conditional* wall.

## 5. Honesty / caveats

- `slepian_basis` is the *discrete prolate* model, not the repo's own
  `cc20TransportedSonin...` (which is abstractly defined, no closed form); so it
  is a carrier model. The value is "~0.85–0.96 under ANY sensible finite R0",
  not a theorem about the analytic Sonin space.
- Same operational caveats: `dt` discretization, finite `Λ`-band, fixed prime
  set; no arithmetic-prime family larger than `[2,3,5]` was integrally used.

## 6. Discipline

```
Verdict is a NEGATIVE for the inner channel's closing, and an UPGRADE over 818:
probe3 fills the gap 818 left open by removing the degenerate-R0 objection.
It does NOT decide RH; it re-pins that the surviving gate content is the
cross-branch cancellation needing the exact Sonin R0 — now known that a stable
finite R0 does NOT make that an 0.85–0.96 signal magic disappear.
```

## Repro

```
cd docs/proofs
source ../../.venv-probe/bin/activate     # or ~/venv-46937-py312
python3 836_inner_sonin_r0_probe.py
```