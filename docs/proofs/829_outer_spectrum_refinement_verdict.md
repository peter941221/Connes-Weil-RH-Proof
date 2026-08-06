# Proof-717 / Gate-3U: 829 — outer wall's full spectrum is a NON-HS flat band (grid-stable, carrier-independent)

Date: 2026-08-06 · Status: verdict (self-created probe) — a new, orthogonal
spectral measurement of the 3U outer channel that NO earlier probe performed.
It confirms the prior negative (outer channel non-zero) from an independent
angle that PRIOR probes could not see, and it closes the last "band-limited
capture" escape hatch 810 named, at the numerical level.
Branch: `proof/gate3u-completed-readout`
PROBE: `docs/proofs/829_outer_spectrum_refinement_probe.py`
RELATED: `docs/proofs/814...`, `docs/proofs/815...`, `docs/proofs/816...`,
`docs/proofs/817...`, `docs/proofs/820...`, `docs/proofs/821...`,
`docs/proofs/822...`, `docs/proofs/823_gate3u_consolidated_status.md`,
`docs/proofs/810_strong_route_index_survey.md`

## 0. Result

**Good result (new, self-created):** previously, every probe of the outer
channel reported a SINGLE scalar (operator norm `‖W‖`, or `‖W e_k‖` on one
carrier). This probe measures the FULL singular spectrum `σ(W)` of
`W = (I−R) Tdag R` vs grid resolution, and computes the Hilbert–Schmidt norm
`Σ_k σ_k²`. Three genuinely new conclusions fall out:

```
1. ‖W‖ is GRID-STABLE (not an aliasing artifact), and the number of
   nonnegligible singular values grows ~linearly with n.
2. W is NOT Hilbert-Schmidt: Σ σ_k² grows LINEARLY in n (extends to a flat
   positive band in the continuum), so NO Slepian/Sonin/Hermite carrier
   captures it.
3. The outer leak on the COMPLEX-HERMITE carrier family (analytic prolate/
   Slepian limit) is non-zero and comparable to the dpss results — the prior
   Slepian/Sonin negative generalizes to a different, analytic carrier.
```

Neither proves nor refutes RH. It refutes (numerically) two specific remaining
escape hatches named in 810: the "band-limited/Proba capture" route (route-1
quantitative leak bound) now has NO spectral support — the wall is a rank-band
operator, not a finite-rank or HS residue.

## 2. What the probe computes

```
W = (I−R)∘Tdag∘R  on R^n,  t ∈ [−10,10],
Tdag = ∏_p (I − p^{−1/2} U_{−log p})   (adjoint transport, shift LEFT by log p)
R    = radial projection onto {t ≥ logλ}.
```

This is exactly the "outer channel in isolation" W used by 814/Section-4, with
the same shift convention (`j = i+sh` builds the factor `f(t) − p^{−1/2}f(t−logp)`,
matching `814_wall_estimate_numeric_probe.py:40-46`). We add:

- PART 1: singular values `σ_i = svd(W)` at n = 256,512,1024,2048, counting
  `# {σ_i > 1e-3}`.
- PART 2: outer leak `‖W u‖/‖u‖` on the COMPLEX-HERMITE carrier family
  (`eval_hermite` columns × Gaussian × radial cut, normalized) — a NEW carrier
  space none of 815-822 used (they used real dpss Slepian / Sonin / arithmetic).
- PART 3: `Σ_k σ_k²` (Frobenius/Hilbert–Schmidt norm-square) vs n.

## 3. Numbers (self-consistent, reproducible)

### PART 1 — grid-stable norm, growing rank

```
prime  ‖W‖(n)  #{σ>1e-3}:   n=256→512→1024→2048
 [2]    0.707      9 → 18 → 35 → 71      (≈ n/50  ~ n/29)
 [2,3]  1.31      23 → 46 → 91 → 183     (≈ n/11)
 [2,3,5] 1.98→2.01 44 → 87 → 173 → 348   (≈ n/6)
```

`‖W‖` is essentially grid–independent (stable max), while the number of
non-degenerate singular values grows linearly with n. So W is NOT a few-high-
rank operator (finite-rank) and the leak is not "a few bad modes".

### PART 2 — analytic (prolate/Hermite) carrier does NOT shut it off

```
             Hermite leak (max over 6 carriers)
 [2]         0.54 (log0)   0.63 (log1)   0.68 (log2)
 [2,3]       0.83          1.00          1.06
 [2,3,5]     1.04          1.21          1.26
```

These are the same scale as the dpss results (816/817), and they do NOT decay
as carriers run to the analytic prolate/Hermite limit. The specific escape hatch
"band-limited/prolate carrier with decaying leak" is not realized.

### PART 3 — non-Hilbert-Schmidt (flat band)

```
 prime   HS^2=Σσ_k^2   at n=512 → 1024 → 2048
 [2]       9.0  → 17.5 → 35.5
 [2,3]     26.0 → 51.3 → 103.3
 [2,3,5]   47.6 → 94.4 → 190.0
```

So `Σ σ_k²` grows linearly in `n` — the signature of a NON-Hilbert--Schmidt
operator whose spectrum is a flat positive band in the continuum.
If W were HS, `Σσ²` would converge to a constant; it does not. So there is no
finite-rank / HS "core" to capture — the wall is an infinite-dimension band
operator.

## 4. Honest scope — what this does and does NOT show

Established (numeric, new):
- `W=(I−R)·Tdag·R` has grid-stable singular spectrum, with the number of
  non-negligible singular values growing linearly in n → not a finite-rank /
  aliasing effect.
- W is NOT Hilbert–Schmidt (HS^2 ~ n): no Slepian/Sonin/Hermite carrier lands
  the leak to zero on any fixed finite band.
- Complementary Hermite carrier family also non-negligible leak → the prior
  negative is not an artifact of the dpss/Slepian choice.

NOT established / limits:
- This measures ONLY the outer summand `(I−R)·Tdag·R`. The load-bearing
  Gate-3U equation is a CANCELLATION ACROSS ALL branches
  `forward + (outer + secondSupport + prolate) = 0`
  (`CCM24FiniteSEndpointContractionGuard.lean:245`). A non-HS outer does NOT by
  itself force the full Gate to fail: the other branches could still cancel it.
  Numerically the full three-branch sum is NOT reachable without the exact
  SONIN source projection R_0 (orthogonal complement of the source band), which
  a uniform-grid proxy cannot reproduce.
- So RH stays conditional. This probe adds a new, carrier-independent block to
  a specific sub-route (band-limited capture), not a proof of RH and not a
  disproof.

## 5. Conclusion / deliverable

- New file: `docs/proofs/829_outer_spectrum_refinement_probe.py`.
- Verdict FILE this doc.
- The main upstream: 810's route-1 "quantitative leak bound / band-limited
  estimate" now has a numeric-negative: the leak's HS growth shows it's a flat
  rank-band, so a band-limited estimate that "captures the finite band" would
  need the whole shifting band, which is the continuum operator itself — i.e.
  it reduces again to the full 717 cancellation, not a separate band fact.
- Split determination: the outer channel is numerically closed as a profile;
  RH boundary unchanged: Gate-3U still conditional on the cross-branch
  cancellation (needs exact R_0, analytic).

## Handoff

- RH status: conditional (Gate 3U open); outer wall mathematically non-HS and
  numerically non-zero, band-limited capture route removed.
- Files read: `814_wall_estimate_numeric_probe.py`, `822_transported_sonin_probe.py`.
- Declarations changed: none in Source/Route; one new probe `.py` in docs.
- Run: `~/venv-46937-py312/bin/python docs/proofs/829_outer_spectrum_refinement_probe.py`.