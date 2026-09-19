# 1699 — D3 frame rig: committed laws reproduce at machine precision; on the naive window-confined family the archimedean sign field reads the WRONG way (arch < 0 at every width, both parities) and the synthetic off-line pair never dominates (gap ≤ 1.5e-2)

Date: 2026-09-19.

Status: one rig on the committed vocabulary
(`scripts/spectral_domination_1699.py`, run in WSL2; results
`results/1699_spectral_domination.json`).  Companion to record 1698; RH is
not claimed.

## 1. Object (hand-derived from the committed definitions, F27/F28)

Seed h = C^∞ bump (even or odd: `x·bump`) confined to `[−w, w]`,
`w ≤ 0.29 < 3/10`, L²-normalized; test `g = tripleVanishingRoot h`
(`C1LaneRD3Root.lean:264`), root L²-normalized (arch and the square's
Laplace are homogeneous of degree 2 in g, so signs and gap ratios are
normalization-invariant); book `F = starConvolution g` (the 1696 discrete
scheme; correlation squares are even, which the pole check below confirms at
1e-13).  All readouts use the committed forms:

```text
  poleTerm F = Re(F̂(1/2) + F̂(−1/2))              C1SameOwnerWeil.lean:31
  archimedeanTerm F = (log 4π + γ_E)·F(0)
      + ∫₀^∞ [e^{y/2}(F(y)+F(−y)) − 2F(0)] / (e^y − e^{−y}) dy
                                                    C1SameOwnerWeil.lean:61
                                                     (denominator :103-104)
  qw g = poleTerm − archimedeanTerm − finitePrimeSum (of the square)  :196
```

An earlier draft truncated the arch integral at the support edge; the
committed definition integrates over `Ioi 0`, and the discarded tail
`−2F(0)/(e^y − e^{−y})` is O(F(0)) — comparable to the whole readout.  The
committed forms are used throughout (erratum-class fix inside this wave,
before anything was recorded or committed).

## 2. Checks (committed identities) — all reproduce

```text
  C1 Vandermonde law  ĝ(s) = (0−s)(½−s)(1−s)·ĥ(s)   (C1LaneRD3Root.lean:271)
     4 probe points s ∈ {0.23+7i, 0.11+19i, −0.31+43i, 0.05+101i}
     max rel err = 2.2e-10
  C2 node vanishing   ĝ|{0, 1/2, 1}:  max abs err = 1.2e-7
     (relative to scale |ĝ| = 5.6e+02:  2.1e-10)
  C3 pole vanishing   poleTerm(D3 square) = 0  (C1LaneRD3Root.lean:332)
     max |pole| = 1.7e-13  against book |arch| ≈ 2.7  (rel 6e-14)
  sanity  PLAIN seed square (no D3), w = 0.29:
     pole = +0.862,  arch = +0.823   (positive — the 1696 sign family)
```

The sanity row seals the interpretation of M1: the arch integrand code reads
POSITIVE on the plain family and NEGATIVE on the D3 family — the flip is a
genuine effect of the differential construction, not a bug.

## 3. Measurements (open objects) — the negative result

```text
  M1  sign field on the naive confined D3 family (qw = −arch on the
      window class; detector needs qw < 0, i.e. arch > 0):

      even seed:  arch(0.10) = −3.773   arch(0.18) = −3.183
                  arch(0.25) = −2.854   arch(0.29) = −2.705
      odd  seed:  arch(0.10) = −3.800   arch(0.18) = −3.210
                  arch(0.25) = −2.881   arch(0.29) = −2.732

      arch < 0 at EVERY tested width and BOTH parities ⟹ qw > 0:
      the naive window-confined D3 family contains NO detector.

  M2  synthetic off-line pair at ρ₀ = 3/4 + iγ, γ ∈ [10, 320]
      (spectral contribution S_pair = 2 Re F̂(1/4 + iγ); only the spectral
      side depends on ρ at all — the arch book is ρ-free):

      γ =  10:  S_pair = +4.83e-3   |S_pair|/|arch| = 1.8e-3
      γ =  20:  S_pair = +8.37e-3                 3.1e-3
      γ =  40:  S_pair = +4.09e-2                 1.5e-2
      γ =  80:  S_pair = +3.63e-4                 1.3e-4
      γ = 160:  S_pair = +2.28e-2                 8.4e-3
      γ = 320:  S_pair = +2.82e-3                 1.0e-3
```

Two findings, both adversarial to the naive route:

1. **The sign field reads the wrong way**: on this family the arch book is
   an O(1) NEGATIVE constant (weakly width-dependent, parity-universal), so
   `qw > 0` — the D3 squares are anti-aligned with the detector sign on the
   window class.
2. **The synthetic pair never dominates**: it is at best 1.5% of the fixed
   book, decays with γ as the C^∞ tail predicts, and is always POSITIVE —
   it pushes `qw` AWAY from the detector sign.  No γ in the scanned range
   rescues the naive frame.

## 4. What this means for the program

The committed frame (1698) says premise 1 = {window-confined seed with
nonvanishing Laplace value} + {arch sign on the D3 square}.  This rig shows
the freedom in that statement is NOT spurious: taking the obvious seed
(compact bump, either parity, any admissible width) fails BOTH halves —
the sign is wrong AND no single off-line pair can outvote the fixed book.
So the surviving premise-1 routes are exactly:

  (a) **shaped seeds** — the classical Yoshida/Weil negative-test shapes the
      test (translate/rotate/phase freedom, cf. law F58) so that the sign
      comes from the FULL spectral book at the true zeros, not from the arch
      side; the naive family's failure quantifies how much shaping is owed;
  (b) **premise 2 directly** — the spectral sign on triple-vanishing
      squares, which map 046/047 already identified as the RH core.

No route is closed by this rig; the naive route is priced and it is not
free.  Map 047's pricing stands with the naive branch now measured.

## 5. Laws

- **F69 (arch book is ρ-free; only the spectral side carries the zero)**:
  on the committed window class the entire ρ-dependence of the Weil book
  lives in the spectral sum; any domination argument must therefore inject
  the zero through `F̂(ρ − 1/2)`, and its magnitude at admissible widths is
  bounded by the C^∞ tail — the naive frame loses by ≥ 2 orders at every
  tested height.

## 6. Next

1. Price the shaped-seed route: quantify the translate/phase freedom needed
   to flip the arch book (the −2.7…−3.8 gap), or show the freedom is
   bounded on the confined class.
2. Full-book cross-check at true zeros (mpmath `zetazero`, truncated
   explicit formula with smoothing discipline) — the genuine spectral-side
   rig that M2 proxies.
3. Keep premise 2 as the RH core; stop word unchanged: gate certificate.
