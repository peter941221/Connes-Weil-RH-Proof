# 1572 — T1 stage 2: adjudicating the projection modulation as a decay source

Date: 2026-09-17.

Status: PAPER SCREEN. Zero Lean, zero digits. This record discharges the
stage-2 obligation registered at the end of record
[1571](1571_T1_exponent_ledger_stage1.md): stage 1 priced the two classical
levers (symbol decay `k`, van der Corput `1/2`) and found the negative
off-diagonal ray stuck at `beta = 1/2 < 1` for EVERY symbol decay, reducing
the whole (★)-tail question to the third source - the projection modulation
of the committed operator family. Here the modulation is adjudicated against
its committed definition (law F20: read the definition, not the memory of
one).

## 1. What the committed modulation actually is

Transcribed from source, not reconstructed:

```text
E_lambda  = starProjection of ker (LpToLpRestrictCLM ... (ccm24LogRadialLowerRegion lambda))
            CCM24LogRadialSupport.lean:34-58, CCM24FiniteSProjectionTrace.lean:76-127
ccm24LogRadialLowerRegion = measurable set of the `Iio` (strictly-lower log-radial) type
Q_lambda  = comap(archimedeanHardyTitchmarshOperator) of the same radial subspace
            CCM24HardyTitchmarsh.lean:361-373
Q = H E H  committed conjugation:
            sourceFourierSupportProjection_eq_hardyTitchmarsh_conjugation
            (used at C1G8R3BoundaryOutputFactorizationBridge.lean:498)
tail normal form (record 1536):
            E (I - Q) E M J = E H (I - E) H E M J
```

Three consequences, in order of decision weight:

1. **`E` is a sharp window.** The projection is the orthogonal projection
   onto functions supported on a half-line-type log-radial region: its action
   on the `(x,y)` variables is multiplication by an indicator, not a smooth
   reproducing kernel. There is no window symbol to decay.
2. **`(★)` and B4 are one family.** With `Q = H E H` committed, the (★) tail
   `P C J` remainder (1513/1514, with `P = E Q E - R_prolate`) and the B4
   obligation `D E H (I-E) H E M_p J e_i` (1568 section 1) are the same
   operator expression under relabelling of the bounded factors. The 1568
   phrase "T0 is their shared entry fee" is now structural, not suggestive.
3. **A positive T2 (Cotlar across Sonin scales) feeds both obligations, and
   a negative T2 kills both.** The phase wave is deliberately concentrated:
   one exponent verdict, two consumers.

## 2. The dead branch, with the typed reason

Hope adjudicated: *the modulation supplies the missing `1/2` on the negative
ray, because restricting `(x,y)` to the region changes the effective
amplitude.* Against the committed definition:

* The indicator window contributes no factor `(1+|xi|)^{-k'}` - its Fourier
  symbol is a Dirichlet-kernel-type distribution, not a decaying function;
  on a two-sided infinite-measure carrier the window is not even Hilbert-
  Schmidt as an operator, so "window decay" is not a usable ledger entry
  (stage-1 finding, 1571: `chi_E not in L^2` on the two-sided carrier).
* The window's only new contribution is the EDGE: the region boundary cuts
  the stationary-phase contour. At a jump edge, integration by parts buys
  `1/|d(Phi)/d(xi)|` evaluated AT the edge, and by T0a (record 1570) the
  phase derivative grows like `2*pi*log|xi|`: edge contributions therefore
  carry at most a `1/log|xi|` gain - logarithmic, never a power. The negative
  ray needs `beta > 1` strictly; a logarithmic multiplier cannot cross a
  power threshold.
* Inside the region the amplitude was already accounted in stage 1 (the
  saddle `eta* = e^u` exits the decaying zone on `u < 0`); cutting the
  domain cannot add decay where the unrestricted integral already fails,
  it can only remove mass - which is the support/self-adaptation effect,
  handled separately as premise `hM` in record 1535's consumer
  (see record [1573](1573_T_B4_instantiation_chain.md), item 2).

Typed verdict: **the multiplier-SYMBOL-decay reading of the projection
modulation is dead** - it was never in the committed definition (sharp
indicator), and its only residual (edge terms) is power-insufficient by T0a.
This is a paper screening verdict on one named mechanism, registered so no
future wave re-prices it; it is NOT a formal impossibility theorem for the
whole (★)/B4 family - the live mechanisms are listed below.

## 3. What survives, and the single next question

After the dead branch, the tail estimate's remaining inputs are exactly:

| mechanism | status | committed anchor |
|---|---|---|
| positive-ray stationary phase (vdc `theta''`, T0b `<= 0.3067/xi^3`) | feeds `beta_+ = 5/2 > 1` | 1570, 1571 |
| prolate absorption `R_prolate` | already HS-free, subtracts from `P` | 1532, 1531 commutator combinators |
| column self-adaptation `hM: E M sourceInclusion = M sourceInclusion` | exact cancellation premise, decidable identity, NOT an estimate | 1535 `..._of_sourceRadialSupport` |
| Cotlar almost-orthogonality across scales | only promotes if a power gain survives stage 1 + prolate | 1568 T2 |

The single next question is therefore NOT an estimate: it is whether the
actual forward-Euler-exposed boundary columns satisfy the `hM` identity, for
the actual ambient factor `M_p` of the B2 factorization (record 1499). If
`hM` holds for the actual columns, the 1535 consumer removes the radial
defect exactly and B4 collapses to the single gap square-sum with T0-priced
phase; if it fails, 1534's warning stands (the radial finite-window result
does not cover arbitrary actual `M`) and the first estimate reopens. That
adjudication is the content of record 1573.

## 4. Boundary

No prior moved: (★), B4, the rho5 combined-row identity, the source/ambient
transport, and the R4 wrapper stay OPEN exactly as registered in map 042.
No estimate is proved here; the negative verdict is scoped to one named
mechanism (symbol-decay reading of the modulation) with its typed reason.
RH not claimed.
