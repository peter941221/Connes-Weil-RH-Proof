# 1585 — erratum to 1584 section 4/5 (the "compact-window indicator is
# Hilbert-Schmidt" step is void), the committed compact-kernel mechanism that
# actually closes hradial, and the exact strip-escape identity that replaces
# 1584's infinite-tail residual (wave V CONT-9)

Date: 2026-09-17.

Status: PAPER DERIVATION ON COMMITTED DEFINITIONS. Zero Lean, zero digits, no
sentinel. This record does NOT open a new route; it repairs the bookkeeping of
1584. It (1) files an erratum to 1584 sections 4 and 5, (2) identifies the
committed mechanism that actually carries hradial, (3) proves the exact
strip-escape identity for left-transported carrier vectors, and (4) re-prices
the remaining residual against that identity. No gate is closed; RH NOT
claimed.

## 1. Erratum: multiplication by a compact-window indicator is not
## Hilbert-Schmidt

1584 section 4 asserts, for the pure-transport case `M = T_{-Lambda}`,

```text
(1-E) T_{-Lambda} J = T_{-Lambda} o M_{1_{[L, L+Lambda)}} o J
"and multiplication by the compact-window indicator IS Hilbert-Schmidt with
 || M_{1_{[L,L+Lambda)}} ||_HS^2 = Lambda"
```

and concludes `|| D (1-E) M J N ||^2 <= ||D||^2 Lambda ||N||^2`; section 5
reuses the same step for the angle-compact part with the constant `2 Lambda`.

The identity is correct. The Hilbert-Schmidt claim is VOID:

```text
+---------------------------------------------------------------------+
| On L^2(R), the operator M_chi : f |-> 1_chi . f  (chi of positive    |
| finite measure) is an ORTHOGONAL PROJECTION of infinite rank         |
| (its range is L^2(chi), infinite-dimensional).                       |
|                                                                     |
| Hilbert-Schmidt  =>  compact  =>  finite rank when a projection.      |
| Hence || M_chi ||_HS = +infinity.  The number Lambda is not its HS    |
| norm; Lambda is the measure of chi (the trace of M_chi evaluated on  |
| a density-one family, which no committed object supplies).           |
+---------------------------------------------------------------------+
```

The same error class as the 1583 section 3 `|W| * ||K||_2^2` erratum that
1584 itself filed: an unbounded-geometry object priced as if the carrier were
a finite-measure window.

What survives from 1584 section 4 is only the operator identity. Composing
with the source inclusion `J` does NOT repair the claim: for an orthonormal
basis `{e_i}` of the source carrier,

```text
|| M_chi o J ||_HS^2 = sum_i || M_chi e_i ||^2
                     = sum_i int_chi |e_i|^2 = int_chi K_P(u,u) du ,
```

the diagonal density of the carrier's reproducing kernel integrated over the
strip — finite only if the carrier has finite local dimension density, which
is exactly the open Sonin-thinness content (section 4 below). Writing
`||M_chi||_HS^2 = Lambda` silently assumes density equal to one everywhere.

Section 5's tail bound is void for the same reason, one step earlier:

```text
Tr_carrier(E_{>L+2 Lambda})  =  sum_i || E_{>L+2 Lambda} e_i ||^2
```

is the compression of an infinite-rank projection to the carrier: an infinite
sum of tail masses, `+infinity` unless the carrier meets the tail in a
finite-dimensional space. So the chain
`residual <= Tr_carrier(M^dagger E_{>L+Lambda} M) <= Tr_carrier(E_{>L+2Lambda})`
ends in `+infinity`; it does not establish finiteness of the residual.

## 2. What actually closes the radial leg: committed compact kernels

The committed closure does not use indicator multiplication at all. It uses
CONTINUOUS KERNELS ON COMPACT WINDOWS, and the roof of the argument is the
root support radius `selectedRootSupportRadius owner` (the width of the
selected test function's positive-root window):

```text
compositeStripWindowOperator owner s
  = kernelIntervalL2ZeroExtension (-s) 0 0
      o ContinuousKernelHilbertSchmidt.operator
          (volume : Measure (CompactInputInterval (-R) R (-s) 0))
          (volume : Measure (CompactOutputInterval (-s) 0))
          (compactOutputRootKernel owner.sourceTest ... R ... (-s) 0)
      o globalL2ToKernelInterval ((-s) - R) (0 + R) 0
        (C1G8R3CompositeBoundaryEnergy.lean:841-854)
```

Why this IS Hilbert-Schmidt, in contrast with section 1: the kernel is
CONTINUOUS on a product of COMPACT intervals, hence square-integrable there,
hence the kernel operator between those two `L^2` spaces is Hilbert-Schmidt
(`ContinuousKernelHilbertSchmidt.basis_normSq_summable`, :877-881). The
surrounding restriction / zero-extension maps are bounded, and bounded
pre/post composition preserves column square-summability
(`PositiveTrace.summable_normSq_precomp`, `summable_normSq_postcomp`, used at
:882-895 and :1056-1080). No density input, no indicator-HS claim.

The roof is the committed theorem (statement elided only in the binder list;
the conclusion is verbatim):

```lean
theorem compositeRadialLeg_sourceBasis_normSq_summable
    ... (hwide : radialSupportProjection (wideRadialScale lambda s) ∘L M ∘L
        sourceInclusion lambda = M ∘L sourceInclusion lambda) :
    Summable fun i : ρ =>
      ‖(((ContinuousLinearMap.id ℂ Carrier -
            radialSupportProjection lambda) ∘L rootConvolution owner ∘L
          M ∘L sourceInclusion lambda) ∘L N) (sourceBasis i)‖ ^ 2
      (C1G8R3CompositeBoundaryEnergy.lean:911-922)
```

Its docstring says the two pieces both go "through committed compact-window
mechanisms" and that "the support fact `hwide` itself stays open" — matching
the proof body read in full: `(I - E) = (I - E'') + (E'' - E)`, the first
piece by `selectedRootBoundaryWindowOperator`, the second by
`compositeStripWindowOperator`.

Consequence. 1584 section 4's last paragraph — the transport ledger DELIVERS
`hwide` at scale `lambda' = lambda e^{-Lambda}`, because `M J N e_i` is
supported in `[L - Lambda, infinity)` — is correct and sufficient. The
committed closure then fires unchanged. So:

```text
+------------------------------------+---------------------------------------+
| hradial status                     | CLOSED-PENDING-ONE-BRICK (unchanged)  |
| hradial mechanism (1584 section 4) | CORRECTED: committed compact-kernel   |
|                                    | route + transport => hwide; the       |
|                                    | constant-Lambda bounds are withdrawn  |
| angle-compact part (1584 section 5)| NOT closed as stated (same erratum)   |
| the one owed Lean brick            | unchanged: transport ledger => support|
|                                    | in [L - Lambda, infinity) => hwide    |
+------------------------------------+---------------------------------------+
```

## 3. The exact strip-escape identity for left-transported carrier vectors

This part is new and independent of the erratum. Let `E` be the radial
(multiplication) projection onto `[L, infinity)`, `Q = H E H` the
Fourier-support projection, `P = E and Q = sourceSoninProjection` the source
Sonin carrier projection, and `A = E - P` the angle projection.

Lemma (transport invariance of the Fourier-support class). For `c >= 0` and
`g` with `Hg` supported in `[L, infinity)` (i.e. `g` in the range of `Q`),

```text
H (T_{-c} g) = T_c (H g)     (the reflection structure H T_c = T_{-c} H)
```

is supported in `[L + c, infinity)`, hence again in `[L, infinity)`:

```text
g in range Q  =>  T_{-c} g in range Q      for every c >= 0.
```

Applied to a carrier vector `f`: `Hf` lies in `[L, infinity)`, so

```text
f in range P  =>  T_{-Lambda} f in range Q   (all Lambda >= 0).
```

Left transports never destroy the Hardy condition; they can only damage the
RADIAL condition. For `g` in the range of `E` the two-projection geometry
gives `(1-P) g = (E - P) g = A g`, so for `f` in the carrier:

```text
(1-P) T_{-Lambda} f  =  (1-E) T_{-Lambda} f   +   A E T_{-Lambda} f
                        [exact; the two terms are orthogonal in L^2]
```

and the first term is EXACT:

```text
(1-E) T_{-Lambda} f  =  T_{-Lambda} ( f . 1_{[L, L+Lambda)} ) ,
```

because carrier vectors live in `[L, infinity)` and the left shift by
`Lambda` exposes exactly the strip `[L, L+Lambda)` below the window edge.
Hence, on the source basis,

```text
sum_i || (1-P) T_{-Lambda} e_i ||^2
  = int_{[L, L+Lambda)} K_P(u,u) du                 (carrier strip density)
  + sum_i || A E T_{-Lambda} e_i ||^2               (angle remainder)
```

The strip term is a FINITE-MEASURE object (width `Lambda = log prod q`), in
contrast with 1584 section 5's infinite tail `[L + 2 Lambda, infinity)`. The
angle remainder involves only `E T_{-Lambda} e_i =
T_{-Lambda}(e_i . 1_{[L+Lambda, infinity)})`, i.e. truncated-and-shifted
carrier vectors — a named, compact-adjacent object.

## 4. Re-priced residual and the decisive fork

For the physical `M` (transport ledger of 1575/1576: only adjoint Euler
transports move support, each by at most `log q`; modulations and right
transports do not), `M J N e_i` is supported in `[L - Lambda, infinity)`, so
the same strip identity applies with the total budget `Lambda`. The gate's
remaining content is therefore the carrier thinness functional

```text
Thin(Lambda)  :=  int_{[L, L+Lambda)} K_P(u,u) du  +  angle remainder ,
```

and the fork is decisive in the F30 sense:

```text
+-------------------------------+--------------------------------------+
| carrier local density finite   | Thin(Lambda) < infinity for every    |
| (thin Sonin space)             | finite window: the residual is        |
|                               | priced, hgap closes, (star) closes    |
|                               | for the physical factors              |
+-------------------------------+--------------------------------------+
| carrier local density infinite | the residual is genuinely infinite:   |
| (fat / generic-position pair)  | the angle route is structurally        |
|                               | re-typed (positive result: the gate   |
|                               | is not reachable through this         |
|                               | compression)                          |
+-------------------------------+--------------------------------------+
```

Searched and confirmed for the record: NO committed dimension, rank, density,
or basis-localisation statement about `ccm24ArchimedeanSoninClosedSubspace`
exists in the tree (`grep` for `finiteDimensional|rank|dimension|span` over
the Sonin files and over all `SoninClosedSubspace` uses returns only
completeness instances and transport/projection algebra). The thinness input
is genuinely new mathematics, not bookkeeping.

Supporting committed anchors used above:

```text
finiteSCarrier := cc20GlobalLogCrossingL2        (CCM24FiniteSProjectionTrace.lean:73)
E = radialSupportProjection = starProjection of the restriction kernel
                                                  (:76-78; CCM24LogRadialSupport.lean:48-58)
Q = sourceFourierSupportProjection = starProjection of the comap of the
    Hardy-Titchmarsh operator                          (:81-83; CCM24HardyTitchmarsh.lean:361-373)
R_S = sourceSoninProjection = E and Q                (:94-96)
K_S = sourceProlateRemainder = E Q E - R_S           (:155-158)
K_S = (E - R_S) o Q o (E - R_S)  [angle sandwich]    (:168-183)
H = F^{-1} o S o F with S f(xi) = m(2 pi xi) f(-xi)  (CCM24HardyTitchmarsh.lean:331-336)
  => H T_c = T_{-c} H   [paper level; the committed conjugation lemma
     `ccm24RadialOrientedCrossing_eq_translation_conjugation` carries an
     explicit COMMUTING hypothesis, which H does not satisfy]
```

## 5. Ledger

```text
+--------------------------------------+------------------------------------+
| item                                 | status after this record           |
+--------------------------------------+------------------------------------+
| 1584 sec.4 indicator-HS claim        | RETRACTED (void)                   |
| 1584 sec.4 constant-Lambda bound     | WITHDRAWN                          |
| 1584 sec.5 constant-2Lambda bound    | WITHDRAWN                          |
| 1584 sec.5 tail-trace bound          | VOID (infinite-rank compression)   |
| hradial, committed route             | CLOSED-PENDING-ONE-BRICK (unchanged|
|                                      | status; mechanism corrected)       |
| prolate term (K_S)                   | CLOSED (committed all-scale HS;    |
|                                      | now also K_S = A Q A, ||K_S|| <= 1)|
| left-transport Q-invariance          | NEW, exact (section 3)             |
| strip-escape identity                | NEW, exact (section 3)             |
| carrier thinness functional          | OPEN — the gate's content          |
| (star)/B4/rho5/R4/(OB)/W1            | OPEN                               |
| machine-checked                      | nothing; RH NOT claimed            |
+--------------------------------------+------------------------------------+
```

## 6. Boundary

Moved: an invalid Hilbert-Schmidt step removed from the record chain; the
correct committed mechanism identified and quoted; hradial's status preserved
with corrected mechanism; an exact strip-escape identity proved for
left-transported carrier vectors; the residual re-priced against a
finite-measure strip instead of an infinite tail; the thinness input confirmed
absent from the committed tree. NOT moved: the thinness functional itself is
OPEN; no Lean; no digits; no sign input anywhere; (star), B4, rho5, R4,
(OB)/W1 remain OPEN; RH NOT claimed.