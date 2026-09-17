# 1586 — the gate residual re-reduced onto the source-side strip: the carrier
# projection is the fixed space of EQE, both escape summands are bounded by the
# strip mass of the basis vector, and the single remaining interface is the
# angle gap at 1 (committed adapter named) (wave V CONT-10)

Date: 2026-09-17.

Status: PAPER DERIVATION ON COMMITTED DEFINITIONS. Zero Lean, zero digits, no
sentinel. This record executes items A and B of the post-1585 punch list. It
(1) identifies the carrier with the fixed space of the compression `E Q E`,
(2) reduces the gate's residual to the source-side escape of the transported
basis vectors, (3) proves the TWO EXACT BOUNDS that price both escape
summands by the strip mass, and (4) isolates the single remaining interface —
the angle gap at 1 — for which a committed adapter already exists. No gate is
closed; RH NOT claimed.

## 1. The carrier is the fixed space of the compression EQE

Committed objects (names as in 1583-1585): `E` = `radialSupportProjection`
(multiplication by `1_{[L,inf)}`), `Q = H E H` = `sourceFourierSupportProjection`,
`P = E and Q` = `sourceSoninProjection = R_S`. Put

```text
K := E Q E        (the compression; positive contraction, 0 <= K <= 1)
```

Lemma (classical, elementary). `range(P) = ker(1 - K)`.

```text
f in range(E and Q) => Ef = f, Qf = f => E Q E f = E Q f = Ef = f.
Conversely E Q E f = f: put h := Ef. Then
  ||h||^2 = <f, E Q E f> = <Ef, Q Ef> = <h, Qh>
          <= ||h|| ||Qh|| <= ||h||^2,
so equality holds, whence Qh = h; with h in range(E) this gives
h in range(E and Q), and f = E Q E f = Eh = h. QED
```

Consequence used below: `K^n -> P` strongly (spectral theorem for a positive
contraction: `t^n -> 0` on `[0,1)`, `= 1` on `{1}`), hence for every vector `g`

```text
dist(g, range(P))^2 = <g, (1-P) g> = lim_n <g, (1 - K^n) g> .
```

Also used: `H` is an INVOLUTION — `H = H* = H^{-1}`, because
`H = F^{-1} S F` with `S = (reflection) . m`, `|m| = 1` and
`m(-xi) = conj(m(xi))` (the scattering phase is self-inverse), so
`H^2 = F^{-1} |m|^2 F = 1`. This is the committed "genuine Hardy-Titchmarsh
involution" of 1536, and it is what makes `Q = H E H` an orthogonal projection
onto the REFLECTED window.

## 2. Residual = source-side escape of the transported basis vectors

Fix the pure-transport case `M = T_{-Lambda}` (the general physical `M` is a
product of unitary modulation and transport factors; all inequalities below
pass through isometries and the strip is the same, with the support claim
coming from the 1575/1576 transport ledger). Let `{e_i}` be an orthonormal
basis of the source carrier `sourceSoninCarrier lambda` and put

```text
g_i := T_{-Lambda} e_i ,      h_i := E g_i = T_{-Lambda}( e_i . 1_{[L+Lambda,inf)} ) .
```

Two elementary transport facts, both used constantly:

```text
(a)  supp(T_{-Lambda} e_i)  =  [L - Lambda, infinity)          (carrier in [L,inf))
(b)  H T_{-Lambda}  =  T_{Lambda} H        (the reflection structure, 1583)
```

The angle projection of 1584-1585 is `A = E - P = E - R_S`. For `g` in the
range of `Q` one has `A g = A(Eg)` (since `(1-E)g` is orthogonal to `range(E)`
which contains `range(P)`), and here `g_i = T_{-Lambda} e_i` lies in `range(Q)`
by the left-transport invariance of 1585 section 3. Hence the residual column
is exactly

```text
A T_{-Lambda} e_i  =  A h_i ,     h_i in range(E),
```

and for `h` in the range of `E` the two-projection geometry gives the exact
identity

```text
dist(h, range(P))^2  =  ||(1-Q) h||^2  +  ||(Q - P) h||^2      (Pythagoras, P <= Q).
```

## 3. The two exact bounds: both summands are strip mass

### 3.1 Radial summand — exact

```text
(1-E) T_{-Lambda} e_i  =  T_{-Lambda}( e_i . 1_{[L, L+Lambda)} )
```

(the left shift by `Lambda` exposes exactly the strip `[L, L+Lambda)` below the
window edge), therefore

```text
|| (1-E) T_{-Lambda} e_i ||^2  =  || e_i . 1_{[L,L+Lambda)} ||^2     EXACT.
```

### 3.2 Hardy summand — bounded by the same strip mass

`||(1-Q) h_i|| = dist(h_i, range(Q))`, and `range(Q) = H(range(E))` with `H`
unitary, so this equals `dist(H h_i, range(E)) = ||(1-E) H h_i||`. Now

```text
H h_i = H T_{-Lambda}( e_i . 1_{[L+Lambda,inf)} ) = T_{Lambda} H( e_i . 1_{[L+Lambda,inf)} )
```

and, writing `e_i^- := e_i . 1_{[L,L+Lambda)}`, so that
`e_i . 1_{[L+Lambda,inf)} = e_i - e_i^-` on the carrier's support,

```text
H h_i = T_{Lambda} H e_i  -  T_{Lambda} H e_i^- .
```

Since `e_i` lies in the carrier, `H e_i` lies in the range of `E`, i.e. is
supported in `[L, infinity)`, hence also in `[L - Lambda, infinity)`; and
`(1-E) T_{Lambda} psi = T_{Lambda} (1 - E_{>L-Lambda}) psi`, so the first term
is annihilated by `(1-E)`:

```text
|| (1-Q) h_i ||  =  || (1 - E_{>L-Lambda}) H e_i^- ||
                <= || H e_i^- ||  =  || e_i^- ||  =  || e_i . 1_{[L,L+Lambda)} || .
```

Both summands are therefore priced by the SAME object: the strip mass of the
source basis vector. Summing the first-order quadratic form:

```text
<g_i, (1 - K) g_i>  =  ||(1-E) g_i||^2 + ||(1-Q) E g_i||^2
                    <=  2 || e_i . 1_{[L,L+Lambda)} ||^2 ,
```

hence, with the carrier strip density

```text
StripDensity(Lambda)  :=  sum_i || e_i . 1_{[L,L+Lambda)} ||^2
                       =  Tr( P M_{1_{[L,L+Lambda)}} P )
                       =  int_{[L,L+Lambda)} K_P(u,u) du ,
```

```text
sum_i <g_i, (1-K) g_i>   <=   2 * StripDensity(Lambda) .
```

Note the difference in kind from 1584 section 5: the bound runs through the
FINITE strip `[L, L+Lambda)` and through the operator `1 - K` (which is
`(1-E) + E(1-Q)E`, both summands computed), not through any infinite tail and
not through any assertion about indicator multiplication (retracted in 1585).
The Hardy summand 3.2 is the new content here: it shows the "Fourier-gap"
defect of a truncated-transported carrier vector is itself strip mass — no
kernel asymptotics are needed for it.

## 4. The single remaining interface: the angle gap at 1

By section 1, for `h` in the range of `E`,

```text
dist(h, range(P))^2  =  int_{[0,1)} d mu_h (lambda) ,
< h, (1-K) h >       =  int_{[0,1)} (1 - lambda) d mu_h (lambda) ,
```

where `mu_h` is the spectral measure of `K = E Q E`. The two differ by the
factor `(1 - lambda)`, so the first-order bound of section 3 controls the
residual only through the ANGLE-GAP AT 1:

```text
(GAP)   spec(K)  subset of  {1}  union  [0, 1 - delta]      for some delta > 0
```

equivalently: no sequence of unit vectors with `K x_n - x_n -> 0` other than
near-carrier vectors ("no approximate carrier"). Given (GAP), for `h` in
`range(E)` orthogonal to the carrier,

```text
delta * ||h||^2  <=  < h, (1-K) h > ,
```

and the committed adapter applies verbatim: the general spectral-gap lemma

```lean
theorem normSq_le_of_spectralGap_of_norm_le
    (A : H →L[ℂ] G) (B : H →L[ℂ] E) (gap rawBound : ℝ)
    (hgap : 0 < gap)
    (hgap_norm : ∀ x : H, gap * ‖x‖ ^ 2 ≤ ‖B x‖ ^ 2)
    (hrawBound : 0 ≤ rawBound) (hrawNorm : ‖A‖ ≤ rawBound) (x : H) :
    ‖A x‖ ^ 2 ≤ (rawBound / Real.sqrt gap) ^ 2 * ‖B x‖ ^ 2
      (CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierSpectralGap.lean:47-92)
```

with `A := (E - P) T_{-Lambda}`, `B := (1 - K)^{1/2} T_{-Lambda}` (both
restricted to the source carrier, where the gap inequality holds on the
orthogonal complement of the carrier and both operators vanish on the carrier
itself) and `rawBound = ‖D‖ ‖T_{-Lambda}‖ ‖N‖`. Combining with section 3:

```text
+---------------------------------------------------------------------+
|  residual (angle part)  <=  (2 / delta) * ||D||^2 ||N||^2 *          |
|                             StripDensity(Lambda)                     |
|                                                                      |
|  arrow: (GAP) + StripDensity(Lambda) < infinity  ==>  hgap priced    |
+---------------------------------------------------------------------+
```

## 5. Status of the two remaining inputs (items A and B of the punch list)

Item B (angle remainder) is hereby REDUCED to the gap statement (GAP); no
carrier-density input enters it. Item A (strip density) remains the one
carrier-geometry input, and it is now the ONLY place where the Sonin space's
local structure is consumed:

```text
+-------------------------------+--------------------------------------+
| StripDensity(Lambda) < inf     | residual priced (with (GAP)); the     |
| (thin carrier at the edge)     | strip is finite-width, so this is    |
|                               | a LOCAL dimension count at the edge   |
+-------------------------------+--------------------------------------+
| (GAP) fails                    | the pair (E,Q) has an approximate     |
|                               | carrier; the angle route is           |
|                               | structurally re-typed (positive       |
|                               | obstruction, same shape as the        |
|                               | committed approximate-kernel theorem  |
|                               | `noExistsUniformOldCarrierDomination_ |
|                               | of_approximateKernel`, :220-238)      |
+-------------------------------+--------------------------------------+
```

For item A the natural committed tool is the Mellin-row density layer: the
committed rows `cc20NaturalMellinRow` / `cc20RestrictedLogNaturalMellinRow` /
`cc20WindowHaarNaturalMellinRow` are dense in the carrier
(`GlobalLogMellinCompleteness.lean:151-252`), so the strip count can be posed
as a counting problem for Mellin rows inside a strip of width `Lambda` — a
concrete, committed-adjacent formulation of the local-density question.

## 6. Ledger

```text
+--------------------------------------+------------------------------------+
| item                                 | status after this record           |
+--------------------------------------+------------------------------------+
| carrier = ker(1 - EQE)               | NEW, exact (section 1)             |
| residual = source-side escape        | NEW, exact (section 2)             |
| radial summand                       | EXACT = strip mass (3.1)           |
| Hardy summand                        | <= strip mass (3.2), NEW           |
| first-order bound                    | <= 2 StripDensity (section 3)      |
| residual <= (2/delta) StripDensity   | conditional on (GAP) (section 4)   |
| committed adapter for (GAP)          | EXISTS (quoted, :47-92)            |
| (GAP)                                | OPEN, named — angle gap at 1       |
| StripDensity(Lambda)                 | OPEN, named — the carrier input    |
| hradial                              | unchanged: one transport=>hwide    |
|                                      | Lean brick owed (1585)             |
| (star)/B4/rho5/R4/(OB)/W1            | OPEN; nothing machine-checked      |
|                                      | RH NOT claimed                     |
+--------------------------------------+------------------------------------+
```

## 7. The two owed Lean bricks (specified here, not written in this wave)

Brick 1 (transport => hwide; carries hradial). Consumes the committed anchors
`mem_ccm24LogRadialSupportClosedSubspace_iff` (CCM24LogRadialSupport.lean:67-70),
the projection-fixes-membership pattern of
`sourceInclusion_adjoint_comp_self` (CCM24FiniteSGramResponse.lean:46-54) and
`realLog_wideRadialScale` (C1G8R3CompositeBoundaryEnergy.lean:108-112):

```lean
theorem radialSupportProjection_fixes_of_support_subset
    (lambda : CCM24SoninScale) (s : ℝ) (v : finiteSCarrier)
    (hv : ∀ᵐ t ∂volume, t < Real.log lambda - s → v t = 0) :
    radialSupportProjection (wideRadialScale lambda s) v = v
```

with the corollary feeding `compositeRadialLeg_sourceBasis_normSq_summable`
(:911-922) at `s := Lambda`, using the 1575/1576 ledger to discharge `hv`
for `M J N e_i`.

Brick 2 (residual; conditional on (GAP)). Instantiate the committed adapter
`normSq_le_of_spectralGap_of_norm_le`
(CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierSpectralGap.lean:47-92) with
`A := (E - R_S) ∘L T_{-Lambda}`, `B := (1 - K)^{1/2} ∘L T_{-Lambda}`,
`gap := delta`, `rawBound := ‖D‖ ‖N‖`, on the orthogonal complement of the
carrier. The (GAP) inequality is the single hypothesis; section 3 supplies the
`B x` side through `StripDensity`.

Status: both statements are written in full above; neither is machine-checked.
No Lean was written or compiled in this wave (repo discipline: paper first,
compilation as its own wave).

## 8. Boundary

Moved: the residual is now a statement about ONE operator (`1 - K`, both
summands computed and priced by strip mass), ONE gap constant, and ONE local
density; the previously opaque "angle remainder" is gone as an independent
object. NOT moved: (GAP) and StripDensity are open; nothing machine-checked;
no digits; no sign input; (star), B4, rho5, R4, (OB)/W1 OPEN; RH NOT claimed.