# 1587 — erratum to 1586 section 4: the angle gap is the already-ruled
# Friedrichs-gap shape (maps 015/016, record 1435; machine-checked sibling
# obstruction, record 590); the residual splits exactly into the strip mass
# plus a ZEROTH spectral moment of EQE whose 1586 bound is only its FIRST
# moment, so the route is re-typed without any gap:
# residual^2 <= (1 + 1/epsilon) StripDensity + endpoint mass (wave V CONT-11)

Date: 2026-09-17.

Status: PAPER ERRATUM + STRUCTURAL RE-TYPING ON COMMITTED DEFINITIONS. Zero
Lean, zero digits, no sentinel. This record repairs section 4 of 1586. It
(1) files the erratum, (2) gives the exact moment accounting that shows what
the 1586 strip bound really controls, (3) replaces the retired gap conditional
by a gap-free decomposition with an explicit named remainder, and (4) records
the bookkeeping law that 1586 section 4 violated. No gate is closed; RH NOT
claimed.

## 1. Erratum to 1586 section 4

1586 section 4 concluded

```text
residual (angle part)  <=  (2 / delta) * ||D||^2 ||N||^2 * StripDensity(Lambda)
```

from the committed adapter `normSq_le_of_spectralGap_of_norm_le`, instantiated
at `B := (1 - K)^{1/2} o T_{-Lambda}` under the hypothesis (GAP). Both halves
of that step are now withdrawn, for independent reasons.

### 1.1 The adapter cannot be instantiated at that B

The adapter's hypothesis is a lower bound over the WHOLE space (quoted
verbatim, conclusion and hypotheses both):

```lean
theorem normSq_le_of_spectralGap_of_norm_le
    (A : H →L[ℂ] G) (B : H →L[ℂ] E) (gap rawBound : ℝ)
    (hgap : 0 < gap)
    (hgap_norm : ∀ x : H, gap * ‖x‖ ^ 2 ≤ ‖B x‖ ^ 2)
    (hrawBound : 0 ≤ rawBound) (hrawNorm : ‖A‖ ≤ rawBound) (x : H) :
    ‖A x‖ ^ 2 ≤ (rawBound / Real.sqrt gap) ^ 2 * ‖B x‖ ^ 2
      (CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierSpectralGap.lean:47-58)
```

For `B := (1 - K)^{1/2} o T_{-Lambda}` the hypothesis needs a uniform lower
bound at every `x` in the ambient space. It fails on exactly the directions
that 1586 section 3 itself measures: if `x` is in the carrier and vanishes on
the strip `[L, L + Lambda)`, then `T_{-Lambda} x` lies in `range(E)` (the strip
was the only obstruction) and, by the 1585 left-transport invariance, also in
`range(Q)`; hence `T_{-Lambda} x` is in the carrier and `B x = 0` while
`‖x‖ /= 0`. Whether such carrier vectors exist is precisely the localisation
question that is the companion open input, so the hypothesis is not available
from committed data either way. The instantiation proposed in 1586 section 7
(Brick 2) is therefore WITHDRAWN.

The same SHAPE is already machine-checked to fail in the sibling reduction:
record 590 / `CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierSpectralGapObstruction.lean`
proves

```lean
theorem noExistsUniformOldCarrierSpectralGap_of_nonzero_source_column_arithmeticPrimes
    {lambda : CCM24SoninScale} (x : sourceSoninCarrier lambda) (hx : x ≠ 0) :
    ¬ ∃ gap : ℝ,
      Nonempty (SuffixRawOldCarrierUniformSpectralGapData lambda gap)
      (…SpectralGapObstruction.lean:118-126)
```

i.e. no family-uniform lower bound exists at all for the old-carrier analysis
map, for any nonzero source column, via the approximate kernel
`y_p = newSuffixFrame lambda [] x`, `‖W_p y_p‖ -> 0`, `‖y_p‖ = ‖x‖ > 0`. That
is a statement about the whole-space denominator shape, not about the
complement-restricted statement below; it does not refute the 1587 route, but
it is the same shape as the hypothesis 1586 section 4 assumed.

### 1.2 (GAP) is a shape already retired by the route maps

The mechanism is elementary, and it identifies (GAP) with a statement the
project has already ruled on. `K = E Q E` is a positive contraction on
`range(E)`; `P` is its fixed projection; `K - P = K|_{P^perp}` is zero on
`range(P)` and equals the compression elsewhere. For a positive operator the
norm is the top of the spectrum, so

```text
(GAP)   spec(K) subset of {1} union [0, 1 - delta]
   <=>  ||K - P|| < 1                     (delta = 1 - ||K - P|| = 1 - ||K|_{P^perp}||)
   <=>  the Friedrichs angle of range(E), range(Q) is positive
   <=>  range(E) + range(Q) is closed     (Kato; angle computed after removing
                                           the intersection range(P), which here
                                           is the source Sonin carrier)
```

Equivalently `||E - Q|| < 1`, since for projections `||P_M - P_N|| = sin c` and
`||K|_{P^perp}|| = cos^2 c`.

In the project's own notation this is a recorded obligation, not a new one.
Map 016 section 1 writes `T_b = p_b q p_b` and `r_b` = projection onto
`Ran(p_b) intersect Ran(q)`; record 1435's "Exact remaining obligation" is
literally

```text
||p_b q_1 p_b - r_b|| < 1     and     r_b (p_b q_1 p_b) = r_b .
```

The ruling predates 1586 by three days:

```text
+----------------------------------+------------------------------------------+
| source (date)                    | ruling                                   |
+----------------------------------+------------------------------------------+
| docs/map/016 section 3.1         | "The assertion ||T_b - r_b|| < 1 is only  |
| (2026-09-14)                     | a conditional bridge in batch 1435. It is |
|                                  | not an available premise. Near-extremal   |
|                                  | prolate directions make a uniform angle   |
|                                  | gap an unsuitable default target."        |
+----------------------------------+------------------------------------------+
| docs/map/015 section 6           | "novel move: Do not assume a Friedrichs-  |
| (generation card, 2026-09-14)    | angle gap. Treat the intersection as the  |
|                                  | spectral endpoint 1 of p_b q p_b and use  |
|                                  | the detector's C†C smoothing to make the  |
|                                  | endpoint filter trace-summable."          |
+----------------------------------+------------------------------------------+
| record 1435 (2026-09-14)         | "If a genuine moving-scale gap cannot     |
|                                  | hold, this bridge localizes the failure   |
|                                  | and forces the next proof to use an       |
|                                  | angle-free weighted spectral estimate."   |
+----------------------------------+------------------------------------------+
| record 577 ("Remaining source    | the two uniform inputs (the gap and the   |
| bottom")                         | raw bound) are explicitly NOT proved      |
+----------------------------------+------------------------------------------+
```

So 1586 section 4's conditional is not a live premise: it re-derives a shape
already retired, three days earlier, by the map that owns this face. The
erratum is filed here rather than in 1586 (records are append-only).

## 2. What the strip density actually bounds: the exact moment accounting

This is the new content of the record, and it is what makes the erratum sharp
rather than merely negative. It has two steps: an exact split of the residual,
then the spectral reading of the part that the strip density does not already
carry.

### 2.1 The residual splits exactly into a strip term and a carrier-distance term

Recall `A = E - P`, so that `A E = A` and `A (1 - E) = 0` (because `P E = P`).
For `g` in the range of `Q` the 1585 strip-escape identity gives
`(1 - P) g = (1 - E) g + A (E g)` with the two terms orthogonal (the first lies
in `range(E)^perp`, the second in `range(E)`). Applying this to
`g_i = T_{-Lambda} e_i` and using 1586 section 3.1 for the first term:

```text
+---------------------------------------------------------------------+
|  residual^2  =  sum_i ||(1 - P) T_{-Lambda} e_i||^2                  |
|                                                                     |
|              =  sum_i ||e_i . 1_{[L, L+Lambda)}||^2                  |
|                 +  sum_i ||(1 - P) h_i||^2                           |
|                                                                     |
|              =  StripDensity(Lambda)                                 |
|                 +  sum_i dist(h_i, carrier)^2          EXACT         |
|                                                                     |
|  h_i := E T_{-Lambda} e_i = T_{-Lambda}(e_i . 1_{[L+Lambda,inf)})    |
+---------------------------------------------------------------------+
```

So the radial/escape half of the residual is not merely bounded by strip mass
— it IS the strip mass, exactly, with no gap and no constant. All remaining
content sits in `sum_i dist(h_i, carrier)^2`, and this is where the moment
question lives.

### 2.2 The remaining term is a ZEROTH moment; the 1586 bound is its FIRST moment

For `h` in `range(E)` let `nu_h` be the spectral measure of the positive
contraction `K = E Q E` (self-adjoint on `range(E)`), split as

```text
nu_h = ||P h||^2 * delta_1  +  nu'_h ,      nu'_h supported in [0, 1) .
```

Then, exactly:

```text
+--------------------------------------------+--------------------------------+
| quantity                                   | spectral reading               |
+--------------------------------------------+--------------------------------+
| ||h - P h||^2 = dist(h, carrier)^2         | nu'_h([0,1))    ZEROTH moment  |
| <h, (1 - K) h> = ||(1 - Q) h||^2           | int (1 - lambda) d nu'_h        |
|                                            |                 FIRST moment   |
| <h, (Q - P) h>                             | int lambda d nu'_h   (the      |
|                                            | near-endpoint mass)             |
+--------------------------------------------+--------------------------------+
```

(the middle identity is 1586 section 3.2's computation: for `h` in `range(E)`,
`1 - K = (1 - E) + E (1 - Q) E` kills the first summand and the second acts as
`1 - Q`). Hence the Pythagorean identity of 1586 section 2 is exactly the
lambda / (1 - lambda) split of the zeroth moment,

```text
nu'_h([0,1))  =  int lambda d nu'_h  +  int (1 - lambda) d nu'_h ,
```

and the 1586 section 3 bound

```text
sum_i ||(1 - Q) h_i||^2  <=  sum_i ||e_i . 1_{[L,L+Lambda)}||^2
                         =  StripDensity(Lambda)
```

is a bound on the FIRST moment of `nu'_{h_i}`, equivalently on the second
Pythagorean summand. The term that remains open in 2.1 is the ZEROTH moment,
equivalently the full `nu'_{h_i}([0,1))`, i.e. the Pythagorean identity itself.

A bound on a first moment does not bound a zeroth moment. Converting them costs
exactly the gap constant `1 / delta`:

```text
nu'_h([0,1))  <=  (1/delta) * int (1 - lambda) d nu'_h      GIVEN (GAP) .
```

That is the whole content of 1586 section 4, and it is the step the maps
retire. The sharp reading of the erratum: **the strip density is already an
exact bound on the radial half of the residual; on the half that remains it
prices the FIRST moment while the residual needs the ZEROTH.** 1586 did not
merely carry an unproved hypothesis; it priced the wrong moment.

## 3. The re-typed decomposition: the gap traded for a named endpoint mass

No gap is needed if the endpoint window is kept as an explicit remainder. For
every `epsilon` in `(0, 1]`, splitting the zeroth moment at `1 - epsilon`,

```text
+---------------------------------------------------------------------+
|  sum_i nu'_{h_i}([0,1))                                              |
|                                                                     |
|    <=  (1/epsilon) * sum_i int_{[0,1-epsilon)} (1 - lambda)          |
|                                 d nu'_{h_i}                          |
|        + sum_i nu'_{h_i}([1-epsilon, 1))                             |
|                                                                     |
|    <=  (1/epsilon) * StripDensity(Lambda)                            |
|        + EndpointMass(epsilon)                                       |
|                                                                     |
|  EndpointMass(epsilon) := sum_i || E_{[1-epsilon,1)}(K) h_i ||^2     |
+---------------------------------------------------------------------+
```

with `h_i = E T_{-Lambda} e_i` as above. Combined with the exact split of 2.1:

```text
residual^2  <=  (1 + 1/epsilon) * StripDensity(Lambda) + EndpointMass(epsilon) .
```

The first part is unconditional and priced by the committed strip object; the
endpoint term is irreducible at this level, since its trivial bound is
`sum_i ||h_i||^2 = +infinity`. The gap constant has not disappeared — it has
been moved into a named window, and the window `[1 - epsilon, 1)` is exactly
where map 016 section 3.1 locates the difficulty ("near-extremal prolate
directions"). This is the shape the binding route already prescribes: map 016
section 2 asks for `int_[0,1) w(t) d tr(C E_b(dt) C†) < infinity` with the
weight derived by the proof; here the derived vanishing weight is
`(1 - lambda)` and the singular part is the endpoint window.

## 4. What survives from 1586, and what is withdrawn

```text
+--------------------------------------------------+-----------------------------+
| item                                             | status after this record    |
+--------------------------------------------------+-----------------------------+
| carrier = ker(1 - EQE), K^n -> P strongly        | STANDS (exact)              |
| residual column = A h_i, h_i = E T_{-Lambda} e_i | STANDS (exact)              |
| residual = StripDensity + dist(h_i,carrier)^2    | STANDS, now EXACT (2.1)     |
| radial summand = strip mass (exact)              | STANDS                      |
| Hardy summand <= strip mass (1586's new content) | STANDS, and is now READ as  |
|                                                  | the FIRST-moment bound      |
| Pythagorean split of the residual                | STANDS, and is now read as  |
|                                                  | the moment identity         |
| residual <= (2/delta)||D||^2||N||^2 StripDensity | WITHDRAWN                   |
| adapter instantiation at B = (1-K)^{1/2} T       | WITHDRAWN (1.1)             |
| (GAP) as a live premise of this route            | WITHDRAWN as a premise      |
|                                                  | (1.2; maps 015/016, 1435)   |
| Lean Brick 2 of 1586 section 7                   | WITHDRAWN with the adapter  |
| Lean Brick 1 (transport => hwide, hradial face)  | UNAFFECTED by this erratum  |
+--------------------------------------------------+-----------------------------+
```

The gate's remaining bones on this face, now each with its correct level:

```text
+----------------------------+------------------------------------------------+
| bone                       | correct form                                   |
+----------------------------+------------------------------------------------+
| StripDensity(Lambda)       | local trace / local (★): Tr(P M_1strip P) =     |
|                            | int_strip K_P(u,u) du; the FIRST-moment object |
+----------------------------+------------------------------------------------+
| EndpointMass(epsilon)      | near-endpoint spectral mass of EQE on the      |
|                            | transported basis; the map-016 weight object   |
+----------------------------+------------------------------------------------+
| T1 transport               | identify the plain-window pair (E,Q) with the  |
| (map 015 section 5)        | doubled-shift pair (p_b,q) so the R3 endpoint  |
|                            | machinery (1432-1452, C1G8R3WeightedStrong-    |
|                            | ToHS) is reusable rather than rebuilt          |
+----------------------------+------------------------------------------------+
| hradial transport => hwide | unchanged from 1585/1586; not touched here     |
+----------------------------+------------------------------------------------+
```

## 5. Bookkeeping law filed with this erratum

1586 section 4 did run a pre-spend sweep — it found and cited the committed
adapter and named the sibling obstruction — but it swept for NAMES. The shape
it introduced had been ruled three days earlier by map 016 section 3.1 and
refuted machine-checked in the sibling reduction by record 590. Filed:

**F31. The pre-spend sweep applies to PREMISE SHAPES, not only to named cards.
Before introducing a conditional (a uniform gap, a domination, a compactness or
injectivity input), grep the maps and records for the ruling on the SHAPE — a
uniform lower bound, an operator-norm gap, a closedness premise — not only for
its spelling.**

## 6. Ledger and boundary

```text
+--------------------------------------+------------------------------------+
| item                                 | status after this record           |
+--------------------------------------+------------------------------------+
| 1586 section 4 conditional bound      | RETRACTED                         |
| 1586 sections 1-3                     | STAND (re-read as moment identity)|
| gap-free decomposition (section 3)    | NEW, exact                        |
| StripDensity(Lambda)                  | OPEN, correctly typed             |
| EndpointMass(epsilon)                 | OPEN, correctly typed             |
| hradial (transport => hwide)          | OPEN, one Lean brick owed         |
| (star)/B4/rho5/R4/(OB)/W1             | OPEN                              |
| machine-checked                       | nothing in this record            |
| RH                                    | NOT claimed                       |
+--------------------------------------+------------------------------------+
```

Moved: an invalid conditional removed from the record chain; the strip object
identified as a first-moment bound and the residual as a zeroth moment; a
gap-free decomposition with an explicit endpoint remainder; the angle face
reconnected to the already-binding R3 endpoint route; a new bookkeeping law.
NOT moved: no gate closed, no estimate proved, no digits, no sign input,
nothing machine-checked, RH not claimed.