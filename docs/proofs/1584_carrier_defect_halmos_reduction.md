# 1584 — carrier-defect brick: the window is a half-line (1583 §3 erratum),
# the exact two-term Halmos decomposition of hgap with committed names, hradial
# closed by the strip trick, and the gate reduced to ONE named tail-trace
# functional (wave V CONT-8)

Date: 2026-09-17.

Status: PAPER DERIVATION ON COMMITTED DEFINITIONS. Zero Lean, zero digits, no
sentinel (every constant below is structural — Lambda, sqrt(Lambda) — and the
one decay rate quoted is the committed 1571 positive-ray row; per F27 no
numerics are opened). This record executes the post-1583 brick. It (1) pins
the committed window as a HALF-LINE and files an erratum to 1583 section 3,
(2) derives the exact decomposition `E(1-Q)E = (E - R_S) - K_S` in committed
names, (3) closes the K_S term by the committed all-scale HS theorem, (4)
closes hradial (the 1498/1576 residue) by strip-confinement plus the
compact-window HS trick, replacing the wide-window premise `hwide`, and (5)
splits the remaining angle term into a closed compact part and ONE named
residual — the carrier tail-trace functional, the Halmos two-projection form
of the classical Sonin-thinness theorem. No gate is fully closed; the gate's
remaining content is now a single named object. RH NOT claimed.

## 1. The window is a half-line (committed), and 1583 section 3 is corrected

Committed anchors:

```text
CCM24SoninScale = {lambda : ℝ // 0 < lambda}      (bare positive real)
ccm24LogRadialLowerRegion lambda = Set.Iio (Real.log lambda)
  (CCM24LogRadialSupport.lean:30-32)
radial support subspace = ker of the restriction to that region
  (:40-52) = functions supported in [log lambda, +infinity)
```

So W = [L, infinity), L = log lambda — INFINITE measure. Two consequences.

Erratum (1583 section 3). The bound `||EH Pi HE||_HS^2 <= |W| * ||K||_2^2`
is void as stated (|W| = infinity). The correct model pricing on the
half-line window substitutes w = u + u': for u, u' in [L, infinity) the fiber
{u : u in W, u' = w - u in W} is [L, w - L], nonempty iff w >= 2L, with
length w - 2L. Hence

```text
||E H Pi H E||_HS^2 = int_{2L}^{inf} (w - 2L) |K(w)|^2 dw
```

and finiteness comes from the decay of K, not from finite measure:
(i) w in [2L, U0] is a compact band (K bounded, 1582); (ii) for w >= U0 the
compact-eta piece of the even-folded model integral is parts-bound (|Phi'| >=
pi w uniformly on |eta| <= 2 by the B1 cap, same mechanism as 1582 section 5)
giving O(w^-N); (iii) the saddle piece has eta* = e^w >= 2 for w >= log 2, so
it lies INSIDE the T0 validity zone (F30-valid — unlike the negative-ray row
1581 killed), and the committed 1571 row gives |K(w)| <= C_+ e^{-(5/2) w}.
The weighted integral converges with the linear Jacobian weight absorbed.
The FINITE verdict of 1583 stands; the mechanism is corrected.

Model-object note (honesty). The 1582 kernel K is the frequency-windowed
single-H object (1571's model); the actual defect composite is the two-H
u-cut object `E H (I-E) H E`. These are genuinely different operators (a u-
cut is frequency convolution, not a frequency multiplier), so the model
pricing above is INDICATIVE of the composite, not a computation of it. The
exact pricing of the composite is section 3's decomposition — which is why
the structural reduction below, not the model, is load-bearing.

## 2. The exact two-term decomposition (committed names only)

For two orthogonal projections, E(1-Q)E = E - EQE. Insert the committed
objects R_S = sourceSoninProjection (projection onto the Sonin carrier
E and Q) and K_S = sourceProlateRemainder = EQE - R_S
(CCM24FiniteSProjectionTrace.lean:155-158):

```text
E (1-Q) E  =  (E - R_S)  -  K_S          [R_S cancels: exact identity]
```

Since the carrier inclusion J satisfies EJ = J and R_S J = J (committed:
bridge :219, :428-429), the hgap column splits EXACTLY:

```text
D E (1-Q) E M J N  =  D (E - R_S) M J N   -   D K_S M J N .
                        (i) angle-excursion        (ii) prolate term
```

## 3. Term (ii) is closed by the committed all-scale theorem

K_S = A_S^dagger A_S with A_S = Q (E - R_S) the committed prolate factor
(CCM24SourceProlateTrace.lean:35-42), and the all-scale theorem gives A_S
square-summable on the named global basis (1532). Bounded precomposition
transfers the square-sum to any source basis (committed HS ideal lemmas, the
1532 toolset), and D, M, N are bounded, so

```text
|| D K_S M J N ||^2  <=  ||D||^2 ||K_S||_HS^2 ||N||^2   <  infinity.
```

Closed, no new analysis. Note what was NOT used: no sign, no phase, no
asymptotics — the prolate leg was always the committed HS source (F29) and
this is where it pays.

## 4. hradial is closed by the strip trick (the 1498/1576 residue paid)

The radial boundary defect is `D (1-E) M J N`. Let Lambda = Lambda(p::S) =
log prod q be the total left-transport budget of the physical M (the
1575/1576 transport ledger: only adjoint Euler transports move support, each
by <= log q; right-transports do not move support left). Every carrier vector
is supported in [L, infinity), so M J N e_i is supported in [L - Lambda,
infinity), and (1-E) keeps only the strip [L - Lambda, L). For the pure
transport part M = T_{-Lambda},

```text
(1-E) T_{-Lambda} J  =  T_{-Lambda} o M_{1_{[L, L+Lambda)}} o J ,
```

and multiplication by the compact-window indicator IS Hilbert-Schmidt with

```text
|| M_{1_{[L, L+Lambda)}} ||_HS^2 = Lambda .
```

Hence

```text
|| D (1-E) M J N ||^2  <=  ||D||^2 Lambda ||N||^2 ,
```

with the mixed-direction case identical after paying only the left-moving
budget (the right-moving factors never enter the strip). This is a
quantitative replacement for the wide-window premise `hwide` consumed by the
committed finite-window radial closure
(C1G8R3CompositeBoundaryEnergy.lean:911-922): where `hwide` demanded
`E'' M J = M J` as a hypothesis, the transport ledger DELIVERS it at scale
lambda' = lambda e^{-Lambda} (the 1575 hM' finding). Status: typed-closable
at paper level; the one Lean brick it owes is "transport ledger =>
propagation budget => hwide at scale lambda'" — then the committed closure
fires unchanged. hradial moves from OPEN (1498) to CLOSED-PENDING-ONE-BRICK.

## 5. Term (i): the compact part closes; the tail is the named residual

Split the transported support at L + Lambda:

Compact part. `(E - R_S) E_{<= L+Lambda} M J`: the same window pull-back as
section 4 gives `E_{<= L+Lambda} M E_{>= L} = T_{-Lambda} o M_{1_{[L-Lambda,
L+Lambda]}}` (length 2 Lambda), so

```text
|| (E - R_S) E_{<= L+Lambda} M J N ||^2  <=  2 Lambda ||D||^2 ||N||^2 .
```

Closed by the same trick (the angle projection (E - R_S) is a contraction).

Tail part — THE residual. What remains is

```text
D (E - R_S) E_{> L+Lambda} M J N ,
```

whose square-sum is bounded by the trace form

```text
Tr_carrier( M^dagger E_{> L+Lambda} (E - R_S) E_{> L+Lambda} M )
   <=  Tr_carrier( M^dagger E_{> L+Lambda} M )          [(E-R_S) <= E]
   ~=  Tr_carrier( E_{> L+2 Lambda} )                   [pure transport]
```

— the CARRIER TAIL-TRACE FUNCTIONAL: the total squared tail mass of the
Sonin carrier beyond a shifted threshold. In the Halmos two-projection
picture, (E - R_S) is the direct sum of the angle blocks (eigenvalues
sin^2-type, the angle spectrum), so this functional is the angle spectrum
of the pair (E, Q) sampled on the carrier's tail — the quantitative form of
Sonin/Hardy thinness. This is the precise content of 1581 section 6's
`P_S . (tail) . P_S`, and it is the gate's remaining content, now a single
named object.

Plausibility and attack vehicle (typed, not claimed): the carrier is
H-invariant (H(E and Q) = Q and E), infinite-dimensional, and thin; the
committed all-scale prolate machinery (1532) constructs exactly the kind of
basis with controlled localization that prices a tail trace; the residual
should fall to the same machinery at the shifted window. If it falls, hgap
is closed and with it (star) for the physical factors; if it diverges, the
Sonin carrier's angle spectrum is genuinely fat and the route is
structurally re-typed — both outcomes are decisive (F30's naming discipline
makes this a fair fork).

## 6. Ledger

```text
+------------------------------------+-------------------------------------+
| premise                            | status after this record            |
+------------------------------------+-------------------------------------+
| hfactor (prolate leg)              | CLOSED (committed, 1532)            |
| hradial (radial boundary defect)   | CLOSED-PENDING-ONE-BRICK (strip     |
|                                    | trick + transport=>hwide bridge)    |
| hgap: term (ii) D K_S M J N        | CLOSED (section 3)                  |
| hgap: term (i) compact part        | CLOSED (strip trick, 2 Lambda)      |
| hgap: term (i) tail part           | OPEN — carrier tail-trace           |
|                                    | functional (Sonin thinness)         |
+------------------------------------+-------------------------------------+
```

The gate's remaining content is now ONE named functional, down from "two
defect columns" (1534/1583) — and it is a thinness statement about the
carrier, not a phase or asymptotics statement, consistent with the 1583
re-typing.

## 7. Boundary

Moved: window pinned as the half-line [log lambda, infinity); 1583 section 3
corrected (mechanism, not verdict); exact decomposition with committed names;
three of the four defect pieces closed with explicit structural constants;
hradial's route to formalization named (one transport bridge brick); the
residual isolated as the carrier tail-trace functional in Halmos form. NOT
moved: the tail functional is OPEN; nothing machine-checked; hgap as a whole
is OPEN until it falls; (star), B4, rho5, R4, (OB)/W1 all OPEN; no sign input
anywhere; RH NOT claimed.
