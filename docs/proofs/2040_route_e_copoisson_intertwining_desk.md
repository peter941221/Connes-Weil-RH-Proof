# Record 2040 — Route E desk: co-Poisson intertwining (theta/Poisson identity)

Date: 2026-09-27.

Status: DESK REGISTRATION ONLY. No scan, no Lean, no producer claim, no RH
claim. Registered subject to law F82 (sign-conservation-under-splitting,
[2039](2039_route_d_closure_sign_conservation.md)).

## 1. Mechanism (what it is)

Burnol's co-Poisson intertwining, from "On Fourier and Zeta(s)"
(arXiv:math/0112254, Forum Math. 16 (2004); see also "Entrelacement de
co-Poisson", Ann. Inst. Fourier 57 (2007) no. 2, 525-602):

```text
F( sum_{n != 0} g(t/n)/|n|  -  (int_R g(1/x)/|x| dx) * 1 )
    =  sum_{m != 0} g(m/u)/|u|  -  (int_R g(y) dy) * 1
```

(F = Fourier transform; sums over nonzero integers; valid pointwise for
smooth g compactly supported away from the origin; also proven as an
identity of tempered distributions, and as a corollary of Euler-Maclaurin
summation, jointly with Candelpergher.)

Transcription caveat: the formula above is transcribed from the source
abstract text and the slashes restored by hand from the paper's proof
section. The first brick re-derives it from Euler-Maclaurin on the owner
before any use (the repo law: never trust a transcribed constant/formula).

Properties recorded in the source:

```text
- the prototype formula is "directly equivalent to the functional equation
  of the Riemann zeta function";
- at the level of the left Mellin transform, co-Poisson acts as
  multiplication by zeta(1 - s);
- both sides are Schwartz functions constant, together with their Fourier
  transforms, near the origin;
- the source builds Hilbert spaces HP_lambda and vectors Z_{lambda,rho,k}
  associated with the non-trivial zeros, and discusses a Krein string of
  the zeta function.
```

## 2. Why this is interesting for THIS repository

```text
(a) The transcription bridge already exists and is committed: record 109
    (docs/proofs/109_burnol_selected_weil_formula_alignment.md) verified
    that the selected owner's weilValue is EXACTLY Burnol's explicit
    formula pairing under g(u) = u^(-1/2) f(log u): pole side, finite-prime
    local terms (vonMangoldt(n) n^(-1/2) [f(log n) + f(-log n)]), and the
    archimedean integrand up to the -2 f(0)/(e^y + 1) term whose integral
    cancels against the constant-term difference. Nothing has to be
    re-derived to speak Burnol's language on the actual owner.

(b) The owner is in the admissible class: CompactLog support is a log
    window [-L, L], so g lives on [e^(-L), e^L], compact and away from the
    origin - exactly where the intertwining holds pointwise with no
    distributional caveat.

(c) The intertwining is the exact reconciliation machine for the two
    channels every dead route tried to estimate: it EXCHANGES the
    sum-over-integers channel (discrete, prime-side shaped) with the
    integral channel (archimedean shaped) as Fourier transforms of one
    another. Routes A/B died estimating this reconciliation; the
    intertwining states it as an identity.
```

## 3. Non-circularity requirement (law F82)

Route D died because splitting an identity and dominating part of it
conserves the sign gap (record 2039). Route E is admissible ONLY in shapes
that are not split-and-dominate:

```text
(E1) NORM SHAPE: weilValue(g_actual) is exactly a norm-squared or an inner
     product in a co-Poisson-equivariant space (candidate: Burnol's
     HP_lambda). Then qw >= 0 becomes a placement/support statement about
     where the owner's mass sits relative to the intertwining - decidable
     in principle by the repository's exact support algebra (the
     vanishing-support identities already formalized in the 1838-era
     bricks).

(E2) EXCHANGE SHAPE: the archimedean signed term is the exact intertwining
     image of a positive prime-side term at a different scale, with the
     remainder equal to ZERO by support algebra (not by domination).

Any other shape (residual r(g) "controlled by" the positive part) is dead
on arrival under F82 and must not be registered.
```

## 4. First decisive brick

One identity plus one finite exact verification, no estimation:

```text
B1. Re-derive the intertwining from Euler-Maclaurin (one page, on the
    owner's g class) and transcribe weilValue(g_actual) exactly as a
    matrix coefficient of the co-Poisson operator S on the committed
    17-dimensional one-copy span (record 2037 basis).

B2. Compute the exact remainder r of that transcription (algebra, not
    intervals) and test its structure:
      r == 0 by support algebra                    -> E2 live;
      r is an S-equivariant (intertwining eigen/shift) term -> E1 live;
      r is a generic signed residual               -> Route E dead (F82).
```

Kill conditions, checked in this order:

```text
(k1) RECORD-111 SCOPE: 111 (log-Poisson positive trace read-off death)
     rejected factoring L = 2 log(1+a) I - log((I - aU)^* (I - aU)) to
     read a positive trace off a HALF-LINE boundary. The co-Poisson
     intertwining is a full-line exact exchange with no boundary term for
     compactly-supported-away-from-origin data - the two share only the
     word "Poisson". Nevertheless k1 requires: verify on the ACTUAL window
     that no boundary term appears when S is compressed to the owner's
     span (the compression is a cut, and record 111's death was precisely
     a cut-induced boundary). If an uncontrollable boundary flux appears,
     Route E dies with 111's scope extended.

(k2) F67 SHAPE: if the HP-space norm or the transcription requires any
     hypothesis equivalent to Weil positivity / RH, the route is an
     inadmissible import (same verdict class as Velez, record 1995).

(k3) F82 SHAPE: Section 3's test.
```

## 5. Provenance

```text
literature:      Burnol, On Fourier and Zeta(s) (arXiv:math/0112254);
                 Entrelacement de co-Poisson (AIF 57, 2007).
project fact:    record 109 alignment on the selected owner (committed).
new derivation:  none yet; B1/B2 are the registered first work items.
formal proof:    none.
```

## 6. Decision

```text
Route E: REGISTERED AS DESK (map 109). No numeric scan, no Lean, no
producer status. First work item: k1 scope check + B1 identity. A wave may
close Route E only through (a) the B2 structure test firing (dead), or
(b) the B1/B2 identities landing with r == 0 or r S-equivariant (live,
then and only then price E1/E2 consumer wiring to qw(g) >= 0).
```

No RH claim.
