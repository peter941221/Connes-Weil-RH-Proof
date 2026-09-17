# 1583 — P2: the gate's restriction functional pinned on committed definitions,
# the model verdict flips to finite, and the remaining content is one
# carrier-defect family (wave V CONT-7)

Date: 2026-09-17.

Status: PAPER SCREENING ON COMMITTED DEFINITIONS. Zero Lean, zero new digits.
This record executes brick P2 of record 1581 section 6. It pins the exact
functional behind the (star)/B4 square-sum on the committed skeleton (section
1), records the carrier-reflection structure that fixes the kernel variable as
u + u' (section 2), prices the functional at model level with the 1582
envelope — the verdict FLIPS from the pre-correction divergent reading to
FINITE (section 3) — and adjudicates the closure question honestly: the
committed prolate absorption closes only the prolate column; what remains is
one named carrier-defect family, not a phase problem (section 4). No gate is
closed; RH is NOT claimed.

## 1. The committed skeleton: the functional is two named column square-sums

All objects are committed; anchors are file:line.

```text
cc20Commutator A W = A W - W A
  (ThreeBranchCommutatorLedger.lean:27-29)
E  = radialSupportProjection        = starProjection of the log-radial
                                      support subspace
  (CCM24FiniteSProjectionTrace.lean:76-78)
Q  = sourceFourierSupportProjection = starProjection of the Fourier-support
                                      subspace  (:81-83)
R_S = sourceSoninProjection         = starProjection of the Sonin subspace
                                      (:94-96)
K_S = sourceProlateRemainder = E Q E - R_S              (:155-158)
A_S = sourceProlateHilbertSchmidtFactor = Q (E - R_S)
  (CCM24SourceProlateTrace.lean:35-38)
H  = ccm24ArchimedeanHardyTitchmarsh = FourierTransform o spectral
     reflection o scattering multiplier o FourierTransform^-1
  (CCM24HardyTitchmarsh.lean:331-336)
Fourier-support subspace = comap H (radial subspace)   (:361-366)
Sonin subspace = radial AND Fourier support            (:376-380)
```

The (star) functional — the gate column the mainline collapsed to — is the
compressed Sonin commutator column, and the committed reduction chain is:

```text
gate column  D o (R_S M - M R_S) o J o N

 (1531, bridge :681-697)   = Hardy block + prolate block
 (1532, bridge :846-866)   prolate block  <= hfactor (all-scale HS theorem,
                             committed - DISCHARGED)
 (1533/1534, bridge :510-531)
   Hardy block ((E Q E) M - M) J
     <= hradial:  Summable || D (1-E) M J N e_i ||^2
     AND  hgap:   Summable || D E (1-Q) E M J N e_i ||^2
 (1536)  hgap's operator:  E (1-Q) E M J = E H (1-E) H E M J
                             = the B4 chain of record 1573, verbatim.
```

So the pinned functional of 1581 section 6 is not a new object: it is
EXACTLY the pair of committed premises

```text
hradial  +  hgap        (bridge :514-525, shapes verbatim above)
```

with hfactor already discharged.  `P_S . (tail) . P_S` on the carrier reads,
in committed names, as the doubly-projected deviation `E(1-Q)E` — note that
`E Q E - R_S = K_S` is itself committed (:155-158): the prolate remainder IS
the doubly-projected deviation beyond the Sonin carrier, which is why 1531's
two-column split and 1532's discharge exhaust everything except these two
defect columns.

## 2. Carrier-reflection structure: the kernel variable is u + u'

Two structural facts, both from the committed definitions, that the model
reading must respect.

(a) The windows are half-lines. The radial support subspace is the `Iio`
half-line at `log lambda` (`CCM24LogRadialSupport`); the Fourier-support
condition is `H v` supported in the same half-line; the Sonin carrier is the
intersection — the double-vanishing class. On this carrier E = Q = R_S = id
(1581 section 1), so the gate column is `- D (1 - R_S) M J N`: the gate
measures the EXCURSION of `M J N` off the carrier, not propagation inside it.

(b) H does NOT commute with log translations — it REFLECTS them. From the
committed factorization H = F o S o F^-1 (:331-336) with S the spectral
reflection-plus-multiplier, a u-translation is frequency modulation, and the
reflection flips the modulation sign: `H T_c = T_{-c} H`. (The committed
translation-conjugation lemma used at
`C1G8R3CompositeBoundaryEnergy.lean:976` carries an explicit COMMUTING
hypothesis — satisfied by `rootConvolution`, not by H.) An operator
anti-commuting with translations in this way has an ANTI-difference kernel:
`k_H(u, u') = K_H(u + u')`. This is multiplicative inversion r |-> 1/r, i.e.
u |-> -u scattering, as it must be for a Hardy-Titchmarsh transform.

Consequently the 1571 section 1 model kernel `K(u) = int a(eta)
exp(i(2 pi eta u + theta(eta))) d eta` is the u + u'-kernel of the
frequency-windowed Hardy scatter (window `a` in frequency, multiplier
`m(2 pi xi) = e^{i theta}` after reflection), NOT a convolution kernel. The
1582 envelope and all its constants apply unchanged — they were proven for
the single variable `u` — but every sandwiched composite below is priced in
the variable `w = u + u'`. This sharpens the model reading; it does not
weaken it.

## 3. Model pricing: the verdict flips to FINITE

Model reading (the 1571 section 1 model): M = N = D = id, and the sharp cuts
`1_W`, `1_{W^c}` replaced by the smooth frequency window `a`. The functional's
kernel on a bounded window W x W is assembled from K(w) and its
window-integrated composites; with 1582 the model kernel obeys

```text
||a||_1 = pi/2   (the window),   ||K||_inf <= ||a||_1 = pi/2,
||K||_2 < infinity   (negative ray 43 (1+|u|)^-2, positive ray
                      beta_+ = 5/2, bounded middle — 1582 sections 2-5);
the HS bound below consumes ||K||_2 only.
```

and therefore

```text
|| E H Pi H E ||_HS^2  <=  int_W int_W |K(u + u')|^2 du du'
                        =   int_W du * int |K(w)|^2 dw      (Jacobian 1)
                        <=  |W| * ||K||_2^2  <  infinity.
```

Every further composite with bounded factors keeps HS-ness by the committed
Hilbert-Schmidt ideal lemmas (the 1532 toolset: bounded pre/post-composition
preserves column square-summability), so the two defect column square-sums
are finite for ALL bounded D, M, N at model level.

Verdict, and what flipped. Before this wave the ledger's negative-ray row
(beta_- = 1/2) read the same functional DIVERGENT under the threshold prose
"envelope e^{-beta|u|} is L^2 iff 2 beta > 2". That reading is now superseded
three times over: the premise was unsound (1581: zone violation + smooth
compact zone), the threshold prose was never satisfiable literally (1581
section 4), and the paid envelope makes the model kernel square-integrable on
the whole line with no beta-threshold in sight (1582). At model level the
(star) functional is FINITE. The negative ray is permanently off the
obstruction list.

## 4. Adjudication: not closure — one named residue family

The gap between the model and the gate consists of exactly two effects, and
they are one family.

```text
(a) sharp-cut counter-term. The true cuts are indicators; (sharp - smooth)
    is the non-local counter-term (third manifestation: 1578 section on the
    counter-term tail, 1580 termwise-split death). By F29 it has no named HS
    source — it is not a rootConvolution column, and no committed lemma
    prices it.

(b) physical M-transport. The actual M moves support by at most log q per
    adjoint Euler transport (1572-1576 ledger), breaking both the window
    alignment and the anti-difference reading of the composite kernel. This
    is the hM premise (1535's slot; the content of the 1576 stop).
```

Committed coverage status of the two premises:

```text
hradial: HAS a finite-window closure for the root factor under the
         wide-window premise (C1G8R3CompositeBoundaryEnergy.lean:911-922),
         but that chain hardwires rootConvolution (F29) and consumes hwide —
         its remaining content is exactly (b) for a general physical M.
hgap:    NO committed estimate. It is B4's content, i.e. the gate's
         remaining content (1498's audit conclusion stands: both diagonal
         gates OPEN).
```

Adjudication of 1581 section 6's question. The corrected model kernel plus
the committed prolate absorption does NOT close the gate: the prolate
absorption closes only the prolate column (hfactor, 1532); the model prices
the two defect columns FINITE but contains no mechanism for (a) or (b). What
the wave has actually established is sharper than either the old divergence
or a bare reopen:

```text
The (star)/B4 gate is NOT a phase/asymptotics problem anymore. The model is
HS with explicit constants. What remains is a CARRIER-GEOMETRY problem: one
family — sharp cuts plus transport, the non-local counter-term — standing
between the model kernel and the true composed kernel.
```

This re-scopes the 1576 typed stop a second time: its driving premise was
withdrawn in 1581, and the lever class it stopped (multiplier-phase) is now
superseded in kind — no multiplier or phase mechanism can be the remaining
content, because carrier vacuity (1581 section 1) voids modulation at the
gate and section 3 above voids the asymptotic objection. The stop file
remains on disk as the pre-registered class record; its scope is hereby
narrowed to "carrier-defect family", and any future attempt must name a
mechanism for (a)+(b), not a phase.

## 5. Boundary

Moved: the functional is pinned on committed definitions (two named premises,
hradial + hgap, with hfactor discharged); the kernel variable is fixed as
u + u' by the committed reflection structure; the model verdict is FINITE
with explicit constants (|W| * ||K||_2^2 bound); the remaining content is
re-scoped to one carrier-defect family (sharp cuts + transport). NOT moved:
hradial and hgap are both OPEN as premises; (star), B4, rho5, R4, (OB)/W1 all
OPEN; nothing is machine-checked; no sign input anywhere; RH NOT claimed.
