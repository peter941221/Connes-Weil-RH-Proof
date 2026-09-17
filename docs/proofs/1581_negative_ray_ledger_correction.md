# 1581 — negative-ray ledger correction: the 1571 β₋ row extrapolates T0 outside
# its own validity zone, the compact-zone phase is smooth, and the sole driving
# datum of the 1572 death and the 1576 typed stop is unsound (wave V CONT-5)

Date: 2026-09-17.

Status: PAPER SCREENING CORRECTION. Zero Lean, zero digits. This record
executes the wave's own F26/F27 discipline (read committed source before
deriving) against the phase wave's screen and finds the screen's negative-ray
row invalid twice over — once by zone violation inside its own text, once by
the smoothness of the compact-zone phase, which is an immediate consequence of
the committed phase transcription. The correction REOPENS a screen, not a
gate: (★), B4, ρ5, R4, (OB)/W1 all stay OPEN, nothing is machine-checked, and
RH is NOT claimed.

## 1. Two committed facts the wave had not assembled

```text
(1) The source carrier is the Sonin intersection
    ccm24ArchimedeanSoninClosedSubspace = radialSupport ∩ FourierSupport
    (CCM24HardyTitchmarsh.lean:376-380), and the Fourier-support space is
    comap H of the radial space (:361-366), with H involutive (:349-357).
(2) On the source carrier the two window projections act as the IDENTITY:
    radialSupportProjection ∘L sourceInclusion = sourceInclusion and
    sourceFourierSupportProjection ∘L sourceInclusion = sourceInclusion are
    COMMITTED lemmas, used as hEJ/hQJ at
    C1G8R3BoundaryOutputFactorizationBridge.lean:428-429.
```

Consequence A (carrier vacuity, with scope). For any bounded X defined on the
ambient carrier, `J† ∘L X ∘L E ∘L J = J† ∘L X ∘L J` and likewise for Q:
the window factor adjacent to J on the carrier side absorbs. Every
E/Q-interaction mechanism is therefore ALGEBRAICALLY void at the gate — not
merely power-insufficient (1572's asymptotic verdict). The scope is exact:
windows separated from J by non-carrier-preserving factors see nontrivial
vectors; that is precisely why the hM premise (`E M J = M J`, 1535's
shortcut slot) is a live hypothesis and not a triviality. Any future rescue
of the tail gate must come from (i) the restriction geometry — the doubly
projected deviation `P_S · (tail) · P_S` on the quadrant-type Sonin class,
the slot the committed prolate absorption (1531/1532) was built for — or
(ii) carrier-defect identities of hM shape. This sharpens 1572's typed death
from "edge terms are power-insufficient" to "the modulation has no leverage
at the gate at all".

## 2. The zone violation, verbatim

The model kernel's phase is pinned by T0 (record 1570):

```text
theta'(xi)  = -2*pi*log|xi| + d1(xi),   |d1(xi)| <= 0.1138 * xi^-2
theta''(xi) = -2*pi/xi     + d2(xi),   |d2(xi)| <= 0.3067 * |xi|^-3
```

with the validity zone stated explicitly in both records:

```text
1570 §3: "xi >= 2 so tau >= 2*pi > 6"          (the Stieltjes rows)
1571 §1: "valid on eta >= 2; the region eta < 2 is a compact segment ...
         and only needs boundedness of psi, psi' there"
```

The 1571 saddle table (§2) prices the negative ray with

```text
eta*(u) = exp(u),   vdc gain = |Phi''(eta*)|^{-1/2} = (2*pi/eta*)^{-1/2}
                    = e^{u/2},   envelope e^{-|u|/2},   beta_- = 1/2.
```

For every u < 0 the saddle sits at eta* = e^u < 1 < 2 — OUTSIDE the zone
where both T0 bounds hold, and the curvature `2*pi/eta*` used in the gain is
the ASYMPTOTIC-zone formula. The record's own correction term confirms the
break: `|r(u)| <= 0.0181 * e^{-2u}` becomes VACUOUS for u < 0 (the bound
diverges), i.e. the saddle's location and curvature are unpinned exactly
where the u<0 row prices them. The row also extrapolates the root factor
`(1+eta*)^{-2} -> 1` — harmless there — but the decay gain is wholly
inherited from the invalid curvature.

## 3. The compact zone is smooth: no saddle exists on the negative ray

The phase is not merely asymptotic; it has a closed form (committed
transcription, 1511 §6 via `logDeriv_GammaR_eq_log_pi_add_digamma`;
restated in 1570 §1):

```text
theta'(xi) = -2*pi*( Re psi(1/4 - pi*i*xi) - log pi ).
```

psi is analytic at 1/4 (Gamma's poles are the non-positive integers), and
psi(1/4) = -gamma - pi/2 - 3*log 2 is finite; hence theta' is C^infinity on
ALL of ℝ and bounded on every compact interval. Set

```text
B := sup_{eta in [0,2]} |theta'(eta)|   <   infinity
     (effectively computable from the same digamma bounds; order
      2*pi*(log pi + 4.23) ~ 34, the exact value not needed for the verdict).
```

Now price dPhi/deta = 2*pi*u + theta'(eta) on the two zones, for u < 0:

```text
asymptotic zone eta >= 2:   dPhi/deta = 2*pi*(u - log eta) + d1(eta)
                            <= 2*pi*(u - log 2) + C1/4  <  0   strictly
                            (T0a at eta = 2; -2*pi*log eta decreases further)
compact zone (0,2):         |dPhi/deta| >= 2*pi*|u| - B  >  1
                            once |u| > U0 := (B+1)/(2*pi).
```

So for u < -U0 the phase has NO critical point anywhere on (0, infinity).
One integration by parts on each zone gives |K(u)| = O(|u|^{-1}); N-fold
integration by parts gives O(|u|^{-N}) for every N once the higher theta
rungs are paid — the same DLMF §5.11 Stieltjes machinery as 1570 §2, where
each psi-derivative gains one power, with the same sec-factor discipline
(F18) and the same sentinel pattern. Until those rungs are paid, the SAFE
unconditional statement is the O(|u|^{-1}) first rung; the superpolynomial
statement is routine, not speculative.

The 1571 row's `e^{u/2}` decay was therefore an artifact of evaluating
`|Phi''|^{-1/2}` at a curvature the model does not own at that point. The
truth is STRONGER decay than recorded, i.e. the screen OVERSTATED the
negative-ray kernel mass. (Direction of the error: against the gate —
the overstatement is what made the model look divergent under the
threshold reading then in force.)

## 4. What this re-opens, and what it does NOT

- The 1572 typed death and the 1576 typed stop fired on the conjunction
  "beta_+ > 1 AND beta_- > 1", failing on beta_- = 1/2 "for ANY symbol
  decay k". That datum is unsound as filed (§2-3). The 1576 stop remains on
  disk as the pre-registered class record, but its DRIVING PREMISE is
  withdrawn here; the multiplier-phase lever class re-opens as
  UNADJUDICATED. The stop's own scope guard (1576 §1.1) anticipated exactly
  this failure mode: "the model may misprice a structured input".
- The threshold sentence itself ("a kernel with envelope e^{-beta|u|} is
  L^2(R^2) iff 2*beta > 2") is never satisfiable under its literal reading:
  a translation-invariant kernel on the full plane has infinite diagonal
  mass for ANY decaying envelope, so no beta passes. The operative
  functional for every committed consumer is a RESTRICTION to the thin
  carrier (Finding 1), under which even the recorded beta_- = 1/2 envelope
  converges (half-line crossing: int_0^infinity u e^{-u} du = 1). The next
  ledger row must pin its functional before pricing exponents against it.
- This record does NOT prove (★), hgap, or B4. The screen is a model; the
  true composed tail kernel is not translation-invariant (the sharp-cut
  smearing — the non-local counter-term structure, third manifestation
  1578/1580). Removing an invalid obstruction is not building the estimate.
- Unchanged and re-affirmed: carrier vacuity (§1) means NO window-edge or
  modulation mechanism can close the tail; the only live content is the
  restriction geometry plus the committed prolate absorption slot, and the
  carrier-defect (hM-shape) identities.

## 5. Law F30 (zone-anchored asymptotics)

- An asymptotic formula may be evaluated only inside its stated validity
  zone; a saddle, edge, or extremum that leaves the zone is re-priced from
  the receiving zone's own committed bounds (compact zone => bounded
  derivatives => computable threshold + integration by parts). A residual
  bound that DIVERGES at the evaluation point (here |r(u)| <= 0.0181
  e^{-2u} for u < 0) is a flag that the pricing is void, not a small
  correction.
- A divergence verdict must name its FUNCTIONAL — which integral over which
  domain, restricted how — and the named functional must be finite for some
  admissible kernel; otherwise the beta-threshold is vacuous prose and the
  verdict does not price anything.

## 6. The two-brick positive program (priced here, scheduled by owner)

```text
P1 (negative-ray lemma, Lean-able after one T0-extension):
    T0_3+ rungs: |theta^(k)(xi) - d/dxi^k(-2 pi log|xi|)| <= C_k |xi|^{-2-k}
    for |xi| >= 2, k >= 3 (same Stieltjes rows; each derivative gains a
    power; same sentinel pattern), then the no-saddle lemma:
    |K(u)| <= C_N (1+|u|)^{-N} on u <= -U0 for the model kernel, all N.
    No sign input, no primes, committed-adjacent only.
P2 (restriction functional):
    Pin the exact functional of the gate on the Sonin carrier —
    the HS norm of P_S . (tail) . P_S — and adjudicate whether the
    corrected model kernel plus the committed prolate absorption
    (sourceSoninCommutator_sourceBasis_normSq_summable_of_hardySubId_*)
    closes it. This is where (star) actually lives.
Then: re-run the 1571 ledger with the corrected row and re-scope the
1576 stop (owner decision card below).
```

## 7. Boundary

Moved: 1572's negative-ray reason and 1576's driving premise are recorded as
superseded-in-premise (files retained verbatim); the multiplier-phase class
re-opens UNADJUDICATED; law F30 registered; the carrier-vacuity fact and its
exact scope are now written. NOT moved: (★), B4, ρ5, R4, (OB)/W1 all OPEN;
nothing machine-checked; no sign anywhere; RH NOT claimed.
