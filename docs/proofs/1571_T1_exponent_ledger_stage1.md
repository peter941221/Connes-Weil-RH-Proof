# 1571 — T1 exponent ledger, stage 1: saddle bookkeeping and the negative-ray obstruction

Date: 2026-09-17.

**Status: PAPER LEDGER, VERDICT OPEN.** Zero Lean, zero digits. This record
executes step T1 of record 1568 §4 at the first stage: it prices the three
phase sources into one exponent table on the off-diagonal ray variable
`u = x - y`, and it records the one nontrivial structural fact the table
already shows. Per the bone-foundry rule the verdict is NOT closed at this
stage: no route is promoted and none is killed. Consumers: (B) of map 042 and
the (★) gate (records 1502/1508/1513). RH not claimed.

## 1. The model kernel (committed transcription, T0-pinned)

Per 1568 §1-2 and record 1511 §6, the tail kernel of the compressed detector,
after Hardy-Titchmarsh conjugation, is modeled on

```text
K(u) ~ integral of  a(eta) * exp(i * Phi(u, eta))  d eta,
Phi(u, eta) = 2*pi*u*eta + theta(eta),        |amplitude root| ~ (1+eta)^-k,  k = 2
theta'(eta) = -2*pi*log|eta| + d1(eta),       |d1| <= 0.1138 * eta^-2   (T0a, record 1570)
theta''(eta) = -2*pi/eta + d2(eta),           |d2| <= 0.3067 * |eta|^-3 (T0b', record 1570)
```

valid on `eta >= 2`; the region `eta < 2` is a compact segment of the
vertical line and only needs boundedness of `psi, psi'` there, which is
classical (no asymptotics required).

## 2. Saddle-point bookkeeping on the two rays

`dPhi/deta = 2*pi*(u - log eta) + d1(eta)` vanishes once, on the principal
branch, near

```text
eta*(u) = exp(u) * (1 + r(u)),   |r(u)| <= 0.1138/(2*pi) * eta*^-2 <= 0.0181 * e^{-2u}
```

(the relative shift is T0a's residual divided by the leading slope
`2*pi/eta*`; at `u >= log 2` this is at most `0.0045`). The saddle curvature
is `|d2Phi/deta2| = |theta''(eta*)| = (2*pi/eta*) * (1 + O(eta*^-3))` by
T0b'. A single van der Corput (second-derivative test) then gives the
pointwise off-diagonal envelope `|K(u)| <~ |Phi''(eta*)|^{-1/2} *
root(eta*(u)) * (edge terms)`:

```text
ray   eta*(u)      vdc gain        root factor (k=2)     envelope        beta
----  -----------  --------------  -------------------   -------------   ------
u>0   e^u >> 1     e^{-u/2}        e^{-2u}               e^{-5u/2}      5/2
u<0   e^u << 1     e^{+u/2}        (1+e^u)^{-2} -> 1     e^{-|u|/2}     1/2
```

Threshold (1568 §3): a translation-invariant model kernel with envelope
`e^{-beta|u|}` is `L^2(R^2)` iff `2*beta > 2`, i.e. `beta > 1`.

## 3. The stage-1 finding (the ledger, not a hope)

- Positive ray: `beta_+ = 5/2 > 1`. The two classical levers (vdc + root
  symbol) DO pay for themselves there, with the phase machinery now pinned by
  T0 (the saddle shift and curvature errors are below 1% for `u >= log 2`).
- Negative ray: `beta_- = 1/2 < 1`, and this is the structural fact: the
  root-symbol lever is unreachable for `u < 0` because the saddle `eta* =
  e^u` leaves the region where ANY positive power of `(1+eta)^{-k}` decays.
  Increasing `k` cannot fix `beta_-`: the saddle is where the symbol is
  flat. So no single-phase-source improvement of the (vdc, root-symbol)
  family can make the translation-invariant model square-integrable.
- Consequently the verdict question reduces exactly to the third source, the
  projection modulation: the actual operator is `P = E - R_prolate`-type
  (records 1513/1514), its `E`-window is NOT translation invariant, and the
  only possible rescue of the negative ray is transfer of window-edge mass
  decay to the `y`-marginal. The obstruction to separating variables is the
  two-sided infinite measure of the committed carrier (record 1503:
  `chi_E` is not in `L^2`, so factorized envelopes are insufficient).

## 4. Stage-2 target and stop-rule wiring (unchanged priors)

```text
T1 stage 2 = quantify the projection-kernel modulation:
  does the E-window edge produce residual decay of the y-marginal
  along u < 0 strong enough to lift beta_- above 1 on the shell?

promotion branch: if yes -> T2 (Cotlar almost-orthogonality across Sonin
                scales with the T0 constants as inputs).
typed-stop branch: if the modulation is shown to carry NO negative-ray
                decay (separable, chi_E not in L^2, no commutator
                transfer), then multiplier-phase routes into (★) are
                typed-impossible for ANY symbol decay k and ANY phase
                residual admitted by T0: recorded as a class death,
                consistent with law F21 and the 1417 mechanism.
```

No prior is moved in this record: the stage-1 ledger shows where a positive
verdict must come from, and it is silent on whether the modulation can pay.

## 5. Boundary

Zero digits, zero Lean, zero premises consumed. (B)/(S) diagonal gates of map
042, (★), B4, rho5, R4 all stay OPEN exactly as recorded. RH not claimed.
