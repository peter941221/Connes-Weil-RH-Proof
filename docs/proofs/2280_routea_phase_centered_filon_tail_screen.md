# 2280: phase-centred Filon tail screen

Date: 2026-09-30

Decision: METHOD-LEVEL NO-GO for the current floating Chebyshev-Filon profile.

## Question

Can the corrected width-a^2 owner tail on the finite window 40 <= xi <= 200 be made trustworthy by factoring out the oscillatory phase and integrating each local polynomial exactly?

## Method

For each y-panel, the amplitude is interpolated in a local Chebyshev polynomial. The factor exp(-2*pi*i*xi*y) is not sampled by Gauss-Legendre nodes; it is integrated analytically against the polynomial through monomial oscillatory moments. The prime kernel is the current-owner support-derived kernel, with 41136 visible prime powers. The computation remains a floating finite-window screen.

## Result

The trust gate fails:

```text
profile       signed integral             absolute integral
12 panels, d12   -3.4603961752115825e14      5.2643296273059006e14
18 panels, d16   -5.1728509228054170e13      1.2651752896823640e14
24 panels, d20   -3.2244732091390990e9       5.3895065122267520e9

12->18 signed movement       5.6895339279x
18->24 signed movement       1.6041468296e4x
18->24 absolute movement     2.3473789649e4x
```

The result is not a small residual drift. Increasing panel and polynomial resolution changes the answer by orders of magnitude, so the floating polynomial coefficient path is not a trustable enclosure in this cancellation regime.

## Interpretation

This rejects the present floating implementation and its current profile schedule. It does not prove that every Filon, Chebyshev, or phase transformation is impossible. A future reopening must change a named hypothesis, for example using directed interval coefficients, a stable Chebyshev-basis oscillatory moment evaluation, or an independently certified residual bound.

The prime-power count and owner hashes are preserved from the 2275 capture. No legacy 52-term kernel is used.

## Nonclaims

- The finite window is not the infinite xi tail.
- This is not an interval enclosure or an hgap supplier.
- No selected-detector readback, producer GO, or RH conclusion follows.
- The result does not close hstrip globally.

## Reproduction

```text
python scripts/routea_phase_centered_filon_tail_screen_2280.py --profiles 12:12,18:16,24:20
python -m unittest discover -s scripts -p 'routea_phase_centered_filon_selftest_2280.py' -v
```
