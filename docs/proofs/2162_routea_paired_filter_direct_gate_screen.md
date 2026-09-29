# 2162 — Direct selected-g screen for the paired finite-zero filter

Date: 2026-09-29.

Status: NUMERICAL CANDIDATE / NO PRODUCER GO. This record is a direct
`ICgate(g.square)` screen, separate from the four-point vertex determinant.
The owner is still an under-approximation and no RH claim follows.

## Entry contract

The healthy B5 consumer is the same selected detector `g` with its exact
support-derived finite visible-prime set:

```
ICgate(g.convolutionSquare) <= 0
 -> orbitWindowSemiLocalGate(g)
 -> qw(g) >= 0
 -> SourceRH.
```

For the numerical model, `rho=0.945+39.25244858548658 i`, `N=0`, and the
owner consists of 21 known positive-height zeros inside the committed ball,
their conjugates, and the three nonzero target values. It is not the complete
abstract closed-ball source owner. The filter uses the exact finite-zero
construction with carrier width `a=2.5`, the same 2143 float coefficient
family, `m=1600` seed quadrature, and the complete 34059-entry visible
prime-power book for support radius `12.9`. The pre-registered target is a
negative direct C value, with both prime-kernel and FFT prime reads negative,
all prime powers covered, and edge mass below `1e-8`.

## Screen and controls

The first width scan (record 2159) gave:

```
width   support   C_A           C_B           A/B relative spread
1.5     11.9       +0.02516296   +0.02660568   5.42e-2
2.0     12.4       +0.01299697   +0.01441569   9.84e-2
2.5     12.9       -0.03895132   -0.03763280   3.50e-2
```

The width-2.5 row is a useful sign candidate but fails the registered `1e-3`
cross-route agreement gate. A wide-window retry (record 2160) is invalidated
by the evaluator horizon: on `[-40,40]` the last-five-unit mass is `0.99858`
for `m=1600` and `0.999968` for `m=3200`, with their direct-B values differing
by `0.982`. This is an alias-dominated control failure, not evidence for a
larger negative margin.

On the trusted `[-20,20]` window, direct prime-kernel B is stable:

```
             C_A             C_B             |A-B|
m=1600,h=.01  -0.03895132296  -0.03763279514  1.3185e-3
m=1600,h=.005  -0.03902261794  -0.03763279514  1.3898e-3
m=3200,h=.01  -0.03895132295  -0.03763279512  1.3185e-3
```

The B-grid and B-rule relative movements are `1.29e-12` and `3.82e-10`,
respectively; every visible prime power is covered and edge mass on
`15<=|xi|<=20` is below `5.5e-26`. Thus the direct B sign is reproducible
for this finite model, but the independent A read carries an absolute
uncertainty roughly `3.7%` of `|C_B|`, above the registered route gate.

## Decision

`DIRECT-FILTER-SCREEN-ONLY`. The finite known-zero model supplies a smaller
numerical target: certify the direct physical-kernel sign with a rule whose
absolute error is below `0.0376` and then transfer it to the complete owner.
Neither step is available. The formal sign-orientation theorem in record 1931
also says the actual healthy selected geometry has `ICgate(g.square)>0` under
the hypothetical off-line-zero assumptions; therefore this negative
under-approximation cannot be substituted for the selected owner. The
complete-owner transfer, full-line interval integral, uniform correction
membership, and formal C3' sign remain open. No producer Go or route ruling
changes.

Evidence: scripts and artifacts `2159`, `2160`, and `2161`; all numerical
runs completed through `scripts/run_resource_aware_task.sh` with exit zero.

Intake screen: GAP fired on the words "error" and "margin". The cited
1590–1634 exhibit concerns an imported theorem whose remainder exceeds its
claimed margin. Here the A/B difference is explicitly booked as an observed
cross-evaluator uncertainty, with no imported theorem or claimed rigorous
bound. This is a vocabulary trigger, not a clearance of the numerical
candidate.
