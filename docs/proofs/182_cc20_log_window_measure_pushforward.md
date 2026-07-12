# Proof 182: logarithmic window measure pushforward

## Result

`GlobalLogKernel.lean` now proves the exact finite-window measure identity

```text
Measure.map (cc20LogWindowExpPoint lambda hlambda)
  (cc20LogWindowBaseMeasure lambda)
  = cc20WindowHaarMeasure lambda hlambda
```

The proof compares integrals of every real compactly supported continuous map
on the Haar window. The logarithmic side is reduced to the interval integral
by `integral_subtype_comap`; the Haar side uses the existing density formula
for `d rho / rho`. `Measure.ext_of_integral_eq_on_compactlySupported` then
gives equality of measures. No measure equality is stored as input data.

The same file packages the equality as
`measurePreserving_cc20LogWindowExpPoint` and obtains the inverse preserving
map from the `exp/log` homeomorphism.

## Verification

Using the retained WSL2 Lake cache:

```text
lake build ConnesWeilRH.Source.CC20Concrete.GlobalLogKernel
lake env lean ConnesWeilRH/Dev/GlobalLogHaarAudit.lean
```

Both passed. The focused declarations use only:

```text
propext
Classical.choice
Quot.sound
```

## Boundary

This is finite-window measure transport. It does not prove whole-line
operator convergence, the diagonal `-2 Dirac_0 -> -2 Id` identity, the same-
test CC20 trace read-off, or unconditional RH.
