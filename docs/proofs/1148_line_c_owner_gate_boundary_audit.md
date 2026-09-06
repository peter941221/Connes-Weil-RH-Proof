# Record 1148 - Line-C owner/gate boundary audit

Date: 2026-09-06.

Status: FORMAL interface audit. Consumer: the healthy `CompactLog`, B5-shaped
detector-specific P2 route. RH is not claimed.

## What the existing owner actually supplies

The formal orbit construction in
`C1HealthyYoshidaUnscaledOrbit.lean` supplies, on one selected owner,

```text
g = selectedOwner base correction n
```

and finite raw interpolation equations for
`laplaceAt ((convolutionIterate base n).convolution correction) z` at the
registered orbit, pole, and detector nodes. It also supplies the selected
owner's support, triple-vanishing detector data, square-zero readback, and
vertical tail estimates.

The correction producer is deliberately surjective at finitely many Laplace
nodes (`exists_residualWindow_correction`). Its contract therefore controls
node values, not the full test function.

## Gate-side readback

`C1LocalConfigurationDomination.lean` defines

```text
ICdefect g s w lam = g - Σ i in s, lam i • w i
```

and proves the exact pointwise archimedean expansion
`archimedeanIntegrand_ICdefect` and the gate expansion
`ICgate_ICdefect`. For the one-window owner,
`C1T2Assembly.defectGate_singleton_eq_sub` gives

```text
ICgate(defect) = ICgate(g.square) - ICgate(W.square).
```

After triple vanishing, record 1143 further rewrites this as

```text
ICgate(defect) = qw(W) - qw(g),
```

or equivalently as the spectral difference of the two Hermitian squares.

## Boundary and required next theorem

No current declaration connects the finite raw node equations to either
`archimedeanTerm` or `finitePrimeSum` of the selected owner. Consequently the
existing interpolation data cannot discharge `hbudget` or manufacture a sign
for `ICgate(defect)`. This is an owner/interface boundary, not a Lean tactic
gap.

The next admissible Line-C producer must therefore prove a new, genuinely
analytic cancellation statement on the same owner, for example an exact
finite-dimensional or low-rank representation of the correction contribution
to `qw(W) - qw(g)`. A triangle/norm envelope would only reproduce the already
refuted Stage-B scale route (records 1140 and 1142).

This audit does not retire Line C. It narrows the target from “use the node
equations” to “derive a gate-level cancellation identity from those equations
plus additional analytic structure.”

## Evidence classification

The owner and gate equations cited above are FORMAL Lean declarations. The
conclusion about the missing bridge is an interface audit based on the
available formal API; it is not a numerical sign claim.
