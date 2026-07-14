# Proof 243: Finite-Window Mellin Riesz Rows

Date: 2026-07-14

Status: accepted as an axiom-clean same-carrier Mellin-row bridge. Actual
finite-S control-space containment, the semilocal remainder sign, and RH
remain open.

## 1. Result

`GlobalLogMellinRows.lean` constructs, for every complex Mellin node `s`, the
continuous log-window row

```text
r_s(t) = conjugate(exp(s t))
```

and the source-test input

```text
x_g(t) = g(exp(t)).
```

Mathlib's complex inner product is conjugate-linear in its first argument, so
the exact finite-window identity is

```text
<r_s,x_g>
  = integral_[ -log(lambda), log(lambda) ] g(exp(t)) exp(s t) dt
  = Mellin(g,s).
```

The second equality requires the explicit source condition

```text
support(g) subset (1/lambda,lambda).
```

This condition is what makes a global Mellin value recoverable from this
particular finite window. It does not contradict
`not_global_mellin_one_factors_through_cc20CompactRestriction`, which rejects
such a factorization for arbitrary global tests on one fixed window.

The principal declarations are:

```text
cc20LogMellinRow_inner_testInput_eq_logIntegral
cc20LogMellinRow_inner_testInput_eq_mellin
cc20LogMellinRow_inner_testInput_eq_fourier
cc20LogMellinRow_inner_testInput_eq_mellinAt
```

## 2. Exact Carrier Transport

The row and source input are transported through the already proved
isometries, not reconstructed independently:

```text
compact log-window subtype L2
        |
        | cc20LogWindowSubtypeRestrictedL2IsometryEquiv.symm
        v
restricted logarithmic L2
        |
        | cc20WindowHaarRestrictedLogL2IsometryEquiv.symm
        v
finite-window Haar L2
```

The restricted-log carrier owns
`cc20GlobalLogWindowRestrictedL2Endomorphism`; the Haar carrier owns
`cc20WindowHaarComplexL2Operator`. The read-off therefore refers to the same
carriers used by the compact remainder, rather than to an abstract basis with
Mellin labels attached later.

The compactness consumers use the opposite inner-product orientation. The
module proves it explicitly:

```text
<x_g,r_s> = conjugate(Mellin(g,s)),
<x_g,r_s> = 0  iff  Mellin(g,s) = 0.
```

The conjugate is harmless only for the zero equation; omitting it from a
nonzero value identity would be incorrect.

## 3. Finite Node Geometry

For a finite `Finset` of complex nodes, the module defines actual row families
on both exact carriers:

```text
cc20RestrictedLogFiniteMellinRows
cc20WindowHaarFiniteMellinRows
```

The existing theorem `fixed_window_finite_mellin_surjective` can prescribe
arbitrary Mellin values at those nodes with one test supported in the same
window. Pairing a hypothetical row relation with these interpolating inputs
therefore proves:

```text
linearIndependent_cc20RestrictedLogFiniteMellinRows
linearIndependent_cc20WindowHaarFiniteMellinRows
```

This proves that distinct finite nodes contribute the expected number of
independent row directions. It does not prove that their span contains the
compact bad space, and it does not make a finite family dense in the full
`L2` carrier.

## 4. Same-Object Control Contract

`exists_finite_cc20WindowHaarMellinControlSpace` now places all of the
following on one Haar object:

```text
finite-dimensional compact control space
actual finite Mellin Riesz rows
source input with the same support window
cc20WindowHaarComplexL2Operator - 2 Id
```

Its remaining premise is displayed rather than stored:

```text
controlSpace <= span(actual finite Mellin rows).
```

Once that containment and the matching finite Mellin zero equations are
provided, the theorem proves the shifted Haar quadratic form is nonpositive.
Thus the Riesz-vector identity is no longer the bottom. The next mathematical
producer is the actual finite-S control-space containment for the negative
Yoshida owner, followed by the Burnol/semilocal same-object identification.

## 5. Verification

The Windows source was copied one way into the isolated WSL2 ext4 mirror. The
following builds passed:

```text
flock -w 1800 /tmp/connes-weil-rh-lake.lock \
  lake build ConnesWeilRH.Source.CC20Concrete.GlobalLogMellinRows

flock -w 1800 /tmp/connes-weil-rh-lake.lock \
  lake build ConnesWeilRH.Dev.GlobalLogMellinRowsAudit

flock -w 1800 /tmp/connes-weil-rh-lake.lock \
  lake build ConnesWeilRH.Source.CC20Concrete
```

The focused audit checks the complete theorem types and reports only:

```text
propext
Classical.choice
Quot.sound
```

No `sorryAx`, project axiom, route premise, or new RH-level root appears.

## Route Judgment

```text
finite-window Mellin Riesz identity:        accepted in Lean
restricted-log/Haar same-carrier transport: accepted in Lean
finite-node row linear independence:        accepted in Lean
finite-S control-space containment:         open
finite-S semilocal sign:                    open
RH:                                         unproved
```
