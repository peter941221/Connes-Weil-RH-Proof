# 098 Named QW--CC20 Bridge Lacks a Numerical Equality

Date: 2026-07-12

## Code audit

`Route/Bridge.lean` defines a structure named
`SourceQWEqualsNegCC20WeilSum`, but its fields are only:

```text
sourceQWUsesCommonTest
sourcePsiSignExpansion
traceLegality
positiveTraceNonnegative
signsAndNormalizations
mellinHalfDensityConvention
sourceFinitePrimeSignOwnedByPackage
sourcePoleSignInCC20LocalSum
```

There is no field asserting a numerical equality between `W.qw f f`, a CC20
local Weil sum, and the positive trace.

The actual numerical bridge appears separately in
`Route/CC20RouteRealization.lean`:

```text
NormalizedRouteBackedYoshidaLocalSumReadOff data :=
  weilLocalSum(starConvolution detector) = -positiveTrace(...)
```

and `NormalizedRouteBackedYoshidaSignWitness` stores this read-off as a field.
The theorem proving nonpositivity simply rewrites by that stored equality and
uses positive-trace nonnegativity.

## Consequence for Plan 028

A fixed-detector arithmetic owner does not derive the decisive sign bridge.
Even after proving exact prime support, pole normalization, and local QW
formulas, the route still needs the same-object theorem

```text
local Weil sum of the genuine convolution square
  = - CC20 positive trace of the matching archimedean test.
```

This is the old M0/M3 source identity in a sharper form. It must be proved from
the CC20 kernel/trace construction; it cannot be inherited from the misleadingly
named `SourceQWEqualsNegCC20WeilSum` bundle.

## Verdict

```text
Plan 028 local arithmetic type: pass
existing named sign bundle: semantically insufficient
decisive local-sum numerical equality: open
route status: unchanged
```

