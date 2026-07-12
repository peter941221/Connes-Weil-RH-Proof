# 107 Selected Weil Formula Local Owner Exists

Date: 2026-07-12

## Existing source owner

The repository already has a fixed-square local owner in
`Source/CCM25Concrete/SelectedWeilFormula.lean`:

```text
SelectedWeilSquareOwner
  sourceTest          : CompactLogTest
  supportRadius       : ℝ
  convolutionSquare   : CompactLogTest
  convolution square support bound

SelectedFinitePrimeSupportData.ofOwner
  exact finite global/restricted prime-power sets for this square

SelectedWeilFormulaOwner
  poleTerm
  archimedeanTerm
  globalFinitePrimeTerm
  restrictedFinitePrimeTerm
  weilValue
```

`SelectedFinitePrimeSupportData.ofOwner` proves exact support by bounding every
nonzero prime term with `n < ceil(exp supportRadius)+1`. This is a genuinely
per-square construction and does not quantify over every ambient Schwartz test.

`SelectedArchimedeanIntegrability.lean` additionally proves the archimedean
integral for every selected square and exposes

```text
SelectedWeilFormulaOwner.ofCompactLogTest
```

so the complete pole/archimedean/prime formula owner has no external analytic
premise.

## Consequence

The finite-prime obstacle in proofs 094-095 is not a mathematical obstacle for
the fixed detector. Plan 028 can use this owner instead of
`ConcreteCCM25ArithmeticPackage`.

The remaining transport is explicit:

```text
SelectedWeilFormulaOwner.weilValue
  = source QW of the same convolution square
  = negative CC20/M4 Weil-side quantity (or a proven inequality)
```

The first equality is not currently present as a theorem; the selected formula
currently defines `weilValue` directly from its pole, archimedean, and prime
terms. The second is the M4/CC20 same-test inequality.

## Verdict

```text
fixed-square finite prime owner: pass
broad ForAllTests package: bypassed
source QW read-off: open
CC20/M4 fixed-square inequality: open
```
