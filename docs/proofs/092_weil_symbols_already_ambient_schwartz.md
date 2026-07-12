# 092 Weil Symbols Already Use Ambient Schwartz Carrier

Date: 2026-07-12

## Source evidence

`ConnesWeilRH/Basic.lean:41-50` defines:

```text
abbrev TestFunction := SchwartzMap ℝ ℂ

structure WeilFormSymbols where
  qw : TestFunction -> TestFunction -> ℝ
  qwLambda : ℝ -> TestFunction -> TestFunction -> ℝ
  psi : TestFunction -> ℝ
  convolutionStar : TestFunction -> TestFunction -> TestFunction
  ...
```

Thus the CCM25-facing Weil carrier is already the ambient Schwartz space. The
full legacy-equivalence issue in proofs 085-086 is confined to the source
construction layer; it does not require a new Weil-form carrier or a new route
type.

## Consequence for Plan 026

Instantiate the source algebra with `Test = TestFunction`, identity legacy
encoding, and the Mathlib Schwartz convolution. Then construct
`WeilFormSymbols` on the same carrier. The Lean probe in proofs 090-091 proves
the convolution and compact-witness transport needed at the function level.

The remaining work is source-data ownership:

```text
ambient convolution square
  -> source psi / pole / archimedean terms
  -> finite-prime package and visibility rows
  -> CC20 support-square trace on the same TestFunction
```

No type-level API rewrite is needed for this version of the plan.

## Verdict

```text
ambient carrier: already present
Weil-symbol carrier compatibility: pass
true convolution owner: probe pass
compact witness square transport: probe pass
arithmetic/trace source package reconstruction: open
```

