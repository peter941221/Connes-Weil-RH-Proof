# CC20 Source-Kernel Haar Bridge

Date: 2026-07-12

## Result

Good local result: the ordinary regular kernel is now matched to the literal
two-branch source formula, and the compact interval carries the correct
multiplicative Haar measure.

Bad route result: the previously constructed real and complex `L2` operators
use ordinary Lebesgue measure `d rho`. CC20 Theorem `thmqkey1` uses
`d*rho = d rho / rho`. Those operators therefore cannot be identified with
the source `K_I` without a new Haar-space construction or a proved weighted
unitary conjugation.

RH remains unproved.

## Primary source evidence

Source:

```text
Alain Connes and Caterina Consani,
Weil positivity and Trace formula, the archimedean place
https://arxiv.org/abs/2006.13771
```

The arXiv source file `weil-compo.tex` states:

```text
lines 571--575:
delta(rho) = 2 sqrt(rho) *
  (Si(2*pi*(1+rho))/(2*pi*(1+rho))
   + Si(2*pi*(rho-1))/(2*pi*(rho-1)))

lines 765--768:
D o Q(xi*xi*) = <xi,(-2 Id + K_I)xi>
on L2(sqrt I, d*rho)

lines 784--787:
Q_+ delta(exp(|x|)) = -2 Dirac_0 + ordinary even part

lines 803--806:
K_I(v,u) = Q delta(u/v) when u >= v,
           Q delta(v/u) when v >= u.
```

The Lean definition `cc20DeltaRegular` is term-by-term the formula at lines
571--575 because `sineIntegralQuotient x` is the continuous extension of
`Si(x)/x`. The previously proved theorem
`multiplicativeQ_cc20DeltaRegular_of_one_lt` identifies the non-diagonal scalar
with the multiplicative differential `Q`.

## Lean result

`RegularKernelCompactMeasure.lean` adds:

```text
cc20CompactHaarDensity(rho) = 1/rho
cc20CompactHaarMeasure = cc20CompactMeasure.withDensity(1/rho)
cc20CompactHaarMeasure_univ_lt_top
integral_cc20CompactHaarMeasure_eq_smul
```

`RegularKernelSourceBridge.lean` adds:

```text
cc20SourceRegularKernel
cc20SourceRegularKernel_eq_cc20RegularKernel
cc20SourceRegularKernel_of_fst_lt_snd
cc20SourceRegularKernel_of_snd_lt_fst
cc20CompactSourceHaarAction
cc20CompactSourceHaarAction_eq_weighted
```

`RegularKernelHaarL2.lean` now reconstructs the complex-linear operator on the
actual source space:

```text
cc20CompactHaarComplexL2Operator : Lp C 2 cc20CompactHaarMeasure ->L[C]
  Lp C 2 cc20CompactHaarMeasure
cc20CompactHaarComplexKernelCoefficient_continuous_input
```

For every continuous input, the operator coefficient is exactly the source
Haar action. This is an `L2` operator construction, not yet a Hilbert--Schmidt
or trace-class theorem.

The piecewise source kernel uses the continuous ordinary value on the
diagonal. This does not absorb the separate `-2 Dirac_0` distribution.

## Verification

Smallest WSL2 target:

```text
lake build ConnesWeilRH.Dev.RegularKernelSourceBridgeAudit
```

Result: passed.

Focused axioms for every audited theorem:

```text
propext
Classical.choice
Quot.sound
```

There is no `sorryAx`, project root, RH premise, or Weil-positivity premise.

## Remaining bottom

The next honest layer is Haar-product kernel square integrability and
Hilbert--Schmidt summability for this operator, followed by the quadratic-form
identity with the separate `-2 Id` term. The current theorem is not yet CC20
`thmqkey1`, a prime/pole/archimedean same-test read-off, or RH.
