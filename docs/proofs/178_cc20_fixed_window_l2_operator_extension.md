# Proof 178: fixed-window L2 operator extension on the common carrier

## Route obligation

Replace the continuous-input-only window action by a genuine bounded operator
on the complete restricted `Lp` space, then transport it to the common global
`Lp C 2 volume` carrier.

## Result

`GlobalLogKernel.lean` now defines, for every `lambda > 1`,

```text
cc20GlobalLogWindowRestrictedL2Operator
  : Lp C 2 (volume.restrict (cc20LogWindow lambda)) ->L[C] cc20GlobalLogL2

cc20GlobalLogWindowL2Operator
  : cc20GlobalLogL2 ->L[C] cc20GlobalLogL2
```

The second operator is the first one composed with
`LpToLpRestrictCLM`, so it is a genuine common-carrier realization of the
finite-window `P_lambda K P_lambda` action.

The extension is built with `LinearMap.extendOfNorm` from the dense range of
`BoundedContinuousFunction.toLp`.  On that dense core, Lean proves

```text
globalWindowL2Operator (globalWindowInputToLp u)
  = globalWindowRegularActionToLp u
```

for every bounded continuous `u`.  The operator estimate is

```text
‖globalWindowL2Operator u‖
  ≤ ‖cc20WindowHaarComplexL2Operator lambda hlambda‖ * ‖u‖.
```

The constant is finite-window dependent; no uniform-in-`lambda` assertion is
made.

The output-side window invariant is also proved on the complete space:

```text
cc20LogWindowProjection lambda hlambda ∘SL
  cc20GlobalLogWindowRestrictedL2Operator lambda hlambda
  = cc20GlobalLogWindowRestrictedL2Operator lambda hlambda.
```

It is obtained by proving the indicator idempotence on the dense core and
using `LinearMap.extendOfNorm_unique`.

The input-side identity is also proved on the public carrier:

```text
cc20GlobalLogWindowL2Operator lambda hlambda ∘SL
  cc20LogWindowProjection lambda hlambda
  = cc20GlobalLogWindowL2Operator lambda hlambda.
```

Thus both sides of the fixed-window map are explicitly restricted to the same
window subspace.

## Verification

Using the retained WSL2 Lake cache:

```text
lake build ConnesWeilRH.Source.CC20Concrete
lake env lean ConnesWeilRH/Dev/GlobalLogHaarAudit.lean
```

Both commands pass (`3496/3496`).  The focused declarations have only:

```text
propext
Classical.choice
Quot.sound
```

`git diff --check` is clean for tracked changes, and the new source contains no
`sorry`, `admit`, or `axiom` declaration.

## Boundary

This closes only the fixed-window operator layer.  It does not prove strong
compatibility or convergence as `lambda -> infinity`, a uniform three-point
bad-space bound, the diagonal `-2 Dirac_0 -> -2 Id` identity, the same-test
CC20 trace read-off, or the final unconditional RH consumer.
