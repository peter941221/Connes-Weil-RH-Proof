# Proof 307: continuous root-sandwiched two-point readback

Date: 2026-07-16

Status: closed as an axiom-clean analytic interface.  The generic continuous
root-sandwiched `A†B` trace owner now has an explicit two-point integral form,
and the CC20 divided-difference specialization factors that scalar into root
weights and an ordered product of the two continuous divided-difference
kernels.  The moving `E/R/K_prol` same-object identity and Gate 3U remain open.

## 1. New interface

For continuous kernels `K_left` and `K_right` on the compact CC20 window, the
new theorem

```text
cc20WindowRootSandwichedPairData_trace_eq_doubleIntegral
```

proves

```text
Tr(A†B)
 = ∫ y, ∫ x,
     conjugate(K_right^root(y,x)) * K_left^root(y,x)
       dμ(x) dμ(y).
```

The proof starts from the existing legal section-inner-product trace theorem,
uses `ContinuousMap.inner_toLp`, and closes the remaining pointwise order with
commutativity of `ℂ`.  No infinite trace cycle is introduced.

The response-level theorem

```text
cc20WindowRootSandwichedResponse_eq_doubleIntegral_sub_residue
```

keeps the source residue as the separate scalar

```text
-2 * inner(rightRoot, leftRoot).
```

The atom is therefore not hidden in a continuous kernel diagonal.

## 2. CC20 divided-difference specialization

For `CC20DividedDifferenceData` witnesses `leftData` and `rightData`,

```text
cc20WindowRootSandwichedDividedDifference_pair_apply
```

proves the pointwise factorization

```text
conj(root-sandwich_right) * root-sandwich_left
 = (conj leftRoot(y) * leftRoot(y))
   * (conj rightRoot(x) * rightRoot(x))
   * conj(D_right(y,x)) * D_left(y,x).
```

The response theorem

```text
cc20WindowRootSandwichedDividedDifferenceResponse_eq_twoPoint
```

then gives the exact continuous source scalar:

```text
∫ y, ∫ x,
  |leftRoot(y)|² |rightRoot(x)|²
  * conjugate(D_right(y,x)) * D_left(y,x)
  dμ(x)dμ(y)
- 2 * inner(rightRoot,leftRoot).
```

Here `D` is the segment-average derivative from Proof 306, equal off the
diagonal to `i/pi * (f(s)-f(t))/(s-t)` and equal on the diagonal to the same
continuous derivative witness.  The displayed expression is the scalar form
that a future continuous Hardy/moving-projection bridge must consume.

## 3. Verification

In a clean WSL2 ext4 verification mirror, run:

```text
flock -w 1800 /tmp/connes-weil-rh-lake.lock \
  lake build \
    ConnesWeilRH.Source.CC20Concrete.RootSandwichedTrace \
    ConnesWeilRH.Source.CC20Concrete.DividedDifferenceKernel \
    ConnesWeilRH.Dev.RootSandwichedTraceAudit \
    ConnesWeilRH.Dev.DividedDifferenceKernelAudit
```

Result: `Build completed successfully (2972 jobs)`.

The import-facing audits report only:

```text
[propext, Classical.choice, Quot.sound]
```

There is no `sorryAx`, project axiom, or stored source-identification premise
in the new theorems.

## 4. Route judgment

```text
continuous A†B trace legality                 closed
section trace -> explicit two-point integral  closed
divided-difference root factorization        closed
explicit -2 residue ownership                preserved
moving E/R/K_prol same-object equality       open
Gate 3U                                       open
finite-S sign, Burnol identity, RH           unproved
```

This proof is a producer for the continuous scalar interface.  It does not
claim that the supplied divided-difference kernel is already the moving
outer/second-support/prolate owner.  Proof 303's finite bridge still requires a
continuous source identification before any compact-support estimate.
