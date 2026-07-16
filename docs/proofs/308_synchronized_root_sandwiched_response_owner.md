# Proof 308: synchronized root-sandwiched response owner

Date: 2026-07-16

Status: closed as the time-integration interface for the continuous scalar
owner.  The theorem integrates an arbitrary measurable-index family of
root-sandwiched responses while keeping the regular two-point term and the
explicit `-2` residue inside one Bochner integrand.  The source-specific
moving `E/R/K_prol` family, its measurability estimates, and Gate 3U remain
open.

## 1. Lean owner

`RootSandwichedTrace.lean` adds

```text
integral_cc20WindowRootSandwichedResponse_eq_integral_doubleIntegral_sub_residue
```

For any `[MeasurableSpace α]`, measure `μ`, and families

```text
α -> leftRoot, rightRoot, leftKernel, rightKernel
```

it proves the exact synchronized identity

```text
∫ α,
  (root-sandwiched A†B trace at α - 2 <rightRoot α,leftRoot α>) dμ
 =
∫ α,
  (explicit two-point kernel pairing at α
   - 2 <rightRoot α,leftRoot α>) dμ.
```

The subtraction is deliberately inside the integrand.  This is the legal
owner for a future moving transport; it does not grant measurability or
integrability automatically.  Those source properties must be supplied by
the actual `E_α/R_α/K_prol` construction.

`DividedDifferenceKernel.lean` adds the matching theorem

```text
integral_cc20WindowRootSandwichedDividedDifferenceResponse_eq_integral_twoPoint
```

which exposes the root-weighted `conj(D_right) * D_left` expression under the
same time integral.

## 2. Finite moving guard

The Proof 307 guard now samples nine transport times with varying left and
right kernel phases.  It checks both the pointwise matrix/two-point readback
and the discrete time-average readback:

```text
matrix/two-point trace error: 8.411394e-19
root-weight factorization error: 1.019048e-17
residue readback error: 0
residue omission gap: 9.171834e-1
moving time-average error: 5.551708e-17
RH=UNPROVED
```

This is a finite algebraic guard, not evidence that the continuous moving
source family exists or satisfies Gate 3U.

## 3. Verification

The clean WSL2 mirror build completed successfully:

```text
Build completed successfully (2973 jobs).
```

The import-facing audits report only:

```text
[propext, Classical.choice, Quot.sound]
```

## 4. Remaining hard bone

The next source theorem must instantiate this owner with the actual synchronized
`E_α/R_α/K_prol` kernels, prove the family is measurable and trace-compatible,
and identify its complete signed scalar with the CC20 divided-difference
response.  No branchwise norm estimate, static Euler telescope, residue
deletion, or Gate 3U claim is licensed by Proof 308.
