# Record 2000 - A-V finite variational probe preregistration

Date: 2026-09-26.

Status: pre-registration. This file is committed before the run. No theorem,
no Lean result, and no RH claim.

## Consumer and owner

Consumer:

```text
same healthy selected CompactLog owner g
  -> same-owner qw(g) >= 0
  -> SourceRH
```

The probe uses the committed Route-A EXT owner constructor from records 1994
and 1996. It preserves the owner nodes, node values, support family,
finite visible-prime cutoff, grouped physical aggregate, and gate instrument.
It changes only the coefficient selector inside an overcomplete source family.

## Registered cases

```text
case        delta   gamma       scale
G5-H        0.10    30.424876   0.92
G5-W        0.10    30.424876   0.90
G7-H        0.10    37.586178   0.92
G8-H        0.10    40.918719   0.88
```

The first and last three cases are committed host locations from the 1994/
1996 audits. G5-W is an adjacent-window control. No cases may be added after
seeing the output.

## Selector

For each owner node, use two distinct width copies of the committed profile
family. Let M be the exact owner interpolation matrix and y be either the
base target vector or the correction target vector. Among all complex
coefficient vectors c satisfying M c = y, select the minimum H1 energy:

```text
E(c) = integral (abs(f_c(x))^2 + abs(deriv f_c(x))^2) dx
```

The numerical H1 Gram matrix uses fixed Gauss-Legendre quadrature and the
same Gevrey profile as the committed family. The solve uses a Hermitian
spectral cutoff of 1e-12 times the largest eigenvalue, reported as
conditioning data. This cutoff is a numerical stability rule, not a theorem.

No residual-budget inequality, sign conclusion, or RH statement is inserted
as a constraint. The only equality constraints are the existing owner
interpolation conditions.

## Measurements

For each case and for both base/correction selectors, report:

```text
constraint residual;
H1 energy and coefficient norm;
Gram condition and effective rank;
gate C, B01, D, determinant;
certified route spread;
finite visible-prime count;
margin proxy = -D / (1 + H1_base + H1_corr);
baseline comparison from the committed selector.
```

The gate calculation uses the committed `gate_entries` instrument and its
three-route certification rule. No new prime model is allowed.

## Decision rules

```text
A-V-GO-CANDIDATE:
  all four cases are feasible;
  interpolation residual <= 1e-6;
  effective rank is full at the registered cutoff;
  C > 0, D < 0, det < 0;
  all live route spreads are < 1/3;
  no margin proxy is nonpositive.

A-V-NO-GO:
  any case is infeasible, rank-deficient, non-physical, or has
  nonpositive D/determinant margin after route certification.

A-V-UNRESOLVED:
  a case is numerically ill-conditioned at the registered cutoff or
  violates the instrument's finite-route coverage rule.
```

A-V-GO-CANDIDATE is not a proof. It only authorizes the next desk: derive a
continuum representer/duality bound and a genuine physical-cost constant.
A-V-NO-GO kills this selector mechanism under this owner family; it does not
kill all Route A mechanisms.