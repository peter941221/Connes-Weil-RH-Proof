# Loewner--Bernstein Route Rejection

Date: 2026-07-12

Status: the complete coupled finite Weil source has the exact algebraic shape
of a Loewner divided-difference kernel in the even positive-frequency sector.
However, its continuous generating function is strictly decreasing between
`x=1/4` and `x=1` for every tested prime cutoff. It cannot be an
operator-monotone or complete Bernstein function, so the standard positive
measure / Loewner theorem cannot supply an unconditional lower proof.

## 1. Exact Loewner Reduction

Let `psi_c(t)` be the odd continuous source whose full divided-difference
matrix is the cutoff-free assembly

```text
Q_(c,N) = W_02 - W_R - W_p.
```

For positive integer frequencies `j,k`, contract the full matrix against the
normalized even vectors `(e_j+e_-j)/sqrt(2)`. Its off-diagonal entry is

```text
B_(j,k)
  = (psi_c(j)-psi_c(k))/(j-k)
    + (psi_c(j)+psi_c(k))/(j+k).
```

Define

```text
Phi_c(x) = sqrt(x) psi_c(sqrt(x)), x>0.
```

Then

```text
B_(j,k)
  = 2 * (Phi_c(j^2)-Phi_c(k^2))/(j^2-k^2).
```

Thus the positive-frequency even block is twice the Loewner matrix of
`Phi_c` on the squared nodes. This identity is elementary algebra, not an RH
criterion.

The exact source recovered from the official closed forms is

```text
psi_c(t)
 = C_c t/(t^2+beta^2)
   + (S_c(t)+P_c(t))/pi,

beta = log(c)/(4 pi),
C_c = log(c)(sqrt(c)+1/sqrt(c)-2)/(2 pi^2),
S_c(t)
 = Im digamma(1/4+i pi t/log(c))/2
   - (2 pi t/log(c))
       sum_(r>=0) exp(-(2r+1/2)log(c))
         /((2r+1/2)^2+(2 pi t/log(c))^2),
P_c(t)
 = sum_(q=p^a<=c) log(p)/sqrt(q)
     sin(2 pi t log(q)/log(c)).
```

## 2. Necessary Condition And Certified Failure

An operator-monotone function on `(0,infinity)` is scalar nondecreasing. A
complete Bernstein function is in particular operator-monotone. Therefore

```text
Phi_c(1/4) > Phi_c(1)
```

is a complete rejection of both standard Loewner routes.

The probe uses the official `arb_ldlt_certify.py` closed forms with Arb
interval arithmetic. It first checks every off-diagonal Loewner identity on
the nodes `1^2,...,4^2`, then evaluates the continuous counterexample:

```text
+-----+----------------------+----------------------+----------------------+
| c   | Phi_c(1/4)           | Phi_c(1)             | difference           |
+-----+----------------------+----------------------+----------------------+
| 13  | 0.809796796348...    | 0.0457203442394...   | +0.764076452109...   |
| 29  | 1.431809500384...    | 0.0372917932764...   | +1.394517707107...   |
| 100 | 3.039164047946...    | 0.0252144735760...   | +3.013949574370...   |
+-----+----------------------+----------------------+----------------------+
```

At `c=13`, Arb additionally encloses the secant slope by

```text
(Phi_c(1)-Phi_c(1/4))/(1-1/4)
  = -1.01876860281155683189...,
```

strictly below zero. The intervals have radii below `5e-25` in the displayed
runs, so the failure is not numerical ambiguity.

## 3. What This Does And Does Not Reject

```text
rejected:
  derive Q_(c,N)>=0 from an operator-monotone or complete-Bernstein theorem
  for this explicit coupled Gamma--prime source;

not claimed:
  finite matrix positivity is false;
  every possible nonlocal positive representation is impossible.
```

Finite Loewner matrices at the particular integer-square nodes can be positive
even when the continuous function is not operator-monotone. The certified
positive finite matrices therefore do not repair the failure. Conversely, a
dense basis change or a Cholesky factor calculated from positive inertia would
consume the sign conclusion and is not a lower representation.

## 4. Reproduction

With the official arXiv:2607.02828 source bundle unpacked and `python-flint`
available:

```text
python3 -B docs/proofs/055_loewner_bernstein_probe.py \
  --upstream anc/arb_ldlt_certify.py --c 13 --N 4 --prec 768
```

Repeat with `--c 29` and `--c 100` for the other certified rows.

## 5. Verdict

```text
even-block Loewner reduction: passed exactly
operator-monotone / complete-Bernstein necessary monotonicity: false
positive-measure Loewner proof: rejected
finite coupled positivity: remains an RH-level Weil gate
new Lean owner: none
unconditional RH: unproved
```

Sources:

```text
https://arxiv.org/abs/2607.02828
official e-print ancillary file anc/arb_ldlt_certify.py
docs/proofs/055_loewner_bernstein_probe.py
```
