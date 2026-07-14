# Proof 221: target-zero Chebyshev pairing

Date: 2026-07-13

Status: exact finite-orbit residue calculation and reproducible numerical
check.  A hypothetical off-critical four-point zero orbit contributes `+2m`
to the weighted Chebyshev defect operator for the value pattern from Proof
077.  Because Proof 220 subtracts that defect, the same orbit contributes
`-2m` to the Weil form.  Retaining the target-zero residue therefore recovers
the negative detector signal; it does not produce the missing finite-S
positivity theorem or prove RH.

## 1. Weighted Chebyshev owner

Write every prime power as `q=p^r`, with `Lambda(q)=log(p)`, and define

```text
M(B)
 = sum_(q<exp(B)) Lambda(q)/sqrt(q)
     -2(exp(B/2)-1).                                  (C.1)
```

For `Re(z)>1/2`, its Laplace--Stieltjes transform is

```text
integral_[0,infinity) exp(-zB) dM(B)
 = sum_q Lambda(q) q^(-z-1/2)
     -integral_0^infinity exp(-(z-1/2)B) dB
 = -zeta'/zeta(z+1/2)-1/(z-1/2).                     (C.2)
```

The second term in `(C.2)` cancels the pole of zeta at `1`.  This is the
spectral transform of the same signed measure used in Proof 220:

```text
dM(B)
 = sum_q Lambda(q)/sqrt(q) Dirac_(log q)
     -exp(B/2) dB.                                    (C.3)
```

Thus `(C.2)` is not a new explicit-formula convention.  It is the exact
Laplace transform of the finite-prime/PNT-main difference `E_c` already
defined there.

## 2. One isolated centered zero

Let `rho` be a nontrivial zero of multiplicity `m` and center it at

```text
u=rho-1/2.
```

Near `z=u`, the zero contributes the principal part

```text
-m/(z-u)                                               (C.4)
```

to `(C.2)`.  Inverting this one residue gives the distributional contribution

```text
dM_u(B)=-m exp(uB) dB,                                (C.5)
M_u(B)=-m (exp(uB)-1)/u.                              (C.6)
```

Here `u!=0` for an off-critical target.  Formula `(C.5)` is an isolated-pole
statement: it does not assert pointwise or absolute convergence of the sum
over every zeta zero.  A finite orbit may be separated by residues first and
paired with a compactly supported test; the remainder stays a distribution.

## 3. Autocorrelation factorization

Let `h` be a complex compactly supported logarithmic test, and assume its
support diameter is strictly less than `T=log(c)`.  Put

```text
F_h(b)=integral_R conjugate(h(x)) h(x+b) dx,
C_h(b)=F_h(b)+F_h(-b),
H(v)=integral_R exp(vx) h(x) dx.                       (C.7)
```

The bilateral Laplace transform of the one-sided autocorrelation factors:

```text
Phi_h(v)
 := integral_R exp(vb) F_h(b) db
  = conjugate(H(-conjugate(v))) H(v).                 (C.8)
```

Indeed, set `y=x+b` and separate the two integrals:

```text
integral_R integral_R
  exp(v(y-x)) conjugate(h(x)) h(y) dx dy
 = conjugate(integral_R exp(-conjugate(v)x)h(x)dx)
     * integral_R exp(vy)h(y)dy.                      (C.9)
```

The source condition `H(1/2)=0` also keeps this calculation on the genuine
Q-root range.  Define

```text
xi(x)=exp(-x/2) integral_(-infinity)^x exp(t/2)h(t)dt. (C.9a)
```

Then `(d/dx+1/2)xi=h`.  Before the support of `h` the integral is zero; after
the support it equals `H(1/2)=0`.  Hence `xi` is compactly supported as well.
The other two rows `H(0)=H(-1/2)=0` are exactly the remaining transported
source conditions from Proof 220.  No generic raw-root test is substituted
for the same-object Q-root here.

Because `F_h(b)=0` for `|b|>=T`, the pair of centered zeros `u,-u` contributes
to the finite-cutoff defect exactly

```text
Defect_(u,-u)(h)
 = -m integral_0^T
     (exp(ub)+exp(-ub)) C_h(b) db
 = -m (Phi_h(u)+Phi_h(-u)).                           (C.10)
```

The second equality follows by expanding `C_h` and changing `b` to `-b` in
the two `F_h(-b)` terms.  No reality assumption on `h` or `u` is used.

The strict support-diameter condition also makes the cutoff convention at
`B=T` irrelevant: the autocorrelation vanishes there.

## 4. Full off-critical orbit

For a nonreal off-critical zero, the centered functional-equation and
conjugation orbit is

```text
O(u)={u,-u,conjugate(u),-conjugate(u)}.                (C.11)
```

All four points have the same multiplicity.  Summing `(C.10)` over the two
opposite pairs gives

```text
Defect_O(u)(h)=-m sum_(v in O(u)) Phi_h(v).            (C.12)
```

Proof 077 assigns the transform values

```text
H(u)=1,
H(-conjugate(u))=-1,
H(conjugate(u))=H(-u)=0.                              (C.13)
```

The four square values are therefore

```text
+----------------+----------------+------+----------------------+--------+
| v              | -conjugate(v)  | H(v) | H(-conjugate(v))    | Phi(v) |
+----------------+----------------+------+----------------------+--------+
| u              | -conjugate(u)  |  1   | -1                   |  -1    |
| -conjugate(u)  | u              | -1   |  1                   |  -1    |
| conjugate(u)   | -u             |  0   |  0                   |   0    |
| -u             | conjugate(u)   |  0   |  0                   |   0    |
+----------------+----------------+------+----------------------+--------+
```

Consequently,

```text
sum_(v in O(u)) Phi_h(v)=-2,
Defect_O(u)(h)=+2m.                                   (C.14)
```

This fixes the sign that remained open at the end of Proof 220.

## 5. Why the sign does not close positivity

Proof 220 gives, on the genuine Q-root `h=L xi`,

```text
QW_c(h,h)
 = <h,2 theta'(D)h>+||xi||^2-<h,E_c h>.               (C.15)
```

The target orbit in `(C.14)` belongs to `<h,E_c h>`.  Its contribution to
the right side of `(C.15)` is therefore

```text
-Defect_O(u)(h)=-2m.                                  (C.16)
```

This is exactly the negative off-line-zero signal constructed in Proof 077.
The residue has not created a compensating positive budget; the passage

```text
prime measure - continuous PNT main
  -> isolated target-zero residue
  -> autocorrelation square value
```

has merely transported the same Weil detector contribution through the
Chebyshev owner.

This result is still useful.  A compact cutoff argument must preserve the
finite target orbit while controlling the non-target residue distribution.
Equation `(C.14)` shows that preserving it retains a fixed negative margin.
What it cannot do is prove that a genuine semilocal positive owner equals the
whole expression in `(C.15)`, or that the remaining same-domain terms have the
required sign.

## 6. Reproduction

The companion script constructs one actual complex compactly supported test,
not just four independent numbers.  Seven translated smooth bumps solve the
joint interpolation problem

```text
H(-1/2)=H(0)=H(1/2)=0
```

together with `(C.13)`.  It then computes the autocorrelation independently
and checks `(C.8)`, `(C.10)`, and the full-orbit sign `(C.14)` under grid
refinement.

The default WSL run has interpolation condition number `3.765890e3` and
maximum interpolation residual `1.987113e-14`.  On the `8001`-point grid, the
independent autocorrelation calculation gives

```text
orbit defect = 2.0000000000 - 3.143e-12 i,
pair relative error = 6.495e-12.
```

```text
python3 -B docs/proofs/221_target_zero_chebyshev_pairing.py
```

The proof is the residue and change-of-variables calculation
`(C.2)--(C.14)`.  The numerical experiment is a guard against a conjugation,
translation-orientation, pairing, or outer-minus-sign error.

## 7. Route judgment

```text
isolated-zero Chebyshev residue:          exact distributionally
opposite-pair autocorrelation identity:   exact
Proof 077 four-point zero sum:            -2m
target-orbit contribution to E_c:         +2m
target-orbit contribution to QW_c:        -2m
target residue as positive producer:      rejected
negative detector margin under cutoff:    retained
finite-S same-object positive owner:       still open
Lean owner or route rewire:                none
RH:                                        unproved
```
