# Latest Loewner, Herglotz, And Prolate Source Screen

Date: 2026-07-13

Status: the checked 2026 sources supply exact finite-coordinate, prime-event,
Herglotz, and prolate-interlacing theorems. None supplies the missing sign of
the complete arithmetic Weil block or the same-object finite-S semilocal
remainder. Combining the isolated positive archimedean tail with the prime
parity law does not change that verdict. RH remains unproved.

## 1. Result First

```text
+----------------------+-------------------------------+------------------------------+
| source               | exact reusable result         | missing target               |
+----------------------+-------------------------------+------------------------------+
| Zenodo 20710075      | prime Loewner formula;        | full prime-block sign;       |
|                      | C-direction sign              | odd competition inequality   |
+----------------------+-------------------------------+------------------------------+
| Zenodo 20737111      | parity Loewner identities;    | arithmetic operator          |
|                      | generic monotone theorem      | monotonicity / bottom order  |
+----------------------+-------------------------------+------------------------------+
| Zenodo 20694588      | exact rank-one Herglotz       | uniform scalar inequality    |
|                      | reduction                     | left explicitly open         |
+----------------------+-------------------------------+------------------------------+
| arXiv:2607.02828     | positive totally-positive    | complete Weil or prime sign  |
|                      | archimedean tail increment    |                              |
+----------------------+-------------------------------+------------------------------+
| Zenodo 21242028      | exact prime-event velocity    | positivity between events    |
|                      | jump and event dictionary     |                              |
+----------------------+-------------------------------+------------------------------+
| Zenodo 21326823 v4   | simple, strictly interlacing  | bridge from negative CM      |
|                      | negative CM prolate spectrum  | prolate to Weil form         |
+----------------------+-------------------------------+------------------------------+
```

No theorem in the right column is a cosmetic API gap. Each is the sign or
same-object bridge needed by the RH consumer.

## 2. Prime Loewner Formula

Zenodo 20710075 proves for a finite Galerkin vector `v`

```text
<v,Pv>
 = -2 sum_(q=p^k<=c) Lambda(q)/sqrt(q) * omega_q
     integral_0^1 Re(conj(W_v(-2*pi*omega_q*t))
                     *W_v(2*pi*omega_q*(1-t))) dt.
```

Primary source:

```text
https://zenodo.org/records/20710075
loewner-note_final.tex:83-108
```

For the one vector `C=cosh(x/2)`, positivity of its Fourier symbol makes every
prime term nonpositive. That result is source lines 118-166. It is a
directional statement

```text
<C,P C> < 0,
```

not `P<=0` on the even sector. The same source proves no odd sign: lines
171-226 derive mixed prime contributions and leave their competition
inequality open.

## 3. Why The Positive Archimedean Tail Does Not Complete It

Theorem 3.2 of arXiv:2607.02828 proves that, at fixed `(c,N)`, the isolated
post-band archimedean increment

```text
Delta_(T1,T2)=Q_arch,T2-Q_arch,T1
```

is positive definite and strictly totally positive. Section 4 explicitly
states that this concerns only the isolated archimedean increment, not the full
Weil block or the prime block:

```text
https://arxiv.org/html/2607.02828v1#S3.Thmtheorem2
https://arxiv.org/html/2607.02828v1#S4
```

There is no implication from

```text
A is strictly totally positive,
<C,P C><0
```

to the inertia or lowest parity eigenvalue of `A+P`. The exact two-dimensional
countermodel is

```text
A   = [[2,1],[1,2]],        C=(1,0),
P_1 = [[-1,0],[0,0]],       P_3=[[-3,0],[0,0]].
```

`A` has positive entries and positive determinant, while both prime proxies
satisfy `<C,P_j C><0`. Nevertheless

```text
A+P_1 is positive definite,
A+P_3 is indefinite.
```

Thus the two source theorems do not determine even the sign of the sum. In the
actual arithmetic matrix the obstruction is stronger: the odd prime terms
already have mixed sign, and the pole, Gamma, and prime Rayleigh values cancel
to exponentially small total margins; see Proofs 044 and 056.

## 4. Operator-Monotone And Herglotz Reductions

Zenodo 20737111 proves the algebraic parity identities

```text
M_odd  = 2 diag(k) L_h diag(k),
M_even = congruence of L_(x*h(x)).
```

Its generic theorem assumes global operator monotonicity of `h` and then orders
an indefinite even sector below a positive odd sector. The source itself says
the arithmetic function is not even scalar monotone and places the desired
doubly-critical ordering in a conjecture:

```text
https://zenodo.org/records/20737111
RIEMANN_loewner_even_simplicity.tex:88-116
RIEMANN_loewner_even_simplicity.tex:123-147
```

The remaining bordered-resolvent inequality is source lines 152-195. Project
Proof 056 independently certifies the continuous monotonicity failure from the
official cutoff-free closed forms, so a standard Pick/Loewner theorem cannot
be the missing lower producer.

Zenodo 20694588 gives another exact reduction conditional on its stated
pole-free sector structural facts. With

```text
A_even = B_even+2|C><C|,
A_odd  = B_odd-2|S><S|,
```

even-simplicity is equivalent, after pole localization, to

```text
<S,(B_odd-lambda_even)^(-1)S> < 1/2.
```

Primary source:

```text
https://zenodo.org/records/20694588
RIEMANN_herglotz_criterion.tex:233-284
```

Lines 337-356 explicitly leave that uniform inequality open. Yoshida's odd
Weil criterion makes a uniform proof of the corresponding odd-sector sign
RH-level. Moreover, the pole-free Perron theorem alone does not prove the
Morse-index statement used in those structural facts; see Proofs 063-064. Even
granting the premise, the scalar resolvent is a precise coordinate for the
obstruction, not a lower theorem about it.

## 5. Finite Prime-Event Calculus

The current public follow-up to arXiv:2607.02828 is Groskin's
*A matrix-valued von Mangoldt measure in the finite Connes-van Suijlekom path*,
Zenodo concept DOI 21242028. At a prime-power event it proves

```text
Delta Q_N'(log q)
 = -2 Lambda(q)/(sqrt(q) log(q)) * 11^T.
```

The source is public at fixed commit `0675989ea73487773825186b6bcfbd6a4465315c`:

```text
https://github.com/akivag613/connes-cvs-/blob/0675989ea73487773825186b6bcfbd6a4465315c/papers/3_matrix_von_mangoldt_measure/source/main.tex#L58-L90
```

This is an exact arithmetic read-off. It does not preserve positivity along
the cutoff path. Theorem 7.4 assumes the matrix at the event is already
positive definite; it only says that elementary spectral-barrier velocities
decelerate there. Source lines 793-814 contain the assumption and conclusion,
and lines 936-943 explicitly disclaim positivity.

Project Proof 047 checks the missing smooth cells directly: `Q_N''(u)`, inverse
curvature, and log-determinant curvature are indefinite or sign-changing away
from prime events. Positive boundary masses therefore do not define a positive
canonical-system flow.

## 6. New Prolate Interlacing Result

Zenodo 21326823 version 4 was published on 2026-07-12. It proves for every fixed
`tau>0` that the parity determinants of the negative Connes-Moscovici prolate
spectrum have simple, disjoint zeros and satisfy

```text
0 > mu_odd,1 > mu_even,1 > mu_odd,2 > mu_even,2 > ... .
```

Primary source:

```text
https://zenodo.org/records/21326823
simple_zeros_parity_interlacing_v4.tex:109-133
```

The proof is genuine lower spectral theory: after the imaginary-axis
reduction, Neumann and Dirichlet half-line Sturm-Liouville eigenvalues are the
zeros and poles of one Weyl m-function. Its Herglotz derivative is a positive
`integral u^2`, giving strict interlacing; source lines 486-536 contain the
proof.

It is not the parity ordering needed by the Weil form. The paper states this
twice:

```text
simple_zeros_parity_interlacing_v4.tex:160-166
simple_zeros_parity_interlacing_v4.tex:608-618
```

The second passage names the bridge from the exact prolate operator to
`Q_Wlambda` as the open missing step. In particular, its ordering begins with
the odd negative CM mode; it cannot simply be relabeled as the even-simple
bottom of the positive, doubly-critical arithmetic Weil matrix.

## 7. Route Judgment

```text
isolated archimedean total positivity + C-direction prime sign: insufficient
global operator-monotone arithmetic source: false
scalar Herglotz criterion: exact but open / RH-level
prime-event calculus: exact read-off, no positive path
negative CM prolate interlacing: proved, wrong operator without open bridge
new finite-S same-object remainder identity: none
new Lean owner: none
unconditional RH: unproved
```

The most direct surviving target is unchanged: derive the actual finite-S
post-Q identity on the selected test-root Hilbert space, with the already
proved whole-line single crossings carrying coefficient `p^(-m/2)/m`, and
prove a common-domain sign for the remaining words. None of the screened
sources supplies that theorem.
