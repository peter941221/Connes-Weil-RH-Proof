# Plan 018 Gate D1 Mathematical Verdict

Date: 2026-07-11

Verdict: **D1 does not pass.** There is an exact unconditional defect formula
as one absolutely convergent real integral, and every finite symmetric zero
truncation has an exact Gram/conjugation decomposition. The available source
does not justify the absolutely convergent zero-pair expansion required by D1.
Moreover, the finite Gram correction is a quadratic form for `K_R - I`, not
for the positive Gram matrix `K_R`; it therefore has no inherited sign.

This rejects the proposed D1-to-D2 sign route. It does not prove that no other
future representation of the same defect can exist.

## 1. Source Objects

Suzuki defines

```text
E(z)     = xi(1/2 - i z) + xi'(1/2 - i z),
Theta(z) = E#(z) / E(z),
A(z)     = (E(z) + E#(z))/2 = xi(1/2 - i z).
```

The Hermite--Biehler and inner-function properties are stated only under RH.
See Suzuki, *On the Hilbert space derived from the Weil distribution*,
arXiv:2301.00421v3, source lines 194-212 and 741-767:

https://arxiv.org/abs/2301.00421

On the real axis, however,

```text
E(x) = A(x) + i A'(x),
|Theta(x)| = 1,
w(x) := |(1 + Theta#(x))/2|^2
      = A(x)^2 / (A(x)^2 + A'(x)^2).
```

This is unconditional; Suzuki explicitly records the cancellation at real
zeros and `|Theta(x)|=1` at source lines 985-1014.

Let

```text
q_gamma(t) := (exp(-i gamma t) - 1) / gamma,
P_t(x)     := sum_gamma m_gamma q_gamma(t)/(x-gamma).
```

Suzuki proves local absolute and compact-uniform convergence of `P_t` away
from its poles (lines 769-787), the explicit arithmetic identity
`mathfrak P_t=P_t` (lines 789-983), and

```text
S_t(x) = i(1 + Theta#(x))/2 * P_t(x) in L2(R).
```

The unconditional `L2` estimate is at lines 985-1014. Therefore the following
formula is exact and its integral is absolutely convergent:

```text
Delta(t)
  = 1/(2*pi) * integral_R w(x) |P_t(x)|^2 dx + g(t).       (D1.1)
```

This is the strongest unconditional defect formula supplied directly by the
source.

## 2. Finite Symmetric Gram Formula

Let `Gamma_R` be any finite multiset closed under

```text
gamma -> -gamma, gamma -> conjugate(gamma).
```

Put

```text
F_gamma(z)
  := sqrt(m_gamma/pi) * i(1+Theta(z))/(2(z-gamma)),

K_(gamma,rho)
  := <F_gamma#, F_rho#>_L2
   = sqrt(m_gamma*m_rho)/pi
     * integral_R w(x)/((x-conjugate(gamma))*(x-rho)) dx.
```

The last identity follows directly from the definition at source lines
1021-1034 and the real-axis formula for `w`. The finite partial sum

```text
S_(t,R) = sum_(gamma in Gamma_R)
            sqrt(pi*m_gamma) q_gamma(t) F_gamma#
```

therefore satisfies, with no interchange of infinite sums,

```text
||S_(t,R)||_2^2/pi
  = sum_(gamma,rho in Gamma_R)
      sqrt(m_gamma*m_rho)
      q_gamma(t) conjugate(q_rho(t)) K_(gamma,rho).        (D1.2)
```

Define the finite Weil zero sum

```text
W_R(t)
  := sum_(gamma in Gamma_R) m_gamma
       (exp(i gamma t)-1)(exp(-i gamma t)-1)/gamma^2.
```

Suzuki's full version is `G_g(t,t)=-2g(t)`; see lines 1213-1228 and
1250-1267. Define the finite comparison defect by

```text
Delta_R(t) := ||S_(t,R)||_2^2/(2*pi) - W_R(t)/2.
```

This is a truncation device, not an assertion that `W_R=-2g` at finite `R`.
Adding and subtracting the Hermitian diagonal gives the exact split

```text
Delta_R(t)
  = 1/2 * [
      sum_(gamma,rho) sqrt(m_gamma*m_rho)
        q_gamma conjugate(q_rho) K_(gamma,rho)
      - sum_gamma m_gamma |q_gamma|^2
    ]
  + 1/2 * [
      sum_gamma m_gamma |q_gamma|^2 - W_R(t)
    ].                                                       (D1.3)

                 +-----------------------+
                 | finite norm defect    |
                 +-----------+-----------+
                             |
              +--------------+--------------+
              |                             |
    +---------v----------+       +----------v-----------+
    | Gram defect        |       | conjugation defect   |
    | quadratic form of  |       | |q_gamma|^2 differs  |
    | K_R - I            |       | from the Weil factor |
    +--------------------+       +----------------------+
```

The second term vanishes when every zero ordinate `gamma` is real. Off the
critical line it must be retained: complex conjugation of `q_gamma` is not the
factor `(exp(i gamma t)-1)/gamma` appearing in the Weil sum.

## 3. Why Absolute Zero-Pair Convergence Is Not Established

The paper proves two different convergence facts:

```text
P_t zero series:
  absolute and compact-uniform away from Gamma;

S_t:
  the completed function is in L2(R).
```

Neither statement implies

```text
sum_(gamma,rho)
  |sqrt(m_gamma*m_rho) q_gamma conjugate(q_rho) K_(gamma,rho)|
  < infinity.                                                (D1.4)
```

The coefficient-square estimate at lines 1197-1207 is used only after RH,
when Proposition 4.1 supplies an orthonormal basis (lines 1111-1138). Without
RH there is no Bessel bound or unconditional synthesis-operator bound for the
family `F_gamma#`. Thus local convergence of `P_t` cannot be integrated
term-by-term twice over the whole real axis.

Consequently, (D1.2)-(D1.3) are rigorous for finite symmetric truncations, but
the source does not prove that they converge to (D1.1), much less converge
absolutely as a zero-pair series. Claiming that limit would insert precisely
the missing global Gram control.

## 4. Sign Verdict

`K_R` is positive semidefinite because it is a Gram matrix. The defect uses
`K_R-I`. Positivity of `K_R` says only that its eigenvalues are nonnegative; it
does not say whether they lie above or below `1`.

Already for two normalized nonorthogonal vectors,

```text
K = [ 1       c ]
    [ conj(c) 1 ],

K-I has eigenvalues +|c| and -|c|.
```

Therefore Gram positivity by itself supplies no sign for the first bracket of
(D1.3). This is a failure of the proposed inference, not a numerical claim
that a particular zeta Gram block has already been proved to realize both
signs.
The second bracket is a separate off-critical conjugation correction, so it
cannot repair that inference by being omitted or folded into the diagonal.

Suzuki's paper is consistent with this obstruction: orthonormality is proved
only assuming RH (lines 1111-1138), and an off-critical zero produces a
negative Weil direction by Yoshida separation (lines 1303-1337). The positive
`L2` norm and the indefinite Weil form are different quadratic geometries;
their difference is not controlled by a soft positivity argument.

## 5. Gate Decision

```text
+--------------------------------------+------------------------------+
| D1 requirement                       | result                       |
+--------------------------------------+------------------------------+
| unconditional exact defect identity | yes: integral formula (D1.1) |
| quadruple-preserving finite formula | yes: (D1.2)-(D1.3)           |
| absolutely convergent zero-pair sum | not established              |
| explicit summable pair majorant     | absent                       |
| inherited fixed sign               | no: defect uses K_R-I         |
+--------------------------------------+------------------------------+
```

Final decision:

```text
D1 status: rejected under its stated pass criterion.
D2 status: inactive for this representation.
Plan 018 status: rejected as a guaranteed RH route in its current form.
RH status: still conditional; no project root was removed or lowered.
```

No Lean API should be created from this formula. A future reopening requires a
new unconditional theorem giving a global synthesis bound plus a genuinely
coercive identity for the full defect; finite Gram positivity alone is
insufficient.
