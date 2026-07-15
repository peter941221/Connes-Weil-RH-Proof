# Proof 272: Concentration-function stopping for the corrected prime sum

Date: 2026-07-15

Status: exact probability-level summation theorem and source-owner guard.
Proof 269's coefficient-weighted chirp square has scale `p^(-m)`, not
`p^(-3m/2)`.  The first mode therefore contains the divergent prime harmonic
sum.  This proof shows that compact-support stopping supplies a sufficient
second factor for the positive square-energy ledger over the ordered future
Euler cloud already present in Proof 271's `A_>p`.  Order the Doob filtration
from large primes to small primes, so
the future average at `p` contains the independent variables at `q<p`.  The
resulting positive square-energy sum is bounded uniformly over every finite prime set, with
polynomial cost in the support width.

Proof 273 shows that a positive norm of the actual
`L_W D^k B A_>p*` row cannot receive this scalar concentration factor.  Gate 3U
requires a same-object disintegration after that row has paired with the right
survivor row and taken its scalar trace.

## 1. Result

```text
+------------------------------------------------+------------------------------+
| layer                                          | judgment                     |
+------------------------------------------------+------------------------------+
| coefficient-weighted chirp square              | p^(-m), exact                |
| first-mode sum over primes                     | divergent                    |
| ordered-future relative Euler law              | exact                        |
| one-prime concentration deficit                | >=p^(-1/2), exact            |
| Kolmogorov-Rogozin concentration bound         | source-backed                |
| positive stopped prime/mode energy              | uniformly bounded            |
| support-width cost                             | polynomial                   |
| positive Proof 271 H1-row stopping             | rejected by Proof 273      |
| signed scalar local coefficient                | p^(-m/2), Proof 274          |
| complete signed extra half-power               | open, Proof 274 (AK.12)      |
| finite-S sign and RH                           | unproved                     |
+------------------------------------------------+------------------------------+
```

The corrected flow is

```text
Proof 228 weighted chirp
  -> square p^(-m)
  -> relative-displacement support event
  -> concentration function of the remaining Euler cloud
  -> uniformly summable positive stopped energy
  -> signed coefficient and extra-half-power theorem still required.      (AI.1)
```

## 2. Relative Euler displacement and concentration function

For each prime `q`, set

```text
a_q=q^(-1/2),

P(N_q=n)=(1-a_q)a_q^n,  n>=0.                         (AI.2)
```

Proof 254 equations `(M.3)--(M.5)` give this one-sided Markov law and its
two-leg relative displacement for the normalized inverse Euler transport.

Let `N_q'` be an independent copy and define the symmetric logarithmic jump

```text
Z_q=(N_q-N_q')log(q).                                  (AI.3)
```

Fix one Doob filtration by ordering `S` from large primes to small primes.  At
the channel for `p`, Proof 271's future factor `A_>p` then contains the primes
`q<p`.  Define its two-leg relative history by

```text
Y_(S,<p)=sum_(q in S, q<p) Z_q,
mu_(S,<p)=Law(Y_(S,<p)).                               (AI.4)
```

The square-function energy has two Stinespring probability legs, which is why
the relative law uses `N_q-N_q'` although `A_>p` itself is one-sided.

For a probability law `mu` on the real line, use the Levy concentration
function

```text
Q_h(mu)=sup_(x in R) mu((x,x+h]),  h>0.                (AI.5)
```

If the compact pre-root lies in `[-B_root,B_root]`, its cross-correlation lies
in `[-2B_root,2B_root]`.  Every translated support event therefore fits inside
an interval of length

```text
h_B=max(1,4B_root).                                    (AI.6)
```

The support statement is Proof 263 equation `(Z.8)`.

The supremum in `(AI.5)` absorbs the prime-mode shift `m log(p)` and any fixed
boundary offset.

## 3. Exact one-prime concentration deficit

The difference of two geometric variables has the exact law

```text
P(N_q-N_q'=k)
 =(1-a_q)/(1+a_q) a_q^|k|,  k in Z.                   (AI.7)
```

This is also Proof 254 equation `(M.6)`.

The largest atom is at zero.  If `log(q)>h`, every interval of length `h`
contains at most one point of the lattice `log(q) Z`.  Hence

```text
Q_h(Law(Z_q))=(1-a_q)/(1+a_q),

1-Q_h(Law(Z_q))
 =2a_q/(1+a_q)
 >=a_q=q^(-1/2).                                      (AI.8)
```

The Kolmogorov-Rogozin inequality states that independent real random
variables satisfy

```text
Q_h(Law(sum_i X_i))
 <=C_KR [sum_i (1-Q_h(Law(X_i)))]^(-1/2).             (AI.9)
```

Apply `(AI.9)` to the jumps in `(AI.4)` whose lattice spacing exceeds `h_B`.
Convolution with the omitted small-spacing jumps cannot increase a
concentration function.  Equations `(AI.8)` and `(AI.9)` give

```text
Q_(h_B)(mu_(S,<p))
 <=min(1,
   C_KR [sum_(q in S, q<p, log(q)>h_B)q^(-1/2)]^(-1/2)).        (AI.10)
```

The empty sum receives the bound `1`.

## 4. Reduce all modes to the first-mode profile

For a fixed nonnegative integer `d`, define the corrected local energy

```text
E_d(p)=sum_(m>=1)(1+m log(p))^(2d)p^(-m).              (AI.11)
```

Since

```text
1+m log(p)<=m(1+log(p)),

sum_(m>=1)m^(2d)p^(-m)<=C_d/p                         (AI.12)
```

for every `p>=2`, one has

```text
E_d(p)<=C_d (1+log(p))^(2d)/p.                        (AI.13)
```

The factor on the right is the only prime profile needed below.  No geometric
event probability has been multiplied into `(AI.11)`.

## 5. Uniform stopped summation

The positive square-energy stopped ledger is

```text
mathcalE_d(S,B_root)
 =sum_(p in S) E_d(p) Q_(h_B)(mu_(S,<p)).              (AI.14)
```

Split `S` at `log(p)=h_B`.  The small-prime part obeys

```text
sum_(p in S, log(p)<=h_B) E_d(p)
 <=C_d sum_(2<=n<=exp(h_B))(1+log(n))^(2d)/n
 <=C_d'(1+h_B)^(2d+1).                                (AI.15)
```

List the large-prime set as

```text
r_1<r_2<...<r_n.                                       (AI.16)
```

Pay the `r_1` contribution directly.  For `j>=2`, the anti-concentration mass
available from the smaller large primes is

```text
sum_(i<j)r_i^(-1/2)
 >=(j-1)r_j^(-1/2).                                   (AI.17)
```

Equations `(AI.10)`, `(AI.13)`, and `(AI.17)` give

```text
E_d(r_j)Q_(h_B)(mu_(S,<r_j))
 <=C_d (1+log(r_j))^(2d)
   /[r_j^(3/4)sqrt(j-1)].                              (AI.18)
```

The `r_j` are distinct integers, so `r_j>=j+1`.  The decreasing envelope of
`(1+log(x))^(2d)x^(-3/4)` turns `(AI.18)` into a constant multiple of

```text
(1+log(j))^(2d)j^(-5/4),
```

which is summable.  Combining this rank sum with `(AI.15)` proves

```text
sup_(finite S) mathcalE_d(S,B_root)
 <=C_d''(1+B_root)^(2d+1).                            (AI.19)
```

This argument uses no prime number theorem.  It works for sparse and dense
finite prime sets and uses one fixed decreasing-prime filtration.  It does not
replace the orthogonal Doob rows by overlapping leave-one-prime decompositions.

## 6. Withdrawn positive source contract

Proof 272 originally proposed

```text
sum_k norm_root(
  stopped[L_W D^k I_(rand,p,m)*])^2

 <=C (1+m log(p))^(2d)p^(-m)
   Q_(h_B)(mu_(S,<p)).                                 (AI.20)
```

The notation `stopped[...]` tried to apply compact cross-correlation support to
the positive norm of the left row.

Proof 273 rejects `(AI.20)`.  A compact-root crossing can have zero scalar
trace outside the support window while its trace norm stays positive.  A
one-element noncommutative `H1` column norm equals that trace norm.  Compact
support therefore acts after the left/right product and scalar trace, not on
the left row alone.

The intervening factor

```text
D^k B A_>p*                                             (AI.21)
```

contains the classical future average `A_>p*` in the chosen ordering, but
`D^k` must stay inside Proof 273's signed scalar pairing.  Proof 272's valid
output is the positive square-energy probability lemma `(AI.19)`.  Proof 274
shows that the actual signed scalar coefficient is only `p^(-m/2)` before the
complete physical cancellation.  Thus `(AI.19)` applies to the scalar route
only after the extra-half-power contract `(AK.12)` has been proved.

## 7. Literature boundary

The concentration-function input is:

```text
Tomas Juskevicius,
The sharp form of the Kolmogorov--Rogozin inequality and a conjecture of
Leader--Radcliffe,
arXiv:2201.09861, 2022.
https://arxiv.org/abs/2201.09861
```

The paper defines `Q_h` as in `(AI.5)` and states `(AI.9)` for sums of
independent real random variables.  Equations `(AI.2)--(AI.8)` and the uniform
summation `(AI.11)--(AI.19)` are project derivations.

The cited theorem applies to the ordered future cloud `(AI.4)`.  It does not
construct Proof 273's paired scalar disintegration.

## 8. Reproduction

Run in WSL2 from the Windows source snapshot:

```text
python3 -B docs/proofs/272_concentration_stopped_prime_sum_probe.py

python3 -B docs/proofs/272_concentration_stopped_prime_sum_probe.py \
  --maximum-prime 1000000 --root-width 2 --polynomial-degree 2
```

The certificate checks the difference-geometric atom formula, the mode
reduction, and the finite-prime stopped ledger based on the right side of
`(AI.10)`.  The numerical concentration column omits the unknown universal
constant `C_KR`; it tests scaling and coefficient ownership, not the paired
source estimate in Proof 273.

## 9. Route judgment

Proof 272 repairs the positive square-energy summation after the Proof 269
double count.  The compact-support concentration function turns the harmonic
chirp square into a uniform probability-level sum with polynomial support
cost.

Proof 273 withdraws `(AI.20)` and retains `(AI.19)`.  The active Gate 3U bottom
is Proof 274 `(AK.12)`: construct the signed scalar disintegration for Proof
271's complete paired renewal and earn the missing extra `p^(-m/2)`, or prove
a sharper location-aware stopping estimate for the exact scalar ledger.  The
finite-S sign, arithmetic same-object trace identity, negative-owner
integration, Burnol's identity, and RH remain open.  No Lean owner or route
rewire is authorized.
