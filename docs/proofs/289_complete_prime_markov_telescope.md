# Proof 289: Complete-prime Markov telescope

Date: 2026-07-15

Status: exact signed summation correction after Proof 288.  The same completed
renewal reward occurs in every Doob prime channel.  Its predictable-future
Markov factors therefore telescope across all visible primes before any
absolute value is taken.

The prime sum is one global contraction defect

```text
I-G_S,  G_S=product_(p in S) A_p A_p*.
```

Thus a separate `O(p^(-1))` estimate for every prime is a sufficient but
unnecessary route.  Proof 274's extra-half-power target is no longer the
active summation gate.  The remaining theorem is a uniform estimate for the
complete global defect together with the base renewal level and the outer
missing channel.  This proof does not establish that estimate, Gate 3U, the
finite-`S` sign, the arithmetic same-object identity, Burnol's identity, or
RH.

## 1. Result

```text
+------------------------------------------------+------------------------------+
| layer                                          | judgment                     |
+------------------------------------------------+------------------------------+
| one-prime relative Markov operator             | exact                        |
| local defect resolvent factorization           | exact                        |
| predictable-future prime factors               | retained                     |
| sum over all Doob prime channels               | exact telescope              |
| complete prime defect                          | I-product_p G_p              |
| complete prime defect order                    | between 0 and I              |
| per-prime absolute values                      | forbidden / unnecessary      |
| per-prime extra half-power                     | sufficient, not active       |
| global renewal-boundary estimate               | open                         |
| Gate 3U and RH                                 | open / unproved              |
+------------------------------------------------+------------------------------+
```

The ownership change is

```text
relative modes within p
  -> one local defect I-G_p, Proof 288
  -> retain the future product G_fut(p)
  -> sum every p with signs intact
  -> I-product_p G_p
  -> estimate one global boundary renewal.             (AZ.1)
```

## 2. Exact local factorization

For one prime put

```text
a=a_p=p^(-1/2),
L=log(p),
U=U_L,
R_a=(I-aU)^(-1),
A_p=(1-a)R_a,
G_p=A_p A_p*.                                         (AZ.2)
```

Because `U` is unitary and `0<a<1`, all inverses in `(AZ.2)` exist in
operator norm.  Direct multiplication gives

```text
(I-aU)(I-G_p)(I-aU*)

 =(I-aU)(I-aU*)-(1-a)^2 I

 =a(2I-U-U*)
 =a(I-U)(I-U*).                                      (AZ.3)
```

Hence

```text
I-G_p
 =a R_a(I-U)(I-U*)R_a*.                              (AZ.4)
```

This displays the route-owned half-power and two discrete translation
differences without expanding relative modes.  Spectral calculus also gives

```text
0<=G_p<=I,

norm(I-G_p)=4a/(1+a)^2.                              (AZ.5)
```

Equation `(AZ.4)` is useful algebra, but applying a norm to its factors would
return Proof 288's single half-power.  It is not the uniform estimate.

## 3. Predictable future is the telescope factor

Use Proof 271's decreasing-prime Doob order.  At the channel for `p`, the
factor called `A_>p` in Proof 286 contains the primes occurring later in that
order, numerically the visible primes `q<p`.  Write

```text
A_fut(p)=product_(q later than p) A_q,

G_fut(p)=A_fut(p)A_fut(p)*
        =product_(q later than p)G_q.                 (AZ.6)
```

All `A_q` are functions of the same translation group, so they are normal
and commute with one another and their adjoints.

Let `X in S1` be any common completed reward and put

```text
Y_p=A_fut(p) X A_fut(p)*.                             (AZ.7)
```

For the one-prime random unitary `V_p`, `E[V_p]=A_p`.  Expanding the centered
covariance and using ordinary trace cyclicity gives

```text
E Tr((V_p-A_p)Y_p(V_p-A_p)*)

 =Tr(Y_p)-Tr(A_pY_pA_p*)

 =Tr(G_fut(p)(I-G_p)X).                              (AZ.8)
```

This is Proof 286's prime scalar after the common past has disappeared.  The
future factor is not deleted: it is exactly the prefix needed by the
telescope.

## 4. Complete-prime telescope

List the primes in the Doob order as `p_1,...,p_n`, and define the product of
the factors later than `p_j` by

```text
H_j=product_(i>j)G_(p_i),
H_n=I.                                                (AZ.9)
```

Commutativity gives the elementary difference

```text
H_j(I-G_(p_j))
 =H_j-product_(i>=j)G_(p_i).                         (AZ.10)
```

The right side telescopes.  Therefore

```text
sum_(p in S)G_fut(p)(I-G_p)
 =I-product_(p in S)G_p
 =I-G_S.                                             (AZ.11)
```

The same identity in Proof 287's coefficient notation is

```text
sum_(p in S)
  P_fut(p)(I-P_p)kappa

 =(I-product_(p in S)P_p)kappa.                      (AZ.12)
```

Thus both sums must be completed before an absolute value:

```text
relative modes first telescope inside each p;

prime channels then telescope across S.              (AZ.13)
```

No prime number theorem, concentration inequality, or source tail estimate is
used in `(AZ.11)--(AZ.12)`.

## 5. Readback on the Proof 286 reward

For `k>=1`, Proof 286 uses the same reward for every prime:

```text
H_(S,k)(W)
 =iota_B* W R A*K Delta^(k-1)
  -iota_B*A*C W K Delta^(k-1).                       (AZ.14)
```

Proof 288 embeds it as the trace-class operator

```text
X_(S,k)(W)=iota_B H_(S,k)(W)iota_B*.                 (AZ.15)
```

The subscript `p` introduced temporarily in Proof 287 labels the channel, not
a different reward.  Combining `(AZ.8)`, `(AZ.11)`, and `(AZ.15)` proves

```text
sum_(p in S)Xi_(S,k,p)(W)
 =Tr((I-G_S)X_(S,k)(W)).                             (AZ.16)
```

More generally, for every displacement `z`,

```text
sum_(p in S)
 Tr(U_z G_fut(p)(I-G_p)X_(S,k)(W))

 =Tr(U_z(I-G_S)X_(S,k)(W)).                          (AZ.17)
```

All traces in `(AZ.16)--(AZ.17)` are ordinary fixed-`S` traces by Proof 288.
This does not legalize the unrelated raw endpoint coefficient prohibited by
Proof 263.

Equation `(AZ.16)` is also the scalar form of Proof 271's already exact Gram
identity

```text
sum_p M_p* M_p=M_rand* M_rand.                       (AZ.18)
```

Proof 289 adds the missing Markov-coordinate readback: the orthogonal Doob
sum is exactly one global relative-translation defect after support has acted.

## 6. Corrected complete response

Retain Proof 286's base and outer-missing terms:

```text
Xi_(S,0)(W)=Lambda_W(Z_(S,0)),

Xi_(S,k,C)(W)=Tr(M_C H_(S,k)(W)M_C*).                (AZ.19)
```

Then its full support-first expansion becomes

```text
Q_S(eta,xi)
 =Xi_(S,0)(W)

  +sum_(k>=1)[
     Xi_(S,k,C)(W)
     +Tr((I-G_S)X_(S,k)(W))
   ].                                                 (AZ.20)
```

Equation `(AZ.20)` is the new analytic owner.  It retains:

```text
the complete outer-minus-Sonin reward inside X_(S,k);

the complete visible Euler law inside G_S;

the outer escape M_C;

the base renewal level;

the signed sum over every renewal level.              (AZ.21)
```

## 7. Why the extra-half-power target is no longer active

Proof 274 proposed the sufficient primewise envelope

```text
|Phi_(S,p,m)|<=C poly(m log p)p^(-m).                 (AZ.22)
```

It was intended to make a sum of primewise absolute values converge.  But the
route forbids those absolute values, and `(AZ.11)` evaluates the signed prime
sum exactly.  Consequently:

```text
(AZ.22) remains a valid sufficient theorem;

(AZ.22) is not necessary for the signed route;

failure to prove (AZ.22) is not the current Gate 3U bottom.              (AZ.23)
```

This does not claim `(AZ.22)` is false.  It removes an avoidable burden from
the main path.

The finite guard constructs one common reward for which prime-channel scalar
terms cancel strongly.  Taking their absolute values costs more than the
completed telescope.  If a different reward is substituted in each prime
channel, the telescope fails.  Thus the common-reward fact in `(AZ.14)` is
structural, not cosmetic.

## 8. What remains hard

Since the `G_p` are commuting positive contractions,

```text
0<=G_S<=I,
0<=I-G_S<=I.                                         (AZ.24)
```

This removes the prime harmonic ledger and introduces no Euler condition
number.  It does not justify

```text
|Tr((I-G_S)X_(S,k))|<=norm(X_(S,k))_1                (AZ.25)
```

as a uniform estimate.  Proof 288 shows that this trace norm depends on `S`,
grows under direct sums, and separates the signed physical branches.

The active theorem is now the single global estimate

```text
|Xi_(S,0)(W)
 +sum_(k>=1)[
    Xi_(S,k,C)(W)
    +Tr((I-G_S)X_(S,k)(W))
  ]|

 <=C(1+B_root)^d
   norm(eta)_(H^r)norm(xi)_(H^r),                    (AZ.26)
```

with constants independent of finite `S`.  A source proof of `(AZ.26)` must
apply compact cross-correlation support to the whole bracket in `(AZ.20)`,
retain the Burnol outer/Sonin boundary difference, and use the killed renewal
as one conservative path law.  It must not reopen the prime or relative-mode
absolute sums.

There is one further circularity guard.  Proof 271 gives

```text
M_rand* M_rand+M_C* M_C=Delta.                       (AZ.26a)
```

Since `H_(S,k)=H_(S,1)Delta^(k-1)`, immediately recombining the two missing
channels yields

```text
Tr((I-G_S)X_(S,k))+Xi_(S,k,C)
 =Tr(H_(S,1)Delta^k).                                (AZ.26b)
```

Adding the base level and summing `k` then gives

```text
sum_(k>=0)Tr(H_(S,1)Delta^k)
 =Tr(H_(S,1)Gamma^(-1)).                             (AZ.26c)
```

This is the original conditioned renewal, not an estimate.  Therefore the
next proof must not merge the global random defect and outer escape back into
`Delta` before using their distinct physical boundary meanings.

A concrete successor contract is a root-completed trace coboundary

```text
H_(S,1)=V_S(I-Delta)+Rem_S                            (AZ.26d)
```

or its scalar-kernel analogue, where `V_S` is constructed from the fixed
outer/Sonin boundary and compact support without using `Gamma^(-1)`.  The
`V_S(I-Delta)` part telescopes across renewal levels.  The remainder must have
a uniformly summable stopped path bound.  Taking
`V_S=H_(S,1)Gamma^(-1)` is tautological and forbidden.

## 9. Finite certificate

The companion certificate uses one common spectral translation group.  It
checks independently:

```text
local resolvent factorization (AZ.4);
local defect positivity (AZ.5);
centered covariance readback (AZ.8);
operator telescope (AZ.11);
scalar and displaced trace telescopes (AZ.16)--(AZ.17);
global defect positivity (AZ.24).                    (AZ.27)
```

It also reports a primewise absolute-value cancellation ratio and a
non-common-reward gap.  Those two values are ownership guards, not continuous
lower bounds.

The default cohort reports

```text
maximum exact error                         4.98e-16,
primewise absolute-value cancellation      35.3468x,
non-common-reward telescope gap             2.03e-1,
global defect operator norm                 0.999994.       (AZ.27a)
```

The alternate cohort reports

```text
maximum exact error                         6.07e-16,
primewise absolute-value cancellation      47.6414x,
non-common-reward telescope gap             3.44e-1,
global defect operator norm                 0.999998.       (AZ.27b)
```

Run in WSL2:

```text
OPENBLAS_NUM_THREADS=1 python3 -B \
  docs/proofs/289_complete_prime_markov_telescope_probe.py

OPENBLAS_NUM_THREADS=1 python3 -B \
  docs/proofs/289_complete_prime_markov_telescope_probe.py \
  --primes 2,3,5,7,11,13,17,19,23,29,31 \
  --spectral-size 72 --seed 2289
```

Both runs report

```text
complete_prime_markov_telescope=EXACT,
predictable_future_factors=RETAINED,
common_completed_reward=MANDATORY,
primewise_extra_half_power_required=FALSE_FOR_SIGNED_SUM,
trace_norm_used_for_uniform_gate=FALSE,
global_renewal_boundary_bound=OPEN,
gate_3u=OPEN,
RH=UNPROVED.
```

## 10. Evidence and route judgment

Project evidence:

```text
Proof 271, orthogonal Doob prime Gram decomposition:
docs/proofs/271_first_missing_prime_row.md

Proof 286, common reward and mandatory future average:
docs/proofs/286_first_missing_relative_mode.md

Proof 288, fixed-S trace domain and local Markov operator:
docs/proofs/288_completed_markov_trace_domain.md
```

Primary source boundary for the still-open Sonin estimate:

```text
Connes--Consani, Weil positivity and Trace formula,
the archimedean place, arXiv:2006.13771.
https://arxiv.org/abs/2006.13771
```

Proof 289 removes a false necessity, not a mathematical difficulty.  The next
attack is

```text
global owner (AZ.20)
  -> combine base, random defect, and outer escape before a norm
  -> read one killed real-line renewal kernel
  -> apply compact support to the complete outer-minus-Sonin boundary
  -> use G_S only as one probability contraction
  -> prove (AZ.26)
  -> Gate 3U.                                             (AZ.28)
```

The uniform global renewal-boundary estimate, finite-`S` sign, arithmetic
same-object trace identity, negative-owner integration, Burnol's all-zero
identity, and RH remain open.  No Lean owner or route consumer is changed.

Successor correction: Proof 290 replaces the provisional right-multiplication
coboundary `(AZ.26d)` by an exact ordered finite-horizon construction.  With

```text
R_n x=(Kx,K Delta x,...,K Delta^n x,Delta^(n+1)x),
L_n x=(Kx,Kx,...,Kx,x),
```

one has `L_n*R_n=I`, `1/2 I<=R_n*R_n<=I`, and

```text
sum_(k=0)^n N_W Delta^k
 =L_n*diag(W,...,W,W_B)R_n-W_B.
```

The active successor is Proof 290 `(BA.23)--(BA.29)`: apply compact support to
the complete intertwinement/path-projection defect before the horizon limit.
