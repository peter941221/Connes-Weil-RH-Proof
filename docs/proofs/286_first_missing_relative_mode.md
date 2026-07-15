# Proof 286: First-missing relative-mode scalar

Date: 2026-07-15

Status: exact fixed-`S` continuation of Proof 285.  Every nonzero
support-first renewal term factors through the actual random and outer missing
channels from Proof 271.  In a Doob prime channel, the complete scalar trace
deletes the common unitary past exactly.  The centered local geometric
innovation then becomes a signed sum of relative-translation second
differences.

The predictable future average remains inside every term.  The real-line
kernel readback, the extra-half-power estimate, Gate 3U, the finite-`S` sign,
the arithmetic same-object trace identity, Burnol's identity, and RH remain
open.

## 1. Result

```text
+------------------------------------------------+------------------------------+
| layer                                          | judgment                     |
+------------------------------------------------+------------------------------+
| support-first two-boundary renewal             | exact, Proof 285             |
| Delta=random missing + outer missing           | exact, Proof 271             |
| every nonzero renewal level through M_a        | exact                        |
| Doob common past V_<p                          | eliminated in scalar trace   |
| predictable future A_>p                        | retained / mandatory         |
| centered local innovation                      | relative-mode second diff    |
| relative geometric coefficient                | one copy of a_p^|r|          |
| relative-mode termwise absolute value          | rejected by finite guard     |
| real-line extra half-power                     | open                         |
| Gate 3U and RH                                 | open / unproved              |
+------------------------------------------------+------------------------------+
```

The new control flow is

```text
support-clipped Z_(S,k)
  -> actual missing channel M_a
  -> prime Doob channel
  -> delete common past V_<p inside the trace
  -> retain future average A_>p
  -> relative mode r=N_p-N_p'
  -> signed two-boundary second difference
  -> source half-power estimate.                           (AW.1)
```

## 2. Missing-channel factorization after support

Retain Proof 285's notation

```text
K=E A iota_B,
Gamma=K* K,
Delta=I_(H_B)-Gamma.                                 (AW.2)
```

The actual missing maps from Proof 271 are

```text
M_rand=I_rand,
M_C=I_C=C A iota_B,                                  (AW.3)
```

with output spaces allowed to differ, and

```text
M_rand* M_rand+M_C* M_C=Delta.                       (AW.4)
```

The random channel has the orthogonal Doob refinement

```text
M_rand* M_rand=sum_(p in S)M_p* M_p.                 (AW.5)
```

For `k>=1`, define the complete two-boundary reward on `H_B` by

```text
H_(S,k)(W)
 :=iota_B* W R A* K Delta^(k-1)
   -iota_B* A* C W K Delta^(k-1).                    (AW.6)
```

No absolute value separates the two terms in `(AW.6)`.  Rectangular trace
cyclicity on the completed fixed-`S` products gives

```text
Lambda_W(Z_(S,k))
 =Tr_(H_B)(H_(S,k)(W) Delta)

 =Tr(M_C H_(S,k)(W) M_C*)
  +sum_(p in S)Tr(M_p H_(S,k)(W) M_p*).              (AW.7)
```

Equation `(AW.7)` is the first-missing scalar factorization.  Compact support
has already acted on Proof 285's two-boundary functional before `(AW.4)` is
inserted.

The base level has no preceding missing event:

```text
Xi_(S,0)(W)=Lambda_W(Z_(S,0)).                       (AW.8)
```

Thus

```text
Q_S(eta,xi)
 =Xi_(S,0)(W)
  +sum_(k>=1)[Xi_(S,k,C)(W)+sum_p Xi_(S,k,p)(W)],    (AW.9)

Xi_(S,k,a)(W)=Tr(M_a H_(S,k)(W) M_a*).
```

This is equivalent to Proof 271's first-missing row, but its order is now
support first and scalar first.  No positive row norm has been introduced.

## 3. Exact Doob prime channel

Fix the prime order used by Proofs 271--272.  Let

```text
V_p(omega_p)=U_(N_p(omega_p) log(p)),
A_p=E[V_p],

V_<p=product_(q before p)V_q,
A_>p=product_(q after p)A_q.                         (AW.10)
```

Proof 271's Doob difference is

```text
M_p(omega)
 =V_<p(omega_<p)(V_p(omega_p)-A_p)A_>p iota_B.       (AW.11)
```

Put

```text
Y_(S,k,p)(W)
 :=A_>p iota_B H_(S,k)(W)iota_B* A_>p*.              (AW.12)
```

Substitution of `(AW.11)` into `(AW.7)` gives a probability-space trace with
`V_<p` on the far left and `V_<p*` on the far right.  Each `V_<p` is unitary,
so completed trace cyclicity gives

```text
Xi_(S,k,p)(W)
 =E Tr((V_p-A_p)Y_(S,k,p)(W)(V_p-A_p)*).             (AW.13)
```

The entire common past has disappeared.  No commutation of `V_<p` with the
Sonin or outer boundary is needed; the two copies form one unitary
conjugation of the already completed scalar.

The future factor `A_>p` has not disappeared.  It remains on both sides of
`H_(S,k)(W)` in `(AW.12)` and carries the ordered-future displacement law used
by Proof 272.

## 4. Centered innovation as a second difference

Let

```text
a_p=p^(-1/2),
nu_p(m)=(1-a_p)a_p^m,  m>=0,
V_p(m)=U_(m log(p)).                                  (AW.14)
```

For an independent copy `N_p'`, elementary centering gives

```text
E Tr((V_p-A_p)Y(V_p-A_p)*)

 =1/2 E Tr((V_p(N_p)-V_p(N_p'))
             Y
            (V_p(N_p)-V_p(N_p'))*).                 (AW.15)
```

Set `r=N_p-N_p'`.  The translation group law gives

```text
U_(N_p log p)-U_(N_p' log p)
 =U_(N_p' log p)(U_(r log p)-I).                     (AW.16)
```

The common absolute local history `U_(N_p' log p)` is again a unitary
conjugation and disappears in the scalar trace.  The exact difference law is

```text
d_p(r)=P(N_p-N_p'=r)
      =(1-a_p)/(1+a_p) a_p^|r|,  r in Z.             (AW.17)
```

Combining `(AW.13)--(AW.17)` proves

```text
Xi_(S,k,p)(W)
 =1/2 sum_(r in Z)d_p(r) Psi_(S,k,p,r)(W),            (AW.18)

Psi_(S,k,p,r)(W)
 :=Tr((U_(r log p)-I)
        Y_(S,k,p)(W)
       (U_(r log p)-I)*).
```

The `r=0` term vanishes exactly.  For `r!=0`, `(AW.17)` carries one and only
one Euler coefficient:

```text
d_p(r) asymp p^(-|r|/2).                             (AW.19)
```

This is the route-owned signed coefficient from Proof 274.  The second copy
needed for summability must come from the real-line scalar
`Psi_(S,k,p,r)`, not from squaring `(AW.19)` by hand.

## 5. What compact support now has to prove

The detector inside `H_(S,k)(W)` is convolution by

```text
F_(eta,xi)=xi^star*eta,
supp(F_(eta,xi)) subset [-2B_root,2B_root].           (AW.20)
```

Expand the two copies of `A_>p` in `(AW.12)` only after this support has been
inserted.  If their relative future displacement is `z`, Proof 287 shows that
the completed local second difference has three outer support windows:

```text
|z|<=2B_root
  or |z+r log(p)|<=2B_root
  or |z-r log(p)|<=2B_root.                          (AW.21)
```

The complete Sonin channel is not compactly supported.  It retains the
half-power tail isolated by Proofs 275--277.  Therefore `(AW.21)` applies only
to the outer component after the outer/Sonin owner has been identified; the
two components must recombine before the final absolute value.

Proof 287 also rejects a `p^(-|r|/2)` estimate on each individual
`Psi_(S,k,p,r)`.  The correct target first sums all relative modes into the
local Markov defect

```text
kappa-P_p kappa,

(P_p kappa)(z)
 =sum_(r in Z)d_p(r)kappa(z+r log(p)).                (AW.22)
```

Only this complete prime-level scalar, after the renewal sum and the signed
outer/Sonin difference, may be asked to earn the missing half-power.

The base term `Xi_(S,0)` and outer-missing terms `Xi_(S,k,C)` must remain in a
uniform signed remainder.  They may not be silently discarded.

## 6. Why the future average is mandatory

The cancellation in `(AW.13)` removes only the unitary past.  It does not
remove

```text
A_>p iota_B H_(S,k)(W)iota_B* A_>p*.                 (AW.23)
```

Deleting `A_>p` would erase the future relative displacement whose
anti-concentration is Proof 272's valid probability input.  In the default
finite certificate, that deletion changes the complex scalar by

```text
2.91994e-3.
```

The alternate cohort changes it by `2.88015e-3`, and the cancellation guard
by `1.89693e-3`.  These finite values are guards, not continuous lower bounds.
They demonstrate that past cancellation does not imply future deletion.

## 7. Why relative modes stay signed

Equation `(AW.18)` is not a positive energy estimate because
`Y_(S,k,p)(W)` is generally non-self-adjoint for cross roots.  The relative
modes can cancel.

The deterministic `seed=1012` guard has

```text
relative scalar magnitude             5.1166e-5,
sum of relative-mode absolute values  12.7449 times that scalar,
maximum exact error                    1.36e-15.       (AW.24)
```

Therefore the order

```text
sum_r d_p(r)|Psi_r|
```

is not the route owner.  Keep the signed mode sum, the renewal sum, and the
two physical boundaries together until the final absolute value.

## 8. Finite certificate

The source layer uses Proof 285's non-Hermitian compact cross detector and
checks `(AW.4)--(AW.9)` with the actual random-defect and outer-escape maps.
The probability layer uses commuting finite spectral translations and checks
`(AW.13)--(AW.18)` independently.

The default WSL2 cohort (`multiplicity=10`, `root-radius=2`, `seed=286`) gives

```text
maximum source/probability error       1.48e-15,
common-past cancellation error         5.21e-18,
relative-mode grouping error           8.67e-19,
future-average deletion gap            2.92e-3.
```

The alternate cohort (`multiplicity=12`, `seed=2286`, `maximum-mode=10`)
gives

```text
maximum source/probability error       2.02e-15,
common-past cancellation error         1.52e-18,
relative-mode grouping error           5.42e-19,
future-average deletion gap            2.88e-3.        (AW.25)
```

The finite translation layer verifies only the probability and trace algebra.
It does not model the invariant real half-line, the CC20 Fourier boundary, or
the complete Markov-defect estimate described after `(AW.22)`.

## 9. Reproduction

Run from the repository root in WSL2:

```text
OPENBLAS_NUM_THREADS=1 python3 -B \
  docs/proofs/286_first_missing_relative_mode_probe.py

OPENBLAS_NUM_THREADS=1 python3 -B \
  docs/proofs/286_first_missing_relative_mode_probe.py \
  --multiplicity 12 --root-radius 2 --seed 2286 --maximum-mode 10

OPENBLAS_NUM_THREADS=1 python3 -B \
  docs/proofs/286_first_missing_relative_mode_probe.py \
  --seed 1012
```

The runs report

```text
support_first_missing_channel_factorization=EXACT,
random_plus_outer_missing_channels=EXACT,
common_past_translation_history=ELIMINATED,
local_centered_covariance=RELATIVE_MODE_SECOND_DIFFERENCE,
predictable_future_average=MANDATORY,
relative_geometric_coefficient=ONE_COPY_a^abs_r,
continuous_source_kernel_readback=OPEN,
complete_signed_extra_half_power=OPEN,
gate_3u=OPEN,
RH=UNPROVED.
```

## 10. Route judgment

Proof 286 constructs the first unmatched prime/mode scalar that Proofs
273--285 had only specified as a target.  The common past and the common
absolute local history are now gone by exact trace identities; the future
cloud, renewal feedback, and two boundaries remain exactly where the source
geometry needs them.

The next attack is

```text
Psi_(S,k,p,r) in (AW.18)
  -> expand both future-average legs to their relative law
  -> sum all relative modes into the Markov defect (AW.22)
  -> apply the three outer support windows (AW.21)
  -> retain the noncompact Sonin tail
  -> estimate the complete signed prime/renewal scalar
  -> Gate 3U.                                             (AW.26)
```

Proof 287 supplies and audits this correction.  The continuous completed
trace domain, Sonin Markov-defect bound, uniform base/outer remainder,
finite-`S` sign, arithmetic same-object trace identity, negative-owner
integration, Burnol's all-zero identity, and RH remain open.  No Lean owner or
route consumer is changed.

See `docs/proofs/287_future_cloud_markov_defect.md`.
