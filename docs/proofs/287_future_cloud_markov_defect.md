# Proof 287: Future-cloud relative law and local Markov defect

Date: 2026-07-15

Status: exact probability-level successor to Proof 286 and correction of its
former analytic target.  Expanding both predictable-future legs leaves only
their relative displacement.  Summing the complete local relative-mode family
before an absolute value gives one centered Markov defect.

Compact support gives three outer-boundary windows, not the single window
formerly displayed in Proof 286.  The complete Sonin channel is not compactly
supported and must be controlled by a signed tail theorem.  A per-mode
extra-half-power estimate is false even for an elementary compact profile.
Gate 3U, the finite-`S` sign, the arithmetic same-object identity, Burnol's
identity, and RH remain open.

## 1. Result

```text
+------------------------------------------------+------------------------------+
| layer                                          | judgment                     |
+------------------------------------------------+------------------------------+
| two predictable-future legs                   | exact probability expansion  |
| common future absolute history                | eliminated in scalar trace   |
| surviving future owner                        | relative displacement law    |
| complete local relative-mode sum              | one Markov defect            |
| constant scalar mode                          | annihilated exactly          |
| former single support window                  | false                        |
| outer second-difference support               | three windows                |
| complete Sonin support                        | noncompact / tail required   |
| per-mode extra-half-power                     | false                        |
| complete signed Markov-defect bound           | open                         |
| Gate 3U and RH                                 | open / unproved              |
+------------------------------------------------+------------------------------+
```

The ownership correction is

```text
individual relative modes
  -X-> no termwise absolute values or per-mode half-power;

complete signed mode family
  -> local relative-geometric Markov defect
  -> outer three-window stopping
     minus complete Sonin tail
  -> one scalar estimate.                                  (AX.1)
```

## 2. Expand both future legs

Retain Proof 286's completed reward and put

```text
X_(S,k,p)(W)
 :=iota_B H_(S,k)(W)iota_B*.                         (AX.2)
```

Let `nu_>p` be the one-sided probability law represented by the predictable
future average:

```text
A_>p=integral_R U_y d nu_>p(y).                      (AX.3)
```

The two-leg relative law is

```text
mu_>p=Law(Y-Y'),  Y,Y' independent with law nu_>p.   (AX.4)
```

For a local relative prime displacement

```text
ell=r log(p),
T_ell=U_ell-I,                                       (AX.5)
```

Proof 286's scalar is

```text
Psi_(S,k,p,r)(W)
 =Tr(T_ell A_>p X_(S,k,p)(W)A_>p* T_ell*).           (AX.6)
```

Expand `(AX.3)` on both sides.  A typical term is

```text
Tr(T_ell U_y X U_(-y')T_ell*).                       (AX.7)
```

Conjugate the entire completed trace by `U_(-y')`.  Translations commute with
`T_ell`, so `(AX.7)` becomes

```text
Tr(T_ell U_(y-y') X T_ell*).                         (AX.8)
```

Therefore

```text
Psi_(S,k,p,r)(W)
 =integral_R Omega_(S,k,p)(ell,z;W)d mu_>p(z),       (AX.9)

Omega_(S,k,p)(ell,z;W)
 :=Tr_completed(T_ell U_z X_(S,k,p)(W)T_ell*).
```

The common absolute future history is gone.  Only the relative future
displacement `z=y-y'` remains.  No half-line invariance or periodic model is
used in this trace algebra.

## 3. The legal completed second difference

Equation `(AX.9)` is the continuous owner.  It is defined as one completed
second difference.  Do not split it into four ambient traces unless a source
trace-domain theorem licenses those coefficients separately.

In a finite model, or whenever the individual displacement coefficient

```text
kappa_X(z)=Tr(U_z X)                                  (AX.10)
```

is legal, cyclicity gives the useful coordinate identity

```text
Omega_X(ell,z)
 =2 kappa_X(z)-kappa_X(z+ell)-kappa_X(z-ell).         (AX.11)
```

Proof 288 proves the corresponding root-completed coefficient domain for the
specific reward `X_(S,k,p)(W)`: it is a signed sum of two trace-class detector
commutator products.  Hence `(AX.10)--(AX.11)` are ordinary fixed-`S` traces
for this owner.  This does not weaken Proof 263's prohibition on the unrelated
raw point trace of the unsmoothed projection difference.

## 4. Sum all local modes first

Proof 286 gives the symmetric local relative law

```text
d_p(r)=(1-a_p)/(1+a_p) a_p^|r|,
a_p=p^(-1/2),
sum_(r in Z)d_p(r)=1.                                 (AX.12)
```

Define its translation Markov operator by

```text
(P_p f)(z)=sum_(r in Z)d_p(r)f(z+r log(p)).           (AX.13)
```

When `(AX.10)` is legal, symmetry of `d_p` and `(AX.11)` give

```text
1/2 sum_(r in Z)d_p(r)Omega_X(r log(p),z)

 =kappa_X(z)-(P_p kappa_X)(z).                       (AX.14)
```

Thus the complete local innovation is the Markov defect

```text
(I-P_p)kappa_X.                                      (AX.15)
```

The completed version of `(AX.14)` is obtained by keeping the left side as a
single signed trace sum.  Since `P_p 1=1`,

```text
(I-P_p)constant=0.                                   (AX.16)
```

This is the exact scalar fixed-mode cancellation from Proofs 253, 257, and
269 in the causal relative-law coordinate.  It is visible only after every
relative mode has recombined.

## 5. Correct outer support: three windows

For the completed outer half-line crossing, compact root support gives

```text
kappa_E(z)=0 when |z|>2B_root.                        (AX.17)
```

Substitution into `(AX.11)` shows

```text
Omega_E(ell,z)=0
```

unless at least one of

```text
|z|<=2B_root,
|z+ell|<=2B_root,
|z-ell|<=2B_root                                     (AX.18)
```

holds.  These are three support windows.  Proof 286's former condition

```text
|z+ell|<=2B_root                                     (AX.19)
```

kept only one orientation and is false for the centered second difference.

The compact-profile guard takes `B_root=1`, so the cross-correlation radius is
`2`, and uses `ell=9,z=0`.  Both shifted coefficients vanish but the central
coefficient survives:

```text
Omega_E(9,0)=2 kappa_E(0)=6.                         (AX.20)
```

The old window `(AX.19)` is separated from the support by `7`, yet the scalar
is nonzero.  The union `(AX.18)` predicts it exactly.

## 6. The Sonin channel has a tail, not support

Proof 275 proves only the outer deletion

```text
q_E(z;g)=0,  |z|>2B_root.                            (AX.21)
```

It then identifies the surviving response with the complete Sonin/prolate
tail.  Proof 276 proves an `exp(-|z|/2)` scale for the static CC20 correction,
while Proof 277 shows that the moving object is a Toeplitz covariance whose
compressed term still needs a source theorem.

Consequently the complete two-boundary second difference does not have the
exact support `(AX.18)`.  Its correct organization is

```text
outer channel:
  three-window compact stopping;

Sonin channel:
  signed second-difference tail with all E/E_hat/K_prol pieces recombined.
                                                               (AX.22)
```

Moving the Sonin contribution into a compactly supported `Phi` would erase
the very half-power term isolated by Proofs 275--277.

## 7. Why the per-mode half-power is false

For the compact triangular profile in the guard, fix `z=0` and let
`|ell|>2B_root`.  Equation `(AX.20)` is independent of `ell`.  Therefore a
bound of the former Proof 286 form

```text
|Omega_E(ell,0)|<=C exp(-|ell|/2)                    (AX.23)
```

does not follow from compact support and is false for this owner.

At `p=3,r=9`, the proposed factor is

```text
3^(-9/2)=7.12778e-3,
```

while the compact-profile second difference is `6`, a ratio of `841.777`.
The alternate `r=11` guard gives a ratio `2525.33`.

The complete Markov defect behaves differently.  For the point profile
`kappa=delta_0`,

```text
[(I-P_p)kappa](0)
 =1-d_p(0)
 =2a_p/(1+a_p)=O(a_p),                               (AX.24)
```

not `O(a_p^2)`.  Thus centering and compact support reproduce the one
route-owned half-power, but do not by themselves create the missing second
half-power.

## 8. Correct analytic target

Let `mathfrakD_(S,k,p)(z;eta,xi)` denote the completed version of the full
local Markov defect in `(AX.14)`, with the outer and Sonin contributions kept
as a signed pair and without defining illegal raw coefficients.

The next theorem must estimate

```text
sum_(k>=1)
 integral_R mathfrakD_(S,k,p)(z;eta,xi)d mu_>p(z),    (AX.25)
```

not the individual relative modes.  Its source proof needs two coupled
mechanisms:

```text
outer three-window part:
  use the relative-future concentration function on all three windows;

Sonin part:
  prove the complete Toeplitz-covariance / prolate tail and cancel its
  central Markov component against the outer channel before one absolute
  value.                                               (AX.26)
```

The desired prime-level output is an `O(p^(-1))` stopped scalar, with the
location factor needed by Proof 272, after the complete local Markov defect
and renewal sum have been taken.  Proving `O(p^(-1))` mode by mode is neither
necessary nor generally true.

The base renewal level and outer-missing channel remain part of the uniform
remainder and must be controlled on the same owner.

## 9. Finite certificate

The probability layer expands two future primes on both legs, checks the
common-future cancellation outcome by outcome, groups the relative law, and
then compares the complete local mode sum with the Markov defect.

The default WSL2 cohort reports

```text
maximum exact error                         2.22e-16,
maximum common-future cancellation error    8.27e-17,
second-difference coordinate error          3.88e-17,
mode-sum/Markov-defect error                 1.67e-18.
```

The alternate cohort reports

```text
maximum exact error                         2.22e-16,
maximum common-future cancellation error    7.69e-17,
second-difference coordinate error          4.91e-17,
mode-sum/Markov-defect error                 5.64e-18.  (AX.27)
```

The compact-profile layer checks the three-window support exactly and rejects
the old single-window and per-mode targets.  These finite certificates do not
prove the continuous Sonin tail.  Proof 288 supplies the separate analytic
trace-domain theorem for `(AX.10)`.

## 10. Evidence and reproduction

Source evidence for the support/tail distinction:

```text
Proof 260 completed outer crossing:
docs/proofs/260_schatten_legality_signed_trace_gate.md

Proof 275 outer deletion and surviving Sonin tangent:
docs/proofs/275_one_prime_first_jet_source_reduction.md

CC20 static Sonin tail source:
Connes--Consani, arXiv:2006.13771
https://arxiv.org/abs/2006.13771
```

Run in WSL2:

```text
OPENBLAS_NUM_THREADS=1 python3 -B \
  docs/proofs/287_future_cloud_markov_defect_probe.py

OPENBLAS_NUM_THREADS=1 python3 -B \
  docs/proofs/287_future_cloud_markov_defect_probe.py \
  --multiplicity 12 --seed 2287 --maximum-mode 5 \
  --guard-relative-mode 11
```

Both runs report

```text
predictable_future_two_leg_expansion=EXACT,
common_future_history=ELIMINATED,
future_cloud_owner=RELATIVE_DISPLACEMENT_LAW,
complete_relative_mode_sum=LOCAL_MARKOV_DEFECT,
scalar_fixed_mode=ANNIHILATED_BY_COMPLETE_MODE_SUM,
former_single_support_window=REJECTED,
outer_second_difference_support=THREE_WINDOWS,
per_mode_extra_half_power=REJECTED,
raw_point_kappa_continuous_domain=OPEN,
complete_sonin_markov_defect_bound=OPEN,
gate_3u=OPEN,
RH=UNPROVED.
```

## 11. Route judgment

Proof 287 removes a false target before it can contaminate the continuous
analysis.  The first unmatched prime is real, but it must be consumed as one
complete local Markov defect, not as independently bounded relative modes.
Compact support controls three outer windows; the Sonin correction supplies a
tail, not a fourth compact window.

The next attack is

```text
completed Markov defect (AX.25)
  -> fixed-S legal coefficient domain, Proof 288
  -> outer three-window concentration
  -> source Sonin Toeplitz-covariance tail
  -> cancel the central outer/Sonin Markov component
  -> O(p^(-1)) stopped prime scalar
  -> Proof 272 summation
  -> Gate 3U.                                             (AX.28)
```

The Sonin Markov-defect bound, uniform base/outer remainder, Gate 3U,
finite-`S` sign, arithmetic same-object trace identity, negative-owner
integration, Burnol's all-zero identity, and RH remain open.  No Lean owner or
route consumer is changed.

## 12. Successor audit

Proof 288 closes the fixed-`S` domain by rewriting the ambient reward as

```text
B[W,R]R A*K Delta^(k-1)iota_B*
 -B A*C[W,E]K Delta^(k-1)iota_B* in S1.
```

It also identifies the complete mode sum with

```text
Tr(U_z(I-A_pA_p*)X_(S,k)(W)).
```

This is an ordinary trace and is continuous in `z`.  Its trace norm remains
an `S`-dependent legality witness, not the Gate 3U estimator.  See
`docs/proofs/288_completed_markov_trace_domain.md`.

Successor correction: Proof 289 retains the local mode sum `(AX.14)` but does
not estimate its prime channels separately.  With the mandatory future
factors left in place,

```text
sum_p P_fut(p)(I-P_p)kappa
 =(I-product_p P_p)kappa.
```

The proposed prime-level `O(p^(-1))` output in `(AX.28)` is therefore an
unnecessary sufficient target.  The complete global renewal-boundary estimate
in Proof 289 `(AZ.26)` is the active successor.
