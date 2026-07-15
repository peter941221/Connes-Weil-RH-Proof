# Proof 273: Signed paired stopping and the positive-H1 guard

Date: 2026-07-15

Status: exact correction of Proofs 271 and 272.  Compact root support cancels
the completed scalar trace of a boundary crossing.  It does not cancel the
trace norm of that operator.  A one-element noncommutative column `H1` norm is
the trace norm, so the positive left-column estimate proposed in `(AH.30)` and
`(AI.20)` cannot receive the Proof 272 concentration factor.

The fixed-`S` renewal and prime-filtration algebra survives.  This proof writes
its exact left/right scalar pairing after the first-missing split.  Gate 3U now
requires a scalar disintegration of that paired trace.  The complete physical
branches and renewal feedback must remain inside the pairing until compact
support has acted.

## 1. Result

```text
+------------------------------------------------+------------------------------+
| layer                                          | judgment                     |
+------------------------------------------------+------------------------------+
| Proof 260 compact-support scalar trace         | zero outside support         |
| trace norm of the same crossing                | positive, exact              |
| one-column noncommutative H1 norm              | equals trace norm            |
| (AH.30)/(AI.20) positive stopped column        | rejected                     |
| Proof 270/271 renewal and Doob algebra         | retained                     |
| Proof 272 positive square-energy sum            | retained                     |
| fixed-S signed first-missing pairing           | exact                        |
| paired real-line scalar disintegration         | open, active Gate 3U        |
| finite-S sign and RH                           | unproved                     |
+------------------------------------------------+------------------------------+
```

The corrected ownership order is

```text
left renewal row * right survivor row
  -> complete outer/second-support/prolate product
  -> ordinary scalar trace
  -> compact-support displacement clip
  -> ordered-future concentration
  -> one absolute value.                                  (AJ.1)
```

## 2. A positive H1 norm cannot see trace support

For a finite noncommutative martingale difference column `(x_j)_j`, the column
square function and its `H1` norm are

```text
S_c(x)=(sum_j x_j* x_j)^(1/2),
norm(x)_(H1c)=Tr(S_c(x)).                               (AJ.2)
```

For one element `x`, this becomes

```text
norm((x))_(H1c)=Tr(|x|)=norm(x)_1.                     (AJ.3)
```

Proof 260 supplies a same-object compact-root crossing.  For nonzero
`g in C_c^infinity([-B,B])`, a finite interval `I`, and `|b|>2B`, put

```text
K_(I,b,g)=C_g U_b E_I C_g*.
```

Its completed scalar trace and trace norm are

```text
Tr(K_(I,b,g))=|I|F_g(b)=0,

norm(K_(I,b,g))_1=|I|norm(g)_2^2>0.                   (AJ.4)
```

Equations `(AJ.3)` and `(AJ.4)` give

```text
norm((K_(I,b,g)))_(H1c)
 =|I|norm(g)_2^2>0                                    (AJ.5)
```

while the compact-support scalar response is zero.  The concentration event
at displacement `b` has probability zero, so a positive `H1` estimate cannot
gain that factor on the same operator.  More generally, a same-object
factorization `K=X*Y` of the nonzero crossing has `X!=0`; every faithful
positive column norm charges that left leg.

The concentration obstruction persists for a diffuse path law.  Choose
pairwise `h`-separated shifts `b_1,...,b_N`, all outside `[-2B,2B]`, and put

```text
mu_N=(1/N)sum_(j=1)^N delta_(b_j),
Q_h(mu_N)=1/N.                                         (AJ.6)
```

Place equal-length intervals `I_j` so that the root-enlarged crossing blocks
are orthogonal, and define

```text
mathbbK_N=directSum_(j=1)^N (1/N)K_(I_j,b_j,g).
```

Proof 260's trace and nuclear formulas give

```text
Tr(mathbbK_N)=0,
norm(mathbbK_N)_1=|I_1|norm(g)_2^2,                   (AJ.7)
```

independent of `N`.  The concentration function tends to zero while the
positive one-column mass stays fixed.  A direct-sum `H1` estimate therefore
recovers total variation, not compact-support probability.

## 3. Why `stopped[...]` does not define a repair

Proof 272 wrote `(AI.20)` with a placeholder

```text
norm_root(stopped[L_W D^k I_(rand,p,m)*]).
```

There are only two interpretations:

```text
same operator:
  its positive column norm retains the nuclear mass in (AJ.5);

trace-truncated scalar:
  it can vanish outside support, but it is no longer the left row operator.
```

The second interpretation breaks the `H1`--`BMO` row pairing from Proof 271.
Taking a trace first produces a scalar coefficient, not an element of the
operator martingale whose column square function appears in `(AJ.2)`.

Proof 260 already rejected the same move for a two-Hilbert--Schmidt
factorization.  A noncommutative `H1` column applies another positive norm to
the same operator and encounters the same obstruction.

## 4. Exact signed first-missing pairing

Keep the notation

```text
K=EAB,
L=L_W,
D=Delta^(1/2),
I_C=CAB.                                               (AJ.8)
```

Let `I_p` be Proof 271's orthogonal Doob component of `I_rand`, so

```text
I_rand*I_rand=sum_p I_p*I_p,
Delta=I_rand*I_rand+I_C*I_C.                          (AJ.9)
```

Define paired channel legs

```text
X_0=L,                         Y_0=K,

X_(k,p)=L D^k I_p*,           Y_(k,p)=K D^k I_p*,

X_(k,C)=L D^k I_C*,           Y_(k,C)=K D^k I_C*.     (AJ.10)
```

Proof 261 makes each completed fixed-`S` product trace class.  Proof 271's
row identity and `(AJ.9)` give the exact scalar expansion

```text
Tr_B(N_W Gamma^(-1))
 =Tr(X_0*Y_0)

  +sum_(k>=0)
    [sum_p Tr(X_(k,p)*Y_(k,p))
      +Tr(X_(k,C)*Y_(k,C))].                          (AJ.11)
```

Indeed the bracket at level `k` is

```text
Tr_B(L* K D^k Delta D^k)
 =Tr_B(L* K Delta^(k+1)).                              (AJ.12)
```

Adding the base term recovers the fixed-`S` renewal
`Tr_B(L*K Gamma^(-1))` without a positive norm on either row.

## 5. Compact support belongs after the pairing

The detector is `W=C_g*C_g=C_F`, with

```text
supp(F) subset [-2B_root,2B_root].
```

Proof 262 gives the outer commutator kernel

```text
[W,E](x,y)
 =(1_E(y)-1_E(x))F(x-y).                              (AJ.13)
```

It also decomposes `[W,R]` into the outer crossing, the scattering-conjugate
second crossing, and the prolate commutator.  Proof 270 combines those three
terms inside `L`.  Consequently compact support applies to the completed
scalar products in `(AJ.11)`, after `X*Y` has recombined the physical branches.

Proof 260 shows why it cannot apply to `X` alone.  The operator `X` may retain
positive singular mass even when `Tr(X*Y)` vanishes at the same displacement.

## 6. Corrected source contract

Proof 272's positive square-energy concentration lemma remains available.  To use it, the
source proof must disintegrate the signed paired scalar in `(AJ.11)`, not the
left row norm.  A sufficient representation has the form

```text
Tr_B(N_W Gamma^(-1))
 =Rem_S(g)

  +sum_(p in S)sum_(m>=1)
    integral_R Phi_(S,p,m)(z;g) d mu_(S,<p)(z),        (AJ.14)
```

where `mu_(S,<p)` is Proof 272's ordered-future relative law.  The source must
derive all of the following on the real CC20 carrier:

```text
Phi includes the complete k-renewal and all three physical branches;

Phi_(S,p,m)(z;g)=0
  when |z+m log(p)|>2B_root;

|Phi_(S,p,m)(z;g)|
  <=C(1+m log(p))^(2d)p^(-m)norm(g)_(H^r)^2;

|Rem_S(g)|
  <=C(1+B_root)^d norm(g)_(H^r)^2,                    (AJ.15)
```

with constants independent of `S`.  The remainder in `(AJ.14)` must retain
any base/outer terms that the source algebra cannot separate without losing a
cancellation.

If `(AJ.14)--(AJ.15)` hold, Proof 272 sums the prime/mode part.  Proof 274
clarifies that the `p^(-m)` line in `(AJ.15)` is itself the missing
extra-half-power theorem, because the local signed coefficient is only
`p^(-m/2)`.  Neither Proof 273 nor an abstract martingale theorem constructs
this disintegration or gain.  The
intervening `D^k` remains inside the completed scalar kernel.

Proof 274 audits the coefficient in `(AJ.15)`.  The signed scalar channel owns
`p^(-m/2)` before the complete physical cancellation; the stronger `p^(-m)`
envelope in `(AJ.15)` is the missing extra-half-power theorem, not a consequence
of Proof 228's operator norm or Proof 272's square energy.

## 7. Literature boundary

Hong and Mei study noncommutative column/row `H1` and `BMO` spaces and their
duality:

```text
Hong and Mei,
John-Nirenberg inequality and atomic decomposition for noncommutative
martingales,
arXiv:1112.3187v2.
https://arxiv.org/abs/1112.3187
```

That theory estimates positive square functions such as `(AJ.2)`.  It does not
turn scalar trace cancellation into a smaller norm of the same operator.

de Branges--Rovnyak models describe ranges of contraction defect operators and
can model `D=(B-K*K)^(1/2)` abstractly:

```text
Ball and Bolotnikov,
de Branges-Rovnyak spaces: basics and theory,
arXiv:1405.2980.
https://arxiv.org/abs/1405.2980
```

The abstract defect model does not supply the real-line boundary kernel or the
signed scalar support rule in `(AJ.13)--(AJ.15)`.

## 8. Reproduction

Run in WSL2 from the Windows source snapshot:

```text
python3 -B docs/proofs/273_signed_paired_stopping_guard_probe.py

python3 -B docs/proofs/273_signed_paired_stopping_guard_probe.py \
  --multiplicity 10 --seed 1273 --maximum-power 768
```

The first layer imports Proof 260's compact crossing and compares its zero
trace with its positive nuclear and one-column `H1` mass.  The second layer
checks `(AJ.11)` by splitting Proof 271's finite model into random and outer
first-missing channels.

The finite model proves algebra only.  It does not prove the source
disintegration `(AJ.14)`.

## 9. Route judgment

Proof 273 withdraws the positive `H1` stopped-column target `(AH.30)/(AI.20)`.
It preserves the fixed-`S` renewal algebra and Proof 272's positive
square-energy concentration sum.

The active Gate 3U bottom is Proof 274 `(AK.12)`: construct the
same-object signed scalar disintegration `(AJ.14)` with its extra half-power,
or prove a sharper location-aware stopping bound for the exact
`p^(-m/2)` scalar ledger.  The finite-S sign, arithmetic same-object trace identity,
negative-owner integration, Burnol's identity, and RH remain open.  No Lean
owner or route rewire is authorized.
