# Proof 229: Euler triangular-profile compactness

Date: 2026-07-14

Status: the complete normalized principal Euler channel from Proof 225 is
compact after post-`Q` finite-window compression.  The proof sums all
triangular widths before differentiating.  Their exact Euler envelope is
continuous and piecewise linear.  Two cellwise integrations by parts transfer
the post-`Q` derivatives away from the rapidly oscillating archimedean phase;
the first boundary family cancels by continuity, while the second is precisely
a logarithmic-chirp series controlled by Proof 228.  The remaining cell
interiors are absolutely summable continuous kernels.  The resulting compact
operator need not be Hilbert--Schmidt.  This closes the uniform principal
channel, not the full metric/amplitude crossing from Proof 227.  The integrated
three-row sign and RH remain open.  No Lean owner is authorized.

## 1. Sum the triangular widths first

Fix one prime and write

```text
L=log(p),
a=p^(-1/2).
```

Proof 225's compact Fourier profile for width `q` is, up to its fixed
normalization,

```text
F_q(x)=(q-|x|)_+ k_infinity(x),
k_infinity(x)=2exp(x/2)cos(2pi exp(x)).                (P.1)
```

Define the complete Euler envelope

```text
W_p(r)=sum_(m>=1)a^m(mL-r)_+,   r>=0.                 (P.2)
```

Then the sum of all profiles is the single object

```text
H_p(x)=W_p(|x|)k_infinity(x).                         (P.3)
```

There is no convergence ambiguity in `(P.2)`: for fixed `r`, only a geometric
tail remains.

## 2. Exact cell formula

Let

```text
n=floor(r/L),
t=r-nL,              0<=t<L.                         (P.4)
```

The two geometric sums are

```text
sum_(m>=n+1)a^m=a^(n+1)/(1-a),

sum_(m>=n+1)m a^m
 =a^(n+1)((n+1)-na)/(1-a)^2.                         (P.5)
```

Substituting `r=nL+t` gives the exact cancellation of every `n`-dependent
linear term:

```text
W_p(nL+t)
 =a^(n+1)(L-(1-a)t)/(1-a)^2.                         (P.6)
```

This formula has three consequences.

First, `W_p` is continuous.  At the right endpoint of cell `n`,

```text
a^(n+1)(L-(1-a)L)/(1-a)^2
 =a^(n+2)L/(1-a)^2,                                  (P.7)
```

which is the left endpoint of cell `n+1`.

Second, its derivative is constant inside each cell:

```text
W_p'(r)=-a^(n+1)/(1-a).                               (P.8)
```

Third, at `r=nL`, `n>=1`, the right-minus-left derivative jump is exactly

```text
W_p'(nL+)-W_p'(nL-)=a^n.                              (P.9)
```

Thus the envelope and its derivative have the sharp bounds

```text
W_p(r)=O(exp(-r/2)),
W_p'(r)=O(exp(-r/2)),                                 (P.10)
```

with constants depending only on `p`.

## 3. Tail geometry of the summed profile

On the positive tail, `(P.10)` cancels the amplitude growth in
`k_infinity`:

```text
H_p(x)
 =bounded cell amplitude times cos(2pi exp(x)),
 x->+infinity.                                        (P.11)
```

On the negative tail, `exp(x)` tends to zero, so every fixed derivative of
`k_infinity(x)` is `O(exp(x/2))`.  Since
`W_p(|x|)=O(exp(x/2))`, one has away from cell boundaries

```text
H_p^(j)(x)=O(exp(x)),
x->-infinity,
j=0,1,2.                                              (P.12)
```

At `x=-nL`, formula `(P.9)` and
`k_infinity(-nL)=O(p^(-n/2))` give

```text
jump(H_p') at -nL =O(p^(-n)).                         (P.13)
```

The positive tail is oscillatory with bounded amplitude; the negative tail
and all of its cell jumps decay geometrically.

## 4. The cellwise derivative-transfer lemma

The inverse Fourier kernel of the product in Proof 225 is a finite linear
combination of convolutions of `H_p` with an archimedean response or its
reflection.  The only tail that is not absolutely differentiable twice has,
after putting `x=-nL-t`, `0<=t<=L`, the form

```text
G_n(r)=integral_0^L A_n(r,t) Phi_n(r,t) dt,

Phi_n(r,t)=exp(i c p^n exp(r+t)),                      (P.14)
```

where `c` is a fixed nonzero real constant.  The amplitude scale follows
directly, rather than from a qualitative oscillation claim.  On this cell,

```text
W_p(nL+t)=a^(n+1) w_p(t),

k_infinity(-nL-t)
 =2a^n exp(-t/2)cos(2pi p^(-n)exp(-t)),

k_infinity(r+nL+t)
 =2a^(-n)exp((r+t)/2)
    cos(2pi p^n exp(r+t)),                            (P.15a)
```

where `w_p` and its cell derivatives are bounded independently of `n`.
After the fast last cosine is put into `Phi_n`, the product of the three
remaining scales is

```text
a^(n+1) * a^n * a^(-n)=a^(n+1)=O(p^(-n/2)).          (P.15b)
```

The only phase left in the amplitude is the slow
`p^(-n)exp(-t)` phase.  Therefore, on every compact `r` interval,

```text
|(partial_r-partial_t)^j A_n(r,t)|
 <=C_I p^(-n/2),
j=0,1,2.                                              (P.15)
```

The phase has the exact derivative identity

```text
partial_r Phi_n=partial_t Phi_n.                      (P.16)
```

Put `D=partial_r-partial_t`.  One integration by parts gives

```text
partial_r G_n
 =integral_0^L (D A_n)Phi_n dt
   +[A_n Phi_n]_(t=0)^(t=L).                          (P.17)
```

When `(P.17)` is summed over adjacent cells, every internal endpoint in the
second term cancels.  This is an exact consequence of the continuity
`(P.7)` and

```text
p^n exp(r+L)=p^(n+1)exp(r).                           (P.18)
```

Differentiate once more.  The already-cancelled boundary family remains
cancelled as an identity in `r`, and

```text
partial_r^2 sum_n G_n
 =sum_n integral_0^L (D^2 A_n)Phi_n dt
   +sum_(internal cells)[(D A_n)_left-(D A_n)_right]Phi_n
   +finite outer boundaries.                          (P.19)
```

The interior integrals in `(P.19)` are uniformly bounded by
`C_I p^(-n/2)` and therefore converge uniformly to a continuous local kernel.
Their finite-window operators are Hilbert--Schmidt.

The internal boundary coefficient is controlled by the only failure of first
derivative matching, namely `(P.9)--(P.13)`.  After the fixed half-density is
removed, it is `O(p^(-n/2))` times a logarithmic chirp at frequency `p^n`.
Proof 228 gives the additional operator-norm estimate `O(p^(-n/2))` for that
chirp.  Hence

```text
norm(internal boundary operator at cell n)=O(p^(-n)), (P.20)
```

which is summable.  Each boundary operator is compact, and their series is an
operator-norm limit of compact operators.

This proves that two post-`Q` derivatives are legal after summing the cells,
even though they are not legal under a termwise Hilbert--Schmidt absolute
value.

## 5. The other tail and central cells

For `x->+infinity`, the reflected archimedean factor in the convolution is on
its exponentially decaying tail.  Its first two `r` derivatives remain
`O(exp(-x/2))`.  Multiplication by the bounded profile `(P.11)` makes the cell
contribution `O(p^(-n/2))`, absolutely summable in local `C^2`.

The finitely many central cells have ordinary smooth kernels.  The conjugate
phases obey the same estimates.  Therefore every term in the real part of
Proof 225's exact principal kernel is covered by `(P.19)--(P.20)` or by this
absolute-tail argument.

## 6. Principal Euler compactness theorem

Let `I` be any bounded root interval.  Sum Proof 225's normalized principal
channels over all widths `q_m=m log(p)` with their exact Euler coefficients,
then apply post-`Q` on the root.

Sections 4--5 decompose the resulting compression into

```text
an absolutely convergent series of Hilbert--Schmidt interior operators;

an operator-norm convergent series of compact boundary chirps;

a finite sum of central Hilbert--Schmidt operators.    (P.21)
```

Consequently:

```text
the complete normalized principal Euler channel is compact on L2(I).       (P.22)
```

The compact operator in `(P.22)` need not be Hilbert--Schmidt.  Proof 228
shows exactly why: the positive-frequency boundary terms have nondecaying
termwise Hilbert--Schmidt norms even though their operator norms are summable.

## 7. Corrected remaining contract

Proof 227's contract `(F.23)` asked for one integrated `L2` kernel and hence a
Hilbert--Schmidt result.  That remains a sufficient condition, but Proofs
228--229 show that it is stronger than necessary.

The sharp compactness contract for the full same-object crossing is now:

```text
decompose the internal complete-crossing profile into

  locally L2 interiors with absolutely summable HS norms

  plus logarithmic-chirp boundaries with summable operator norms.          (P.23)
```

No termwise absolute-HS theorem should be required for the second family.
The normalized principal part satisfies `(P.23)`.  The nonconstant metric
defect inside Proof 227's complete `Y_alpha+Y_alpha*` has not yet been put into
this profile and remains the active compactness bottom.

## 8. Reproduction

Run in WSL:

```text
python3 -B docs/proofs/229_euler_triangular_profile_compactness.py
python3 -B docs/proofs/229_euler_triangular_profile_compactness.py --prime 3
```

The deterministic certificate checks:

```text
the closed envelope formula (P.6) against the defining series;
continuity at every tested cell boundary (P.7);
the exact derivative jumps (P.9);
uniform positive/negative tail envelopes;
convergence of the interior and boundary majorant series in (P.21).
```

The script checks the algebra and sharp scales.  The compactness proof is the
derivative-transfer identity `(P.16)--(P.20)` together with Proof 228's exact
Fourier conjugation.

## 9. Route judgment

```text
closed Euler triangular envelope:               exact
first internal boundary family:                  cancels exactly
second boundary family:                          operator-norm summable
cell interiors:                                  HS-absolutely summable
complete normalized principal Euler channel:    compact
global Hilbert--Schmidt claim:                    unnecessary / not claimed
full metric complete-crossing profile:           open
integrated three-row sign:                       open
Lean owner or route rewire:                      none
RH:                                              unproved
```

The next proof must derive the corresponding cell amplitudes for Proof 227's
full metric crossing.  The principal channel itself is no longer an open
Euler-summation gate.
