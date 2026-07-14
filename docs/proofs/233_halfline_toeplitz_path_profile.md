# Proof 233: half-line Toeplitz path profile

Date: 2026-07-14

Status: exact word normal form and summable profile estimate for the half-line
Toeplitz factors in Proof 232's linear channel.  Every word in compressed
positive and negative Euler translations collapses to one partial translation
whose threshold is the maximum of a finite lattice path.  The endpoint
amplitude produced at that threshold is canceled exactly by Proof 228's
Fourier operator-norm gain.  The Neumann coefficient sum is then controlled
by `sum_k (1+k)^d eta^k`, with `eta<1`.  Hence the half-line factors
`M^(-1)` and `D^(-1)` preserve Proof 229's post-`Q` profile class.  The
Sonin-corner factor `A^(-1)` still requires the scattering/prolate reduction;
full metric compactness, the integrated sign, and RH remain open.  No Lean
owner is authorized.

## 1. Compressed translation words

Work in the logarithmic coordinate.  Let

```text
(U^n f)(x)=f(x-nL),
L=log(p),
P f=1_[0,infinity)(x) f(x).                            (H.1)
```

For a path

```text
epsilon=(epsilon_1,...,epsilon_k),
epsilon_j in {-1,+1},                                 (H.2)
```

put

```text
s_0=0,
s_j=epsilon_1+...+epsilon_j,
M(epsilon)=max_(0<=j<=k) s_j.                         (H.3)
```

Consider the compressed word

```text
W_epsilon
 =P U^(epsilon_1) P U^(epsilon_2) P ...
    U^(epsilon_k) P.                                  (H.4)
```

Reading the indicators from left to right gives the exact pointwise formula

```text
(W_epsilon f)(x)
 =1_[M(epsilon)L,infinity)(x)
    f(x-s_k L).                                       (H.5)
```

Indeed, the successive projections impose

```text
x>=0,
x-s_1 L>=0,
...,
x-s_k L>=0,                                           (H.6)
```

and their conjunction is precisely `x>=M(epsilon)L`.  Reflection gives the
corresponding formula for the negative half-line.  Thus no word creates a new
kind of kernel: it changes only a translation and one endpoint threshold.

## 2. The two inverse families

For the graph factor in Proof 232,

```text
M=P(I-alpha U)P,

M^(-1)=sum_(k>=0) alpha^k (P U P)^k.                  (H.7)
```

This is the one-sided specialization of `(H.5)`.  Its `k`th word is one
partial translation with threshold at most `kL`, and its coefficient is
`alpha^k`.

For the metric corner,

```text
D=(1+alpha^2)P-alpha P(U+U*)P,

D^(-1)
 =(1/(1+alpha^2))
   sum_(k>=0) beta^k [P(U+U*)P]^k,

beta=alpha/(1+alpha^2).                               (H.8)
```

Expanding the `k`th power gives the `2^k` paths in `(H.2)`.  Their total
absolute coefficient is

```text
2^k beta^k=eta^k,
eta=2alpha/(1+alpha^2).                               (H.9)
```

On the route interval `alpha<=p^(-1/2)<=2^(-1/2)`, one has

```text
eta<=2sqrt(2)/3<1.                                    (H.10)
```

## 3. Endpoint growth cancels path by path

The only non-Hilbert--Schmidt family in Proof 229 is the positive
archimedean endpoint.  If a word has threshold height `M=M(epsilon)`, the
translated response contains

```text
k_infinity(r+M L)
 =2 p^(M/2) exp(r/2)
    cos(2*pi*p^M*exp(r)).                             (H.11)
```

The complex chirp operator at frequency `p^M` has, by Proof 228,

```text
operator norm <=p^(-M/2).                             (H.12)
```

Therefore the apparent endpoint growth cancels exactly for every path:

```text
p^(M/2) * p^(-M/2)=1.                                 (H.13)
```

The cancellation depends on the path maximum, not its final displacement.
Using only `s_k` would miss large excursions that return to the origin.

Two cellwise derivative transfers create at most a fixed polynomial in the
path length.  For every fixed graph order `d`, the full endpoint majorant is

```text
sum_(k>=0) (1+k)^d eta^k<infinity.                    (H.14)
```

The one-sided family `(H.7)` has the smaller majorant

```text
sum_(k>=0) (1+k)^d alpha^k<infinity.                  (H.15)
```

No termwise Hilbert--Schmidt estimate is used for `(H.11)`.  The chirp bound
is applied before the path sum, exactly as in Proofs 228--229.

## 4. Interior and negative endpoint families

After the fast phase in `(H.11)` is extracted, all derivatives of the local
cell amplitude are bounded by a fixed polynomial in `k`; the path word itself
has norm at most one.  The cell interiors therefore have absolutely summable
Hilbert--Schmidt majorant `(H.14)`.

At the negative endpoint,

```text
k_infinity(r-M L)
 =2 p^(-M/2) exp(r/2)
    cos(2*pi*p^(-M)*exp(r)).                          (H.16)
```

so the ordinary Hilbert--Schmidt estimate already gains `p^(-M/2)`.  It is
strictly easier than the positive endpoint.  Reflections and adjoints obey
the same estimates.

Consequently the half-line inverse factors in the linear channel `(Q.26)` of
Proof 232 preserve the profile ledger

```text
HS-absolutely summable interiors
  plus operator-norm-summable logarithmic chirps.      (H.17)
```

## 5. Why this does not yet close the Sonin corner

The factor `A^(-1)` in Proof 232 is compressed to the Sonin projection `r`,
not to a single half-line.  CC20 gives

```text
P P_hat P=r+K_prol,                                   (H.18)
```

where `K_prol` is positive trace class and `P_hat` is the archimedean
scattering conjugate of the other half-line.  Terms containing `K_prol` are
already compact after bounded metric dressing.  What remains is to show that
the no-`K_prol` alternating `P/P_hat` words reduce, modulo two-crossing
root-Hilbert--Schmidt terms, to the single-half-line path class above.

The scattering multiplier and every Euler multiplier commute with the
logarithmic differential defining `Q`.  This removes derivative loss, but it
does not by itself classify the number of half-line crossings in an
alternating word.  That exact crossing-count reduction is the next gate.

## 6. Reproduction

Run in WSL:

```text
python3 -B docs/proofs/233_halfline_toeplitz_path_profile.py
python3 -B docs/proofs/233_halfline_toeplitz_path_profile.py --prime 3
```

The certificate enumerates every `+/-1` path through the requested depth and
checks `(H.5)` on a finite lattice away from the artificial outer boundary.
It also checks the exact path coefficient identity `(H.9)`, the endpoint
compensation `(H.13)`, and the convergence of the polynomially weighted
majorants `(H.14)--(H.15)`.

## 7. Route judgment

```text
compressed half-line word normal form:          exact
path-maximum endpoint owner:                    exact
positive endpoint growth/chirp cancellation:   exact
M^(-1) half-line profile stability:             proved
D^(-1) half-line profile stability:             proved
prolate insertions:                             trace class / compact
A^(-1) alternating Sonin profile stability:     open
full metric post-Q compactness:                 open only at Sonin branch
integrated three-row sign:                      open
Lean owner or route rewire:                     none
RH:                                             unproved
```

The next proof must classify the alternating scattering words modulo the
already closed two-crossing root ideal.
