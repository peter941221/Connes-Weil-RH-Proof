# Proof 353: graph detector innovation identity

Date: 2026-07-18

Status: exact one-step and sequential finite-trace identity for the detector
response of a Gram-normalized graph projection.  It gives an explicit
candidate detector innovation on the literal moving quotient subspaces of
Proof 343, without expanding the physical outer/Sonin/prolate branches.

The identity is algebraic.  Its infinite-dimensional use still requires a
root-sandwiched trace-legality theorem for every displayed rectangular cycle
and a uniform weighted Hilbert--Schmidt estimate for the innovation row.
Those analytic statements are not proved here.  Gate 3U, the finite-S sign,
Burnol's identity, and RH remain open.

## 1. Result

```text
+------------------------------------------------+---------------------------+
| layer                                          | judgment                  |
+------------------------------------------------+---------------------------+
| one graph projection block difference         | exact                     |
| one self-adjoint detector response             | one innovation pairing    |
| sequential endpoint telescope                 | exact                     |
| dependence on branch decomposition             | none                      |
| finite-matrix certificate                      | passes                    |
| infinite root-sandwiched rectangular cycles    | open legality producer    |
| weighted detector S2 row                       | open uniform estimate     |
| Gate 3U / finite-S sign / Burnol / RH           | open / open / open / open|
+------------------------------------------------+---------------------------+
```

The new reduction is

```text
Proof 343 moving quotient range
  -> one Euler factor
  -> canonical graph cosine/sine (C,S)
  -> exact projection block difference
  -> keep W whole
  -> one detector innovation H_W
  -> pair H_W with S only after trace legality.       (GI.1)
```

## 2. Exact graph block

Let `P` be an orthogonal projection and write the ambient Hilbert space as

```text
H=Ran(P) orthogonal-direct-sum Ran(I-P).              (GI.2)
```

Let `X:Ran(P)->Ran(I-P)` be a bounded graph coordinate and define

```text
C=(I+X*X)^(-1/2),
S=XC,
V=[C;S].                                             (GI.3)
```

Then `V*V=I` and the projection onto the graph is `P_X=VV*`.  Since `C` is
positive and commutes with `X*X`,

```text
C^2+S*S=I.                                           (GI.4)
```

Consequently

```text
P_X-P
 =[[ -S*S, C S*],
   [  S C, S S*]].                                   (GI.5)
```

Equation `(GI.5)` is an operator identity.  It uses no trace, determinant,
finite-dimensional approximation, or small-angle expansion.  Both the
linear off-diagonal channel and the quadratic diagonal correction remain.

For Proof 350's Euler step,

```text
X=a(I-aU_11)^(-1)U_10,                               (GI.6)
```

so `(GI.5)` is the actual Gram-corrected range change, not an oblique
similarity.

## 3. Complete detector innovation

Let a self-adjoint detector have blocks

```text
W=[[W_00,W_01],
   [W_10,W_11]],

W_01=W_10*.                                          (GI.7)
```

In finite dimension, or whenever all rectangular trace cycles below are
already legal, multiply `(GI.5)` by `W` and take the trace.  The two
off-diagonal terms are conjugates.  The two diagonal terms can be cycled once
to the source graph carrier.  This gives

```text
Tr[W(P_X-P)]
 =Re Tr[S* H_W],                                     (GI.8)

H_W
 :=2 W_10 C+W_11 S-S W_00.                          (GI.9)
```

The three terms in `(GI.9)` have distinct roles:

```text
2 W_10 C:
  completed first-order boundary crossing;

W_11 S-S W_00:
  diagonal intertwining defect forced by the
  quadratic blocks of the orthogonal projection.     (GI.10)
```

Deleting the second line of `(GI.10)` would replace the orthogonal graph
projection by its linear tangent.  That would repeat the error rejected in
Proofs 226, 250, and 350.

Equation `(GI.9)` also shows why an arbitrary detector need not receive the
prime-square gain automatically.  The range sine `S` is small in the Julia
row, but `H_W` must still be estimated on the source side.

## 4. Sequential endpoint

Order the visible primes and let `P_j` be the actual projection after the
first `j` inverse Euler factors.  For the `j`-th graph write `C_j,S_j` and
form `H_(W,j)` from the blocks of the same fixed detector relative to
`P_(j-1)`.

The projection telescope is an operator identity:

```text
P_n-P_0=sum_(j=1)^n (P_j-P_(j-1)).                  (GI.11)
```

Under the same trace-legality contract as `(GI.8)`,

```text
Tr[W(P_n-P_0)]
 =sum_(j=1)^n Re Tr[S_j* H_(W,j)].                   (GI.12)
```

Thus `(GI.12)` supplies the finite-trace algebraic shape requested by Proof
351 `(JB.20)`.  It does not yet supply its Schatten-class realization.  In
the route, `S_j` must be pulled back through the Julia prefix and paired only
after compact roots make both rows Hilbert--Schmidt.

## 5. Trace-anomaly guard

Finite matrices allow every cycle used in `(GI.8)`.  The route does not.
Proofs 259, 264, 297, and 340 show that finite-section cyclicity can move a
nonzero response to an artificial far boundary.

The legal infinite-dimensional order is therefore

```text
root-sandwich W(P_j-P_(j-1))
  -> prove each completed block product is trace class
  -> prove the required rectangular cycles
  -> identify the resulting H_(W,j)
  -> prove the weighted S2 row bound
  -> apply one final direct-sum Cauchy--Schwarz.       (GI.13)
```

It is forbidden to start from raw `Tr(WP_j)` and `Tr(WP_(j-1))`, or to
declare the cycles legal because `(GI.8)` holds in finite sections.

## 6. Finite certificate

The companion probe uses a common diagonal spectral representation.  Every
Euler translation and the self-adjoint detector commute exactly before a
random source subspace is chosen.  At each prime it checks:

```text
the direct inverse-Euler range projection;
the graph-frame projection;
the block identity `(GI.5)`;
the detector innovation identity `(GI.8)`;
the sequential projection telescope `(GI.11)`;
the final endpoint response `(GI.12)`.               (GI.14)
```

Run in WSL2 without a Lean build:

```text
OPENBLAS_NUM_THREADS=1 python3 -B \
  docs/proofs/353_graph_detector_innovation_probe.py
```

The probe is a certificate for finite algebra only.  It is not evidence for
the continuous trace-legality or weighted detector estimate.

## 7. Active analytic theorem

For the diagonal compact-root detector `W=C_g* C_g`, the remaining near
theorem is now concrete.  Construct root-split Hilbert--Schmidt realizations
`R_j` and `D_j` of the two sides of `(GI.8)` such that

```text
Tr[W(P_j-P_(j-1))]=Re <R_j,D_j>_S2,                 (GI.15)

sum_j (p_j-1) norm(R_j)_2^2
 <=norm(A_g)_2^2,                                    (GI.16)

sum_(log(p_j)<=L) norm(D_j)_2^2/(p_j-1)
 <=C_g L(1+L).                                       (GI.17)
```

Proofs 350--352 own the abstract range budget and final consumer.  Compact
support makes `(GI.17)` numerically plausible because a completed half-line
crossing at displacement `log(p)` has square cost proportional to `log(p)`.
What remains to prove is that the entire innovation `(GI.9)`, including its
intertwining defect, is a contractive image of the recombined physical
outer-minus-Sonin-plus-prolate crossing.  No branchwise trace-norm estimate is
allowed.
