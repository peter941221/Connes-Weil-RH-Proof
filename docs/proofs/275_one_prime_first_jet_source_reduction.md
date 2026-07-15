# Proof 275: One-prime first-jet source reduction

Date: 2026-07-15

Status: exact reduction of Proof 274's missing half-power at the one-prime
linear level.  The derivative of the orthogonal projection onto
`(I-aU_z) Ran(J)` is one completed boundary tangent.  For the nested band
`B=E-R`, its first jet is the outer tangent minus the Sonin tangent.  Compact
root support deletes the outer scalar response exactly once `z>2B_root`.

Consequently the desired dressed estimate `O(exp(-z))` is equivalent to an
`O(exp(-z/2))` off-diagonal bound for the complete Sonin/prolate tangent.  This
proof identifies that source theorem but does not prove it.  Proof 251's
finite sections support the decay and remain diagnostic only.  Mixed-prime
terms and the determinant-resummed renewal are not controlled.  Gate 3U and
RH remain open.

## 1. Result

```text
+------------------------------------------------+------------------------------+
| layer                                          | judgment                     |
+------------------------------------------------+------------------------------+
| orthogonal projection first-jet formula       | exact                        |
| nested E-R first jet                           | exact                        |
| outer compact-support scalar response          | zero for z>2B_root          |
| extra-half-power equivalence                   | exact                        |
| complete Sonin/prolate exp(-z/2) decay         | open source theorem          |
| one-prime finite-section decay                 | supporting diagnostic        |
| mixed-prime determinant resummation            | open                         |
| Gate 3U and RH                                 | unproved                     |
+------------------------------------------------+------------------------------+
```

The corrected flow is

```text
one Euler coefficient exp(-z/2)
  * complete nested first jet at displacement z
  -> outer scalar crossing vanishes by compact support
  -> Sonin/prolate tangent must contribute exp(-z/2)
  -> dressed scalar exp(-z)=p^(-m).                    (AL.1)
```

## 2. Exact projection first jet

Let `J` be an orthogonal projection, let `U` be bounded, and put

```text
T_a=I-aU,
J_a=orthogonal projection onto T_a Ran(J).             (AL.2)
```

The graph of `T_a Ran(J)` over `Ran(J)` is

```text
L_a=(I-J)T_aJ [J T_aJ]^(-1)
    =-a(I-J)UJ+O(a^2).                                (AL.3)
```

The first derivative of a graph projection at the zero graph is its two
off-diagonal blocks.  Therefore, with

```text
Z_J(U)=(I-J)UJ,
```

one has

```text
partial_a J_a at a=0
 =-Z_J(U)-Z_J(U)*.                                    (AL.4)
```

For nested projections `R<=E`, put `B=E-R` and transport both ranges by the
same `T_a`.  Subtraction gives

```text
partial_a B_a at a=0
 =-[Z_E(U)+Z_E(U)*]+[Z_R(U)+Z_R(U)*].                 (AL.5)
```

Equations `(AL.4)--(AL.5)` are operator identities.  The certificate checks
them against independent symmetric finite differences of QR-constructed
orthogonal projections.

## 3. The signed scalar first jet

Let `W=C_g*C_g` be the compact-root detector and let `U_z` be logarithmic
translation by `z>0`.  Fixed-`S` trace legality is supplied by Proof 261.
Define

```text
q_J(z;g)
 :=Tr(W partial_a J_a|_(a=0))
 =-2 Re Tr(W(I-J)U_zJ),                               (AL.6)

q_B(z;g)=q_E(z;g)-q_R(z;g).                          (AL.7)
```

For a prime mode `z=m log(p)`, Proof 222 and Proof 264 show that the local
signed scalar owns exactly one Euler coefficient

```text
a_p^m=exp(-z/2)=p^(-m/2).                             (AL.8)
```

Ignoring only the already recorded polynomial word and logarithmic weights,
the one-prime dressed first jet is

```text
Psi_(p,m)(g)=exp(-z/2) q_B(z;g).                      (AL.9)
```

Thus Proof 274's extra-half-power target

```text
|Psi_(p,m)(g)|
 <=C(1+z)^(2d)exp(-z)norm(g)_(H^r)^2                 (AL.10)
```

is equivalent to

```text
|q_B(z;g)|
 <=C(1+z)^(2d)exp(-z/2)norm(g)_(H^r)^2.              (AL.11)
```

This equivalence is coefficient bookkeeping, not an estimate.

## 4. Compact support deletes the outer scalar

If `supp(g) subset [-B_root,B_root]`, then the cross-correlation kernel of
`W` is supported in `[-2B_root,2B_root]`.  Proof 260 proves for every completed
half-line crossing

```text
Tr(K_(I,z,g))=|I|F_g(z).                              (AL.12)
```

Hence

```text
q_E(z;g)=0,  z>2B_root.                               (AL.13)
```

The exact orientation only exchanges `F_g(z)` and `F_g(-z)`; both vanish.
Combining `(AL.7)` and `(AL.13)` gives

```text
q_B(z;g)=-q_R(z;g),  z>2B_root.                       (AL.14)
```

This is a scalar cancellation after the completed crossing.  It does not
make the outer tangent's trace norm or `H1` norm vanish; Proof 273's guard
remains active.

## 5. Exact source term that remains

CC20 supplies

```text
R=E E_hat E-K_prol,
E_hat=mathcalS*(I-E)mathcalS.                         (AL.15)
```

The Euler translations commute with the scattering multiplier `mathcalS`.
The Leibniz rule therefore gives

```text
[R,U_z]
 =E E_hat[E,U_z]
  +E[E_hat,U_z]E
  +[E,U_z]E_hat E
  -[K_prol,U_z].                                      (AL.16)
```

Apply `(AL.16)` to both orientations in `(AL.6)`.  The missing continuous
theorem is the signed, root-smoothed estimate for their complete sum:

```text
|q_R(z;g)|
 <=C(1+z)^(2d)exp(-z/2)norm(g)_(H^r)^2,              (AL.17)
```

with constants independent of the visible finite prime set when this tangent
is inserted into Proof 273's renewal.  Estimating the three half-line words
and the prolate commutator separately is not justified: Proof 258 permits
arbitrarily large cancellation between the second-support and prolate-like
pieces.

Proof 228 supplies the required `exp(-z/2)` mechanism for an individual
logarithmic chirp.  What remains open is an exact source reduction of the
whole expression `(AL.16)` to those chirps with uniform amplitudes after the
renewal has been retained.

## 6. Why the one-prime theorem is not Gate 3U

Proof 251's mixed Hessian contains distinct-prime terms with dressed scale

```text
(p q)^(-1/2),                                         (AL.18)
```

not `(p q)^(-1)`, in the tested finite sections.  Therefore proving
`(AL.17)` for every individual translation does not authorize termwise
absolute summation of the nonlinear finite-S endpoint.

The route needs both layers:

```text
one-prime source decay (AL.17);

mixed connected terms kept inside the relative determinant / renewal
before the first absolute value.                                    (AL.19)
```

Proof 275 isolates the first layer.  Proof 273's paired renewal remains the
owner of the second.

## 7. Evidence and reproduction

Source evidence:

```text
CC20 Sonin/prolate identity and scattering conjugacy:
https://arxiv.org/abs/2006.13771

Proof 260 completed crossing trace and nuclear-norm guard:
docs/proofs/260_schatten_legality_signed_trace_gate.md

Proof 251 complete nested first-variation diagnostic:
docs/proofs/251_complete_nested_central_and_mixed_curvature.md
```

Run in WSL2:

```text
python3 -B docs/proofs/275_one_prime_first_jet_source_reduction_probe.py

python3 -B docs/proofs/275_one_prime_first_jet_source_reduction_probe.py \
  --size 768 --lengths 3,4,5,6,7,8
```

The exact layer checks `(AL.4)--(AL.5)` by finite differences and checks the
Euler coefficient identity in `(AL.8)--(AL.9)`.  The source-shaped layer
verifies that the outer Toeplitz read-off is zero after its displacement
clears the compact root window.  Its fitted decay is a finite periodic Sonin
diagnostic, not a proof of `(AL.17)`.

## 8. Route judgment

Proof 275 converts the coefficient gap into one explicit source estimate.  It
does not claim that Proof 228 alone proves `(AL.17)`, and it does not replace
the determinant-resummed mixed renewal by a sum of one-prime tangents.

Proof 276 proves the required half-power tail for CC20's static Sonin
correction.  Proof 277 then shows that the moving first jet is a Toeplitz
covariance, not that static coefficient alone.  The active Gate 3U bottom is
therefore:

```text
prove the complete Sonin Toeplitz covariance estimate (AN.13)
inside Proof 273's complete renewal;

retain all mixed connected channels until the scalar trace and compact-support
stopping have acted.                                           (AL.20)
```

The finite-S sign, arithmetic same-object trace identity, negative-owner
integration, Burnol's identity, and RH remain open.  No Lean owner or route
rewire is authorized.
