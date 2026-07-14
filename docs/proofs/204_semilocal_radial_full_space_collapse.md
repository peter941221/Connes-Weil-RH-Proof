# Proof 204: Semilocal radial full-space collapse

Date: 2026-07-13

## Result

Passing from the invariant space `L2(X_S)^K_S` to the full semilocal space
`L2(X_S)` does not create new input or output channels for the existing
radial Riemann-zeta test.

Let

```text
H   = L2(X_S),
K   = K_S = ker(Mod_S),
E_K = integral_(k in K) U(k) dk,
A_g = U(g) = integral_(c in C_S) g(c) U(c) d*c,
g(c) = g_0(Mod_S(c)).
```

Here `dk` is normalized Haar measure on the compact group `K`. Then

```text
E_K A_g = A_g = A_g E_K.                                (R.1)
```

Consequently, for every bounded operator `B` on `H`,

```text
A_g* B A_g = A_g* E_K B E_K A_g.                        (R.2)
```

Thus a bounded positive sandwich for a radial test sees only the
`K_S`-invariant compression `E_K B E_K`. Merely placing the same construction
on full `L2(X_S)` cannot use nontrivial `K_S` input or output blocks to cancel
the one-prime defect.

## Route obligation

```text
route obligation:
  produce a genuine finite-S positive owner whose exact single-crossing
  term is the selected finite-prime operator and whose same-domain post-Q
  remainder has the required sign

old weak path:
  move the radial positive sandwich from L2(X_S)^K_S to full L2(X_S) and
  appeal to additional compact-group channels

new mathematical owner:
  none; (R.2) is a no-go theorem for that carrier enlargement

consumer to rewire:
  Plan 032 Gate 3 route judgment

forbidden circular inputs:
  a stored semilocal Weil read-off, a stored remainder sign, either RH-level
  route root, or an unnamed equality between full-space and invariant traces

smallest verification target:
  Haar-averaging algebra (R.1)--(R.2) plus the cited source definitions

focused axiom audit:
  not applicable; no Lean declaration is introduced
```

## Proof

The module is a group homomorphism and `K=ker(Mod_S)`. Hence for `k in K`,

```text
Mod_S(k^(-1)c) = Mod_S(c),
Mod_S(ck^(-1)) = Mod_S(c).
```

The radial function is therefore invariant under left and right translation
by `K`:

```text
g(k^(-1)c) = g(c) = g(ck^(-1)).                          (R.3)
```

Using Haar invariance in the integrated representation gives

```text
U(k) A_g
  = integral_C_S g(c) U(kc) d*c
  = integral_C_S g(k^(-1)c') U(c') d*c'
  = A_g,

A_g U(k)
  = integral_C_S g(c) U(ck) d*c
  = integral_C_S g(c'k^(-1)) U(c') d*c'
  = A_g.                                                  (R.4)
```

Averaging (R.4) over `K` proves (R.1). The normalized compact-group average
`E_K` is self-adjoint by invariance under `k -> k^(-1)` and idempotent by a
second Haar change of variables, so it is the orthogonal projection onto
`H^K`.

Now `A_g=E_K A_g` implies `A_g*=A_g* E_K`, while `A_g=A_g E_K` gives the
right insertion. Therefore

```text
A_g* B A_g
  = A_g* E_K B E_K A_g,
```

which is (R.2). In block form the mechanism is visible without trace
manipulation:

```text
H = H^K (+) (H^K)^perp

        [ A_0   0 ]          [ B_00  B_01 ]
A_g  = [         ],     B  = [             ],
        [  0    0 ]          [ B_10  B_11 ]

              [ A_0* B_00 A_0   0 ]
A_g* B A_g = [                    ].
              [       0           0 ]
```

The off-diagonal and nontrivial-isotypic blocks do not enter the radial
sandwich. If `B` is positive, then `E_K B E_K` is positive on `H^K`, so the
compression does not lose positivity.

## Primary-source evidence

```text
+-------------+------------------------------+------------------------------+
| source      | TeX lines                    | fact used                    |
+-------------+------------------------------+------------------------------+
| Connes 1999 | zeta.tex:1740-1808           | C_S, X_S, L2(X_S), U(h)      |
| Connes 1999 | zeta.tex:1870-1909           | full-space cutoff trace      |
| CCM24 v2    | mainc2m24fine.tex:237-245    | K_S maximal compact          |
| CCM24 v2    | mainc2m24fine.tex:730-741    | unitary L2 identification    |
| CCM24 v2    | mainc2m24fine.tex:761-804    | zeta cyclic pair in H^K      |
| CCM24 v2    | mainc2m24fine.tex:934-1029   | Sonin space in H^K           |
| CC20        | weil-compo.tex:111-114       | finite-S positivity open     |
| CC20        | weil-compo.tex:488-559       | positive compression and     |
|             |                              | explicit remainder           |
| CC20        | weil-compo.tex:765-808       | archimedean -2 Id + K_I      |
+-------------+------------------------------+------------------------------+
```

Primary sources:

```text
Alain Connes, Trace Formula in Noncommutative Geometry and the Zeros of the
Riemann Zeta Function, arXiv:math/9811068.
https://arxiv.org/abs/math/9811068

Alain Connes and Caterina Consani,
Weil Positivity and Trace Formula, the Archimedean Place, 2020.
https://arxiv.org/abs/2006.13771

Alain Connes, Caterina Consani, and Henri Moscovici,
Zeta Zeros and Prolate Wave Operators: Semilocal Adelic Operators, v2.
https://arxiv.org/abs/2310.18423
```

Connes's 1999 `R_Lambda=P_hat_Lambda P_Lambda` theorem is an asymptotic trace
formula with an `o(1)` term; it is not itself a positive owner. CC20 obtains
positivity from the three-projection compression and proves the explicit
archimedean remainder. CCM24 then places both the zeta cyclic pair and the
semilocal Sonin space inside `L2(X_S)^K_S`; it does not prove the missing
finite-S positive trace identity.

## One-prime consequence

For `S={infinity,2}`, CCM24's invariant coordinate contains the multiplier

```text
1 - 2^(-1/2-is)
```

(`mainc2m24fine.tex:950-981`). A full-space lift of the same radial sandwich
has exactly the invariant compression in (R.2), so the lift does not alter
that scalar scattering channel.

For the direct cocycle owner, proof 026 computes the resulting pure
finite-place distribution. Its central coefficient is

```text
d_0 = 2^(-1) log(2) > 0,
```

and post-composition with `Q=-partial^2+1/4` leaves a nonzero
`-d_0 Dirac_0''` principal part. The corresponding fixed-support modulated
quadratic forms grow quadratically, so that direct invariant compression is
not a bounded `-c Id + compact` remainder. Equation (R.2) shows that moving
this same owner to full `L2(X_S)` does not repair it.

The same-range positive-weight family remains separately rejected by proof
124: exact archimedean bulk forces the endpoint metric projection, whose
`p^2` coefficient has the factor-two error proved in proof 042.

## Scope

This theorem does **not** prove that every possible bounded operator `B` has a
bad invariant compression. A full-space construction with genuinely new
internal geometry could produce a new block `B_00=E_K B E_K`. Such a proposal
must state that block explicitly and prove its exact same-object finite-S
trace identity and remainder sign. Calling it a full-space or angular effect
is not evidence.

The radial hypothesis is essential. Integrating `g_0` only along a chosen
section of `C_S -> C_S/K_S` need not satisfy (R.1); it defines a different
test operator, not another realization of `g(c)=g_0(Mod_S(c))`. Its
nontrivial `K_S` character channels cannot be identified with the existing
Riemann-zeta `finitePrimeTerm` without a new semilocal trace formula.

It also does not reject an unbounded or relative positive quadratic form; that
case needs a common form domain before the Haar insertions and trace pairing
are legal.

## Verdict

```text
radial full-space carrier enlargement: not a new owner
nontrivial K_S input/output blocks in a bounded sandwich: invisible
full-space lift of the direct cocycle owner: rejected by proof 026
same transported Sonin range: rejected by proofs 124 and 042
genuinely new invariant compression E_K B E_K: not produced, still open
nonradial or section-supported test: different arithmetic owner, not covered
unbounded/relative positive form: not covered, still open
Lean owner: forbidden
RH: unproved
```
