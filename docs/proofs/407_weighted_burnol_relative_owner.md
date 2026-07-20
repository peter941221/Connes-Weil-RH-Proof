# Proof 407: weighted Burnol relative owner

Date: 2026-07-19

Status: exact weighted compression owner at the form level, with a finite
certificate.  The standard unweighted multiplier intertwinement is rejected as
a consequence of Burnol's isometry.  The continuous root-relative estimate,
Gate 3U, the finite-S sign, Burnol's identity, and RH remain open.

## 1. Result

```text
+--------------------------------------------------+--------------------------+
| layer                                            | judgment                 |
+--------------------------------------------------+--------------------------+
| source range `M_0=g_0 K_Theta`                   | Proof 375 owner          |
| isometric source multiplier                     | exact on `K_Theta`       |
| actual compressed multiplier form               | weighted by `h=|g_0|^2`  |
| raw unweighted `RL.7` inference                 | rejected                 |
| finite weighted projection readback             | exact                    |
| fixed-quotient first-jet match                 | target, not yet source   |
| continuous root-relative estimate               | open                     |
| Gate 3U / RH                                     | open / unproved          |
+--------------------------------------------------+--------------------------+
```

The correction is:

```text
M_0 = g_0 K_Theta,
h   = |g_0|^2,

U_g^* P_(M_0) M_a P_(M_0) U_g
  = A_Theta(a h),
```

where `U_g f=g_0 f` and `A_Theta(phi)` is the truncated Toeplitz form on
`K_Theta`.  Burnol's isometry gives only

```text
A_Theta(h)=I.
```

It does not give `A_Theta(a h)=A_Theta(a)` for a detector or Euler symbol.

## 2. Why the weight is mandatory

For `f,k in K_Theta`, the source form is

```text
<a g_0 f, g_0 k> = integral a h f conjugate(k),
```

so the transported compression is the weighted form `A_Theta(a h)`.  The
fact that `g_0` is isometric says that the same expression with `a=1` equals
`<f,k>`; it does not remove `h` after another multiplier is inserted.

The failure is already exact in a one-dimensional model.  Take

```text
Theta(z)=z,
K_Theta=span{1},
g(z)=(1+r z)/sqrt(1+r^2),
h=|g|^2,
w(z)=z+conjugate(z),
```

with `0<r<1`.  On the boundary,

```text
A_Theta(h)=1,
A_Theta(w)=0,
A_Theta(w h)=2r/(1+r^2) != 0.
```

Thus an isometric multiplier preserves the source norm but not the raw
detector compression.  The finite probe also checks the transported
projection trace, not just these scalar forms.

## 3. Correct relative determinant owner

Let `tau_S` be the complete causal Euler multiplier and let `w_g` be the
compact-root detector symbol.  At a finite model level define

```text
Psi_S(s)
  = log det A_Theta(h |tau_S|^2 exp(s w_g))
  - log det A_Theta(h |tau_S|^2)
  - log det A_Theta(h exp(s w_g))
  + log det A_Theta(h).
```

In the actual infinite-dimensional route this notation means the completed
relative Fredholm determinant from Proofs 261 and 341; the four bare
determinants must not be formed independently.

The finite projection formula is

```text
Psi_S'(0)
 = Tr[W_g(P_(tau_S M_0)-P_(M_0))].
```

Since the route band is `B_S=E-R_S`, its Gate response has the fixed sign

```text
Tr[W_g(B_S-B_0)] = -Psi_S'(0).
```

This is the weighted version of the Proof 405 semicommutator.  The next
source theorem must identify its derivative with the complete two-branch
corner

```text
2 Re Tr[P [W_E,R] R X P],
```

and retain both the reflected second-support commutator and the prolate-root
leg before any absolute value.

## 4. Single Gate 3U target

The decisive new theorem is the root-relative weighted gradient bound

```text
sup_(finite S)
  |Psi_S'(0)|
  <= C_lambda (1+B_root)^d ||g||_(H^r)^2.             (WB.1)
```

The proof order is fixed:

```text
actual Burnol weighted form
  -> completed relative determinant
  -> far/near split after root completion
  -> Proof 336 far tail
  -> near signed two-branch gradient
  -> one final absolute value.                        (WB.2)
```

Do not replace `(WB.1)` by a norm of `h`, a raw Euler `H^(1/2)` norm, a
primewise trace-norm sum, or the unweighted model formula.  The continuous
prime-log symbols have atomic frequencies, so the finite BOGC gradient from
Proof 346 cannot be applied without a root-relative limiting theorem.

## 5. Evidence and boundaries

Proof 375 gives the actual nearly invariant source carrier
`M_0=g_0 K_Theta` and the causal Euler range transport.  Proof 405 gives the
fixed-quotient first jet and its exact two-branch collapse.  Proof 336 closes
the fixed-source far lane, but explicitly leaves the near complete-product
estimate open.

Primary source for the Sonin/de Branges identification:

```text
J.-F. Burnol,
Sur les espaces de Sonine associes par de Branges a la transformation de Fourier,
Theorem 8,
https://arxiv.org/abs/math/0208121
```

Current status:

```text
weighted finite owner                 exact;
raw unweighted intertwinement         rejected as an inference;
continuous weighted gradient (WB.1)   open;
Gate 3U                               open;
finite-S sign / Burnol / RH           open / open / unproved.
```

## 6. Reproducible certificate

Run without a Lean build:

```text
OPENBLAS_NUM_THREADS=1 python3 -B \
  docs/proofs/407_weighted_burnol_relative_owner_probe.py
```

The probe checks the weighted projection formula, the direct projection trace,
the transported relative response, and the failure of the raw unweighted
compression identity.  The algebra checks are at machine precision; the
reported relative-log-determinant derivative uses a symmetric finite
difference with tolerance `5e-10`.
