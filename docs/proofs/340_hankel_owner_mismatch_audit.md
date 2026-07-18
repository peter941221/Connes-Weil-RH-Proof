# Proof 340: Hankel-owner mismatch audit

Date: 2026-07-18

Status: rejection of Proof 339's proposed same-object Gate 3U interface.  The
operator-valued Peller theorem and the missing-channel completely positive
contraction remain valid local tools.  The unweighted emission corner they
control is not the complete weighted Gate response.

Gate 3U, the finite-S sign, Burnol's identity, and RH remain open.

## 1. Result

```text
+------------------------------------------------+--------------------------+
| object                                         | judgment                 |
+------------------------------------------------+--------------------------+
| right-path projection emission corner         | Hankel                   |
| emission detector commutator corner            | Hankel                   |
| actual weighted off-range owner                | not Hankel               |
| canonical response                             | nonzero / mandatory      |
| path-boundary strip                            | nonzero / mandatory      |
| infinite trace anomaly                         | nonzero in exact guard   |
| Peller theorem for emission corner             | valid local lemma        |
| Proof 339 same-object Gate implication         | rejected                 |
| corrected full owner                           | relative heat/moving band|
| Gate 3U / RH                                   | open / unproved          |
+------------------------------------------------+--------------------------+
```

The ownership correction is

```text
emission Hankel corner
  -X-> not the full Gate scalar;

canonical + weighted off-range + path boundary
  -> ordered relative heat cocycle
  -> complete moving-band integral
  -> source-relative BOGC or direct signed bound.   (BX.1)
```

## 2. What is genuinely Hankel

Proof 294 proves, for emission indices,

```text
P_(j,k)=K Delta^(j+k)H_nK*,                         (BX.2)

[O_n^E,P_n]_(j,k)
 =W_E P_(j,k)-P_(j,k)W_E.                           (BX.3)
```

Both blocks depend only on `j+k`.  Peller/de la Salle may therefore be used
to estimate the trace ideal of this unweighted emission corner, provided its
`S_1`-valued symbol is constructed.

Proof 339's Peller citation is correct at this local level:

```text
Mikael de la Salle,
Operator space valued Hankel matrices,
Theorem 0.1, p=1,
https://arxiv.org/abs/0909.5151
```

## 3. The actual owner has separate row and column weights

Proof 296 gives the complete off-range operator

```text
T_n^off
 =sum_(a,b) Z_a* C_(a,b)R_b,                        (BX.4)

C_(a,b)=[O_n^E,P_n]_(a,b).                          (BX.5)
```

Although `C_(a,b)` depends on `a+b`, the surrounding factors do not:

```text
Z_a=K(I-f_(N,a)(Delta)),
R_b=K Delta^b                                      (BX.6)
```

on emission slots, with different formulas on the survivor slot.  Therefore

```text
Z_(a+1)* C_(a+1,b)R_b
 !=Z_a* C_(a,b+1)R_(b+1)                            (BX.7)
```

in general.  The weighted contribution is not a block Hankel matrix even
though its middle block is.

Proof 296's exact reflection does not repair this.  It produces four parity
sectors.  The all-even sector has only one fixed-mode zero, and Proof 298
shows that every sector has a nonzero reciprocal-gap heat profile.  Thus no
horizon-uniform `B^1_1` estimate follows by attaching the weights after the
Peller bound.

## 4. Two missing parts outside the emission corner

Proof 290's exact response is

```text
sum_(k=0)^n N_W Delta^k
 =F_n*E_n+L_n*(I-P_n)E_n.                            (BX.8)
```

The first canonical term is not part of the path-projection commutator.
Inside the second term, every pair with row or column in `{0,tail}` is the
path-boundary strip.  Proof 295 shows that those blocks require carrier-change
corrections; Proof 296 shows that their scalar magnitude is order one.

Proof 297 adds the decisive infinite-dimensional guard: a route-shaped
weighted commutator can be trace class and still have trace `-i/16`.  Finite
sections cancel it against an artificial far boundary.  Consequently neither
finite Hankel truncation nor trace cyclicity may delete the missing boundary.

The hard package remains

```text
canonical response
  +all-even weighted sector
  +path-boundary anomaly.                            (BX.9)
```

## 5. The completely positive contraction does not fix ownership

Proof 271's row identity is valid:

```text
mathcalM*mathcalM=Delta<=I.                          (BX.10)
```

Therefore the diagonal output map

```text
X ->Diag(M_rand X M_rand*,M_C X M_C*)               (BX.11)
```

is contractive on `S_1`, and it is contractive coefficientwise on any
`B^1_1(S_1)` symbol to which the same map applies.

The actual Proof 286/289 coefficients, however, contain renewal-level and
predictable-future factors.  Proof 289 telescopes their **scalar traces** only
after the common reward and future product are aligned.  No theorem identifies
that scalar telescope with coefficientwise application of `(BX.11)` to Proof
339's emission symbol.  The CP lemma remains useful but does not supply the
missing same-object equality.

## 6. De Branges kernel domination is also insufficient

Proof 337 proves the positive-kernel order

```text
K_Delta<=K_Hardy.                                    (BX.12)
```

This gives a contractive inclusion of reproducing-kernel spaces.  It does not
by itself prove that an arbitrary trace-class Hankel functional, its weighted
boundary correction, or the ordered trace anomaly has no larger trace norm
after restriction.  That multiplier/intertwining statement would require a
separate theorem.

CCM24's de Branges realization does not provide a shortcut.  Its Section 4.8
proves that the same set `B_lambda` receives different de Branges norms from

```text
L2(R, ds/|E_S(s)|^2),
E_S(s)=product_(v in S)L_v(1/2+is).                  (BX.13)
```

It does not identify `E_S` as the Hermite--Biehler generator of the new norm,
nor give the new reproducing kernel or a relative trace formula.  Therefore
one may not replace the Gram-corrected projection response by the derivative
of the explicit Euler-factor phase.

Primary source:

```text
Connes--Consani--Moscovici,
Zeta zeros and prolate wave operators,
Section 4.8, arXiv:2310.18423v2.
https://arxiv.org/abs/2310.18423
```

## 7. Finite certificate

The companion probe checks the exact distinction.  In the default cohort:

```text
projection Hankel error             3.36e-17,
commutator Hankel error             3.91e-17,
weighted-owner Hankel mismatch      1.69e-3,
canonical response norm             4.46e-2,
path-boundary norm                  3.19e-2,
full response norm                  4.52e-2,
boundary/off-range ratio            0.7824.           (BX.14)
```

The alternate cohort gives weighted mismatch `1.56e-3` and boundary/off-range
ratio `0.7712`, with both unweighted Hankel errors below `4.3e-17`.

Run without a Lean build:

```text
OPENBLAS_NUM_THREADS=1 python3 -B \
  docs/proofs/340_hankel_owner_mismatch_probe.py

OPENBLAS_NUM_THREADS=1 python3 -B \
  docs/proofs/340_hankel_owner_mismatch_probe.py \
  --multiplicity 12 --seed 2340 --horizon 14
```

These are finite algebra guards.  The continuous rejection comes from the
separate-index formulas `(BX.4)--(BX.7)` and Proof 297's exact unilateral-shift
anomaly.

## 8. Corrected successor

The full finite path has already been resummed without loss by Proof 298:

```text
Q_S(W)
 =integral_0^infinity
   Tr_B(g_W* K exp(-t Gamma))dt.                     (BX.15)
```

Equivalently, Proof 282 gives the same endpoint as the complete moving-band
integral

```text
2 integral_0^1 [
 Tr(B_alpha W C_alpha H_alpha B_alpha)
-Tr(R_alpha W B_alpha H_alpha R_alpha)
]dalpha.                                            (BX.16)
```

These formulas retain the canonical term, all parity sectors, and boundary
anomaly as one scalar.  A Hankel/BOGC successor is legal only after proving
that its Fredholm determinant derivative equals `(BX.15)` or `(BX.16)`.

The recommended source coordinate is Proof 280's relative detector-first
Toeplitz semicommutator, together with Proof 278's Burnol boundary Gram.  Its
required derivative must reproduce the complete outer/second-support/prolate
ledger before any trace norm.

## 9. Route judgment

```text
operator-valued Peller theorem:              valid;
emission Hankel corner:                      exact;
complete weighted owner is Hankel:           false;
Proof 339 Gate implication:                  rejected;
ordered relative heat / moving-band owner:   exact;
uniform source-relative determinant bound:   open;
Gate 3U:                                     open;
finite-S sign / Burnol identity / RH:         open.      (BX.17)
```
