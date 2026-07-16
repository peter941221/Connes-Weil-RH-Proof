# Proof 303: Quantized divided-difference bridge for the moving E/R/K_prol owner

Date: 2026-07-16

Status: the finite source-shaped bridge is now exact.  A Hardy commutator
reads back the projection covariance at every moving time, and the identity
`R = E Q E - K_prol` expands the `R` commutator into the outer,
second-support, and prolate branches.  The three branches recombine before
the pairing is estimated.  The CC20 `-2 Dirac_0` term remains a separate
distributional scalar: the ordinary divided-difference matrix does not
recover it, and no automatic cancellation was found.

This does not prove the continuous source identification, the uniform
compact-root estimate, Gate 3U, the finite-`S` sign, the arithmetic
same-object identity, Burnol's all-zero identity, or RH.

## 1. Result

```text
+------------------------------------------------+------------------------------+
| layer                                          | judgment                     |
+------------------------------------------------+------------------------------+
| CC20 off-diagonal divided difference           | exact source formula         |
| Hardy covariance readback                      | exact in finite dimension    |
| moving E/R covariance readback                 | exact at every time          |
| R = E Q E - K_prol commutator expansion        | exact                        |
| outer + second-support + prolate recombination | required before pairing      |
| prolate omission                               | rejected by finite guard     |
| ordinary kernel recovering -2 Dirac_0          | false                        |
| automatic residue cancellation                 | rejected                     |
| continuous root-sandwiched source bridge       | open                         |
| compact-support signed estimate                | open                         |
| Gate 3U and RH                                 | unproved                     |
+------------------------------------------------+------------------------------+
```

The new ownership chain is

```text
CC20 [H,f] divided difference
  -> finite Hardy covariance identity
  -> moving E/R identity at each alpha
  -> E Q E - K_prol branch ledger
  -> one signed root-paired scalar                 (BN.1)
```

The chain is an algebraic bridge.  It does not turn a finite matrix into the
continuous CC20 operator, and it does not provide the missing estimate.

## 2. Source formula and the finite Hardy identity

CC20 Appendix D defines the quantized differential (quantized calculus)

```text
H = 2 F 1_[0,infinity) F^(-1) - 1,
[H,f] = H f - f H.                                  (BN.2)
```

For a Schwartz multiplier, Appendix E gives the kernel normalization

```text
([H,f])(s,t)
  = i/pi * (f(s)-f(t))/(s-t),                         (BN.3)
```

The diagonal value is the removable limit `f'(s)`.  The source statements are
CC20, Appendix D equations (156)--(157) and Appendix E equation (161), in

```text
https://arxiv.org/abs/2006.13771
```

For a finite orthogonal projection `J`, put

```text
H_J = 2 J - I,
C_J(f) = [H_J, M_f],                                 (BN.4)
```

where `M_f` is the diagonal multiplier.  For real diagonal `f,g`, direct
block multiplication gives

```text
S_J(f,g)
 := Tr(J M_f (I-J) M_g J)
  = 1/8 Tr(C_J(f)^* C_J(g)).                           (BN.5)
```

The factor `1/8` is important.  Since

```text
[H_J,M_f] = 2(J M_f (I-J) - (I-J) M_f J),
```

the two off-diagonal blocks contribute the same trace for commuting real
diagonal multipliers.  No cyclic permutation of a non-trace-class infinite
operator is used in the finite certificate.

Equation `(BN.5)` is the finite shadow of the source quantized-calculus
readback.  Complex cross roots are recovered only after a diagonal estimate by
polarization; the probe deliberately keeps `f` and `g` real at this stage.

## 3. The complete moving E/R bridge

Use the finite source-shaped model from Proof 266.  Its projections satisfy

```text
R <= E,
R <= Q,
E Q E = R + K_prol.                                  (BN.6)
```

For any diagonal multiplier `f`, expand the commutator before taking a
pairing:

```text
[R,M_f]
 = E Q [E,M_f]
   + E [Q,M_f] E
   + [E,M_f] Q E
   - [K_prol,M_f].                                   (BN.7)
```

The four displayed terms have the following source interpretation:

```text
outer crossing          E Q [E,M_f] + [E,M_f] Q E
second-support crossing E [Q,M_f] E
prolate correction      -[K_prol,M_f].               (BN.8)
```

The `R` Hardy commutator is twice the sum in `(BN.7)`.  Therefore the signed
covariance is

```text
S_E(f,g) - S_R(f,g)
 = 1/8 Tr(C_E(f)^* C_E(g))
   -1/8 Tr(C_R(f)^* C_R(g)),                          (BN.9)
```

with the complete branch sum substituted for each `C_R`.  Expanding the two
products branch by branch is not a norm estimate: all cross terms remain in
the same scalar.  Dropping the prolate term changes the scalar in both probe
cohorts.

Now let `U_alpha = exp(i alpha G)` be a finite unitary transport and define

```text
E_alpha = U_alpha E U_alpha^*,
R_alpha = U_alpha R U_alpha^*,
Q_alpha = U_alpha Q U_alpha^*,
K_alpha = U_alpha K_prol U_alpha^*.                   (BN.10)
```

Conjugating `(BN.6)--(BN.9)` proves the same identity pointwise in `alpha`.
The time integral is consequently a readback of the same moving owner, not a
static Euler-product telescope:

```text
integral_0^1 (S_(E_alpha)-S_(R_alpha)) d alpha
 = integral_0^1 (complete three-branch divided-difference pairing) d alpha.
                                                               (BN.11)
```

## 4. Compact roots enter before mode splitting

The probe builds a root `eta` supported on `[-B,B]` on a non-wrapping cyclic
carrier.  Its multiplier and correlation are

```text
w(k) = |eta_hat(k)|^2,
F_eta(u) = sum_n conjugate(eta(n)) eta(n+u),
w(k) = N^(-1) sum_u F_eta(u) exp(-i u theta_k).       (BN.12)
```

The support check is exact in the finite model:

```text
supp(F_eta) subset [-2B,2B].                          (BN.13)
```

The covariance is evaluated with this complete multiplier before any prime or
branch disintegration.  This preserves Proof 301's support-first order:

```text
root correlation
  -> moving signed E/R pairing
  -> divided-difference branch expansion
  -> only then a possible source estimate.             (BN.14)
```

## 5. The residue ledger

CC20's logarithmic endpoint has the distributional split

```text
Q_+ delta(exp(|x|)) = -2 Dirac_0 + q_reg.             (BN.15)
```

This is the derivative jump at `rho=1` discussed after CC20 formula (11).
The `-2 Dirac_0` term is not the removable diagonal value in `(BN.3)`.  A
finite divided-difference matrix has no diagonal measure, so it records only
the regular two-point kernel.

The probe makes this separation explicit.  For the source-shaped test pair,
`f(0)=1` and `g(0)=0.15`, so the isolated residue is `-0.30`, while the
ordinary divided-difference diagonal mass is zero.  A constant-mode guard also
has `[H,1]=0` but a formal residue magnitude `2`; this is a warning about
ownership, not a legal compact-support test.

For the actual compact root pair there is a stronger same-object identity:

```text
F_(eta,xi)(0)=<eta,xi>,
-2 <Dirac_0,F_(eta,xi)>=-2 <eta,xi>.                 (BN.16)
```

Thus the Dirac atom pulls back to CC20's literal `-2 Id` form on the root
Hilbert space.  It is neither a fourth crossing branch nor a value inserted on
the diagonal of `(BN.3)`.  Both probe cohorts verify `(BN.16)` exactly.

The conclusion is deliberately negative:

```text
ordinary divided difference alone = regular kernel;
ordinary divided difference + hidden diagonal = not justified;
-2 Dirac_0 must be paired as the explicit -2 Id form. (BN.17)
```

In particular, the finite `E/R/K_prol` identity does not prove that the Dirac
term cancels.  The source route must supply the same-test diagonal form and its
compatibility with the prolate correction before any contour or Sobolev bound.

## 6. Finite certificate

`303_quantized_moving_er_kprol_bridge_probe.py` checks:

```text
CC20 off-diagonal divided-difference kernel and double pairing;
removable diagonal finite difference and constant commutator;
root multiplier reconstruction and compact correlation support;
moving E/R covariance readback at every sampled alpha;
R commutator expansion into outer/second/prolate branches;
integrated complete-branch readback;
nonzero error after deleting K_prol;
same-root Dirac-to-identity-form alignment;
separate -2 Dirac residue ledger.                     (BN.18)
```

Run in WSL2:

```text
OPENBLAS_NUM_THREADS=1 python3 -B \
  docs/proofs/303_quantized_moving_er_kprol_bridge_probe.py

OPENBLAS_NUM_THREADS=1 python3 -B \
  docs/proofs/303_quantized_moving_er_kprol_bridge_probe.py \
  --multiplicity 12 --support-radius 3 --seed 1303 \
  --flow-samples 13 --source-size 44
```

The two cohorts report:

```text
+-----------------------------------------------+-------------+-------------+
| diagnostic                                    | default     | alternate   |
+-----------------------------------------------+-------------+-------------+
| source first divided-difference error         | 2.66e-16    | 2.93e-16    |
| source second divided-difference error        | 1.66e-16    | 1.53e-16    |
| source double-pairing error                   | 1.78e-15    | 8.88e-16    |
| nested projection identity error              | 1.20e-15    | 1.15e-15    |
| same-root Dirac identity-form error           | 0           | 0           |
| maximum moving covariance readback error      | 3.50e-17    | 4.86e-17    |
| maximum moving branch expansion error         | 1.19e-15    | 7.08e-16    |
| integrated covariance readback error          | 3.57e-18    | 1.93e-17    |
| integrated complete branch error              | 7.63e-17    | 1.92e-16    |
| minimum prolate omission gap                  | 1.83e-04    | 1.49e-03    |
| maximum prolate omission gap                  | 9.39e-04    | 1.63e-03    |
| integrated prolate omission gap               | 6.34e-04    | 1.55e-03    |
| source Dirac residue                          | -3.00e-01   | -3.00e-01   |
| ordinary diagonal mass                        | 0           | 0           |
+-----------------------------------------------+-------------+-------------+
```

The exact errors are machine precision.  The omission gaps are not error
bars; they are rejection guards showing that `K_prol` is an active signed
branch.  The residue gap is a source-ownership guard, not a lower bound for a
continuous operator.

## 7. Route judgment

```text
CC20 off-diagonal divided difference:       retained;
finite moving Hardy bridge:                 closed;
outer/second/prolate recombination:         mandatory;
prolate-only deletion:                      rejected;
automatic Dirac cancellation:              rejected;
continuous H-to-source moving identification: open;
compact-root signed estimate:               open;
Gate 3U and RH:                             open / unproved. (BN.19)
```

The primary source is Connes--Consani, *Weil positivity and Trace formula, the
archimedean place*, arXiv:2006.13771:

```text
https://arxiv.org/abs/2006.13771
```

The local source bridges are
`docs/proofs/160_cc20_source_kernel_haar_bridge.md`,
`docs/proofs/171_cc20_qdelta_branch_derivative_reduction.md`, and
`docs/proofs/302_quantized_divided_difference_residue_guard.md`.

Proof 303 itself did not change a route consumer.  Proof 304 now supplies the
missing ordinary CC20 residue owner and its global zero-extension carrier:
`docs/proofs/304_cc20_quantized_remainder_owner.md`.

## 8. Next hard point: the continuous Proof 305 bridge

Proof 304 closes the diagonal-residue and same-carrier bookkeeping for the
ordinary owner `K_I - 2 Id` / `K_window - 2 P_window`.  The remaining
continuous theorem is:

```text
1. construct the root-sandwiched continuous [H,f] kernel on the CC20 Haar
   carrier and prove trace-class membership;
2. identify its outer branch with the moving E_alpha divided difference;
3. keep the source form as the ordered pair

     (regular divided-difference pairing, -2 <eta,xi>),

   rather than hiding the atom in a continuous kernel;
4. match that complete pair to the second-support and K_prol branches;
5. only after that identity, prove the compact-support signed estimate. (BN.20)
```

The forbidden shortcuts remain the global post-`Q` strip, a raw translated
projection trace, a branchwise absolute value, and deletion of the prolate or
Dirac terms.  Gate 3U, the finite-`S` sign, the arithmetic same-object
identity, Burnol's identity, and RH remain open.
