# Proof 292: Causal two-boundary generator

Date: 2026-07-16

Status: exact causal collapse of Proof 291's returned-outer branch.  The
result is an algebraic reduction only.  It does not prove the stopped-path
bound, Gate 3U, the finite-`S` sign, the arithmetic same-object identity,
Burnol's identity, or RH.

## 1. Result

Proof 291 retained the exact source expansion

```text
d_W
 =[W,E] A iota_B
  +E A C[W,E]iota_B
  -E A R[W,R]iota_B.                         (BC.1)
```

Proof 256 supplies the causal invariance identities

```text
E A C=0,
C A* E=0.                                    (BC.2)
```

Therefore the middle term in `(BC.1)` is identically zero, not merely small:

```text
d_W
 =[W,E] A iota_B
  -E A R[W,R]iota_B.                          (BC.3)
```

The active owner is now a signed pair of completed physical boundaries:

```text
+----------------------+-----------------------------------------------+
| boundary              | exact source factor                           |
+----------------------+-----------------------------------------------+
| outer half-line       | [W,E] A iota_B                                |
| Sonin / second support | -E A R[W,R] iota_B                             |
| returned outer branch  | E A C[W,E] iota_B = 0                          |
+----------------------+-----------------------------------------------+
```

The cancellation is structural.  It comes from one-sided invariance of the
causal inverse, not from a norm estimate or from a finite-dimensional
approximation.

## 2. Source objects and orientation

Use the Proof 290 notation.  `E` is the outer half-line projection, `C=I-E`
is the opposite half-line projection, `R<=E` is the Sonin projection, and
`B=E-R` is the crossing band.  Let `iota_B` be the inclusion of the band
space, so

```text
iota_B iota_B* = B,
iota_B* iota_B = I_B.
```

For a finite prime set `S`, let `A=T_S^(-1)` be the normalized causal Euler
inverse.  Let `W` be a compact-root convolution detector and

```text
K=E A iota_B,
W_B=iota_B* W iota_B,
d_W=WK-KW_B,
d_W^left=K*W-W_BK*.                           (BC.4)
```

The source route requires the whole-line convolution commutation

```text
[A,W]=0,
[A*,W]=0,
```

while `A` need not commute with `E`, `R`, or `B`.  This distinction is why the
boundary commutators must remain visible.

## 3. Causal collapse

Start from `(BC.4)` and insert `K=E A iota_B`:

```text
d_W
 =W E A iota_B-E A iota_B W_B
 =[W,E]A iota_B+E A(I-B)W iota_B.             (BC.5)
```

Because `I-B=C+R`, and `iota_B` has range in `E`, the two complementary
pieces are completed detector crossings:

```text
C W iota_B       =C[W,E]iota_B,
R W iota_B       =-[W,R]iota_B.               (BC.6)
```

Substitution gives Proof 291's three-branch identity `(BC.1)`.  The first
identity in `(BC.2)` then removes its returned-outer branch exactly:

```text
E A C[W,E]iota_B=(EAC)[W,E]iota_B=0.          (BC.7)
```

The adjoint causal identity in `(BC.2)` removes the dual returned branch when
the left defect is expanded.  A convenient orientation is to apply `(BC.3)`
to `W*` and take adjoints:

```text
d_W^left
 =-iota_B* A*[W,E]
  +iota_B*[W,R]R A*E.                          (BC.8)
```

For a Hermitian detector `W=W*`, `(BC.8)` is exactly `d_W*`.  For a cross-root
detector it is the adjoint orientation of the same two-boundary formula; the
complex polarization step is applied only after the signed scalar estimate.

## 4. Exact outer boundary support

Write the whole-line convolution kernel of `W` as `F(x-y)`.  For a compact
cross-correlation of roots supported in `[-B_root,B_root]`,

```text
supp(F) subset [-2 B_root, 2 B_root].          (BC.9)
```

The outer commutator has kernel

```text
[W,E](x,y)
 =(1_E(y)-1_E(x)) F(x-y).                     (BC.10)
```

Consequently it is zero unless the pair `(x,y)` crosses the half-line
boundary, and the crossing is confined to the strip `|x-y|<=2 B_root`.
This is the support operation that must happen before any path or branch norm.

The statement is about the completed commutator.  It does not say that the
raw translated projection difference or the uncompleted Sonin term is trace
class.

## 5. Full Sonin recombination

The Sonin projection must be read through its complete CC20 decomposition.  In
the abstract source notation write

```text
R=E E_hat E-K_prol,
```

and in the finite algebra certificate use `E_hat=Q` and
`K_prol=B Q B`.  The Leibniz rule gives the exact signed identity

```text
[W,R]
 =[W,E] E_hat E
  +E[W,E_hat]E
  +E E_hat[W,E]
  -[W,K_prol].                               (BC.11)
```

The first and third terms are outer-boundary orientations, the middle term is
the transported second-support crossing, and the last term is the prolate
correction.  They are one Sonin boundary, not four estimates.  The generator
that enters every renewal path is therefore

```text
d_W
 =[W,E]A iota_B
  -E A R(
      [W,E] E_hat E
     +E[W,E_hat]E
     +E E_hat[W,E]
     -[W,K_prol]
    )iota_B.                                   (BC.12)
```

Proofs 257--260 prohibit taking absolute values between the terms in
`(BC.11)`.  The prolate term is part of the cancellation budget, even when
its singular values are rapidly decreasing.

## 6. Consequence for the renewal path

Proof 291's path transform remains valid, but its input is now the shorter
two-boundary generator.  With

```text
[W_B,Delta]=d_W^left K-K*d_W,
```

every emission block is

```text
W K Delta^k-K Delta^k W_B
 =d_W Delta^k
  +K sum_(j=0)^(k-1)
     Delta^j(d_W^left K-K*d_W)Delta^(k-1-j).   (BC.13)
```

The final survivor block has the same formula with `k=n+1`.  The legal order
of operations is

```text
two completed boundaries (BC.3)
  -> assemble the complete path transform (BC.13)
  -> apply the off-range projection only to that transform
  -> pair with the bounded right path and canonical dual
  -> use cross-correlation support on the scalar
  -> take one absolute value.                   (BC.14)
```

Do not norm the `j`-sum, the growing left coframe, or the outer and Sonin
branches separately.  The horizon has introduced no new detector owner and
no additional support window; the unresolved problem is now a single signed
stopped transform of `(BC.3)`.

## 7. Finite certificate

`292_causal_two_boundary_generator_probe.py` uses the source-shaped model from
Proof 266 and the compact cross detector from Proof 285.  It checks:

```text
EAC=0 and CA*E=0;
[A,W]=[A*,W]=0;
R=E Q E-K_prol;
the complete commutator decomposition (BC.11);
direct d_W equals the two-boundary formula (BC.3);
the deleted returned branch is zero;
every path emission and tail block is unchanged;
the diagonal left defect is the right adjoint;
the scalar fixed mode is zero;
the outer commutator has no entries outside its finite displacement mask.
```

Run in WSL2:

```text
OPENBLAS_NUM_THREADS=1 python3 -B \
  docs/proofs/292_causal_two_boundary_generator_probe.py

OPENBLAS_NUM_THREADS=1 python3 -B \
  docs/proofs/292_causal_two_boundary_generator_probe.py \
  --multiplicity 12 --root-radius 2 --seed 2292 --horizon 12
```

The two cohorts report:

```text
+--------------------------------------+-------------+-------------+
| diagnostic                           | default     | alternate   |
+--------------------------------------+-------------+-------------+
| EAC                                  | 0           | 0           |
| CA*E                                 | 0           | 0           |
| returned-outer branch                | 0           | 0           |
| complete Sonin commutator error      | 3.22e-16    | 3.79e-16    |
| direct two-boundary generator error  | 1.26e-15    | 9.66e-16    |
| maximum exact error                  | 1.26e-15    | 1.03e-15    |
| two-boundary triangle ratio          | 1.216x      | 1.255x      |
+--------------------------------------+-------------+-------------+
```

The triangle ratio is a guard against branchwise norms, not an estimate used
by the route.

The certificate is finite algebra only.  A passing residual at machine
precision does not imply the continuous uniform estimate.

## 8. Evidence and route judgment

The external papers justify the geometric vocabulary, not the new theorem:

```text
CC20, "Weil positivity and Trace formula, the archimedean place":
https://arxiv.org/abs/2006.13771

CCM24, "Zeta zeros and prolate wave operators":
https://arxiv.org/abs/2310.18423
```

Their repository-specific locations and the causal invariance premise are
recorded in Proof 256:

```text
docs/proofs/256_one_sided_shorting_collapse.md, (O.7)--(O.8)
```

The new conclusion is strictly local:

```text
Proof 291 three-branch source expansion
  -> Proof 256 causal invariance
  -> Proof 292 two-boundary generator
  -> signed stopped-path estimate (open)
  -> Gate 3U (open)
  -> finite-S sign / RH (open).
```

No Lean theorem, axiom list, route consumer, or public Git history is changed
by this proof note.

## 9. Successor: observable compression

Proof 293 makes the next deletion before any norm.  Since the emission range of
`R_n` and `L_n` lies in `E`, replace every emission detector `W` by `E W E`.
The difference is the escape path generated by `C d_W=C W K`; it is killed by
`R_n*`, `L_n*`, and `P_n` exactly.  The surviving generator is

```text
g_W=E d_W
 =-E W C A iota_B-E A R[W,R]iota_B.
```

This keeps the ordered Gram anomaly and removes no arithmetic term.  The next
estimate is therefore Proof 293 `(BD.23)`, not a norm bound on `d_W` itself.
