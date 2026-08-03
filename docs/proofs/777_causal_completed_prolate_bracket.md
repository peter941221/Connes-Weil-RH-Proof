# Proof 777: Causal Completed-Prolate Bracket

## Result

Proof 777 connects the actual causal corner from Proof 776 to CCM24's actual
two-support/prolate identity.  It is an exact Lean normal form, not a Gate 3U
estimate.

Write

```text
E = radialSupportProjection,
Q = sourceFourierSupportProjection,
R = sourceSoninProjection,
K = sourceProlateRemainder,
T = finiteEulerTransportOperator.
```

The concrete source identity is

```text
R = E Q E - K.
```

Lean first packages the coupled band

```text
B_complete = E - E Q E + K = E-R.                  (777.1)
```

It then proves the causal identity

```text
E T (I-R)
  = E T (I-E) + T B_complete.                       (777.2)
```

Therefore the literal target has the completed-root form

```text
Target_S
 = D_S* [E T_S (I-E) + T_S(E-EQ E+K_prol)] C_root* C_root J.
                                                               (777.3)
```

The declarations are:

```text
sourceCausalCompletedBand_eq_sourceBandProjection
sourceSoninComplementProjection_eq_radialComplement_add_causalCompletedBand
finiteEulerCausalCompletedSoninComplement_eq_causalTransportComplement
finiteEulerTargetCommutatorResponse_eq_causalCompletedProlateRootCorner
```

## Why It Matters

Proof 776 put the compact root after the full source complement:

```text
Target_S = D_S* E T_S (I-R) C_root* C_root J.
```

Equation `(777.2)` says exactly what the source complement contains before
that root acts.

```text
source complement
       |
       +-- outer crossing: E T (I-E)
       |
       +-- completed Sonin band: T(E-EQE+K_prol)
                                      ^      ^
                                      |      |
                                  Fourier  prolate
```

The displayed plus sign is part of one operator identity.  Neither term may
be assigned an independent trace norm or Hilbert--Schmidt cost before the
compact root has acted; doing so recreates the total-variation obstruction of
Proof 260.

## Stronger Generic Guard

The accompanying finite certificate checks that even the complete *abstract*
two-projection algebra is not a uniform-bound producer by itself.  For each
block use orthonormal vectors `r,b,f`, set

```text
E = |r><r| + |b><b|,
R = |r><r|,
B = E-R = |b><b|,

q_j = sqrt(mu_j) b + sqrt(1-mu_j) f,
Q = |r><r| + |q_j><q_j|,
K = mu_j |b><b|,
mu_j = 2^(-4(j+1)^2).
```

Then, blockwise,

```text
R = E Q E-K,
K = B Q B,
norm(Q B) = sqrt(mu_j) <= 1/4.
```

Thus `K` is positive, trace class across arbitrarily many blocks, and has a
uniform strict-angle and super-exponentially decaying spectral ledger.

Let `U` swap `r` and `b` while fixing `f`, and choose `0<a,b<1`:

```text
T = I-aU,
C = (I+bU)/(1+b),
W = C* C,
H = T* T.
```

Both `T` and `T^-1` preserve `E`; `H W=W H`; and `C` is a contractive local
one-edge root.  With `J` the inclusion of the `r` coordinates,

```text
G = J* H J = (1+a^2) I,

G^-1 J* H (I-R) W J
 = -4ab / ((1+a^2)(1+b)^2) I.                       (777.4)
```

The trace of `(777.4)` grows linearly in the number of blocks although
`sum_j mu_j` stays bounded.  This is not a CCM24 counterexample: the block
projection `Q` is not the Hardy--Titchmarsh/Fourier half-line projection on a
single real logarithmic line.

It proves the narrower conclusion:

```text
causality + local root + R=EQE-K + K=BQB
  + strict prolate angle + rapidly summable prolate spectrum
does not by itself imply Gate 3U.
```

The next valid estimate must use the genuine Fourier transport and real-line
compact-root geometry, while retaining the bracket in `(777.3)` before its
first absolute value.

## Verification

```text
lake build ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSGatePhysicalCausalCompletedBracket
lake env lean ConnesWeilRH/Dev/CCM24FiniteSGatePhysicalCausalCompletedBracketAudit.lean
python3 -B docs/proofs/777_causal_completed_prolate_bracket_probe.py
```

The Ubuntu-24.04 WSL2 ext4 verification batch passed:

```text
+----------------------------------------------------------+-------+--------+
| target                                                   | jobs  | result |
+----------------------------------------------------------+-------+--------+
| Proof 777 focused source                                 |  3393 | PASS   |
| Proof 777 focused axiom audit                            |    -- | PASS   |
| Proof 777 finite-block certificate                       |    -- | PASS   |
| CCM25Concrete aggregate                                  |  4036 | PASS   |
| full repository                                          |  4117 | PASS   |
+----------------------------------------------------------+-------+--------+
```

The certificate's maximum completion, causality, corner-formula, and
metric/detector errors were respectively `1.18e-16`, `0`, `0`, and `0`.
Its prolate trace stayed below `0.062515`, while the absolute corner trace per
source block was `0.355556`.

```text
+--------------------------------------------------------------+----------------+
| claim                                                        | status         |
+--------------------------------------------------------------+----------------+
| causal completed-prolate normal form                         | Lean proved    |
| generic two-projection/prolate sufficient bound              | disproved      |
| actual Fourier/real-line compact-root estimate               | open           |
| Gate 3U / finite-S sign / Burnol identity / RH               | open           |
+--------------------------------------------------------------+----------------+
```
