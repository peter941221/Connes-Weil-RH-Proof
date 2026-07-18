# Proof 375: Sonin nearly-invariant transport

Date: 2026-07-18

Status: source-level identification of every finite-Euler-prefix Sonin range as
a nearly invariant Hardy subspace after the genuine common-log Fourier/Mellin
coordinate.  This supplies the carrier needed for a condition-number-free root
commutator theorem.  It does not identify the semilocal Euler weight with a
Hermite--Biehler structure function.

Gate 3U remains open.  The commutator estimate is Proof 376 and the
compact-root Sobolev transfer is Proof 377; those successors close `(MR.6)`,
not the final same-object root-split pairing.

## 1. Result

```text
+------------------------------------------------+---------------------------+
| layer                                          | judgment                  |
+------------------------------------------------+---------------------------+
| source Sonin completed Mellin image            | Burnol de Branges space  |
| ordinary log-Fourier image                     | nearly invariant         |
| finite Euler prefix                            | invertible H-infinity    |
| transported Sonin range                        | nearly invariant         |
| actual orthogonal endpoint projection          | retained                 |
| explicit semilocal structure function          | not needed / not claimed|
| finite certificate                             | supplied                 |
| Gate 3U / finite-S sign / Burnol / RH           | open / open / open / open|
+------------------------------------------------+---------------------------+
```

## 2. Source Sonin range

Let `F_log` be the unitary Fourier transform in the common logarithmic
coordinate.  The outer radial-support projection becomes one Hardy projection:

```text
F_log E F_log* =P_+.                                (NI.1)
```

Burnol's Theorem 8 identifies the completed Mellin image of the source Sonin
space with a de Branges space `B(E_lambda)`.  Write

```text
Theta_lambda=E_lambda#/E_lambda.                    (NI.2)
```

Division by `E_lambda` identifies `B(E_lambda)` isometrically with the Hardy
model space `K_(Theta_lambda)`.  If `gamma_infinity` is the fixed completed
Mellin factor, then the ordinary log-Fourier image of the source Sonin space is

```text
M_0=F_log Ran(R_0)
   =g_0 K_(Theta_lambda),

g_0=E_lambda/gamma_infinity.                        (NI.3)
```

Multiplication by `g_0` is isometric on `K_(Theta_lambda)` because both sides
of `(NI.3)` carry the original `L2` norm.  In particular, `M_0` is a closed
nearly invariant subspace of `H^2`.

Primary source:

```text
Burnol, Sur les espaces de Sonine associes par de Branges a la
transformation de Fourier, Theorem 8:
https://arxiv.org/abs/math/0208121
```

## 3. Causal Euler prefix

For a finite ordered prefix `S_j`, the repository's actual transport is

```text
T_j=product_(p in S_j)
  (I-p^(-1/2)U_(-log p)).                            (NI.4)
```

After `F_log`, `(NI.4)` is multiplication by

```text
tau_j(s)=product_(p in S_j)
  (1-p^(-1/2)exp(i log(p)s)),                        (NI.5)
```

up to the fixed Fourier-sign convention.  The sign is immaterial here.  Every
factor and its inverse are bounded analytic multipliers in the Hardy half-plane
selected by `(NI.1)`.  This is also the spectral readback of the concrete Lean
facts that both `T_j` and `T_j^-1` preserve the radial-support subspace.

The exact CCM24 transport theorem gives

```text
Ran(R_j)=T_j Ran(R_0).                               (NI.6)
```

Consequently,

```text
M_j=F_log Ran(R_j)
   =tau_j g_0 K_(Theta_lambda).                      (NI.7)
```

The range is closed because `tau_j` is boundedly invertible.

## 4. Near invariance survives the transport

Let `m_j=tau_j g_0`.  It is analytic and nonzero at the Cayley base point.  If

```text
f=m_j h in M_j,
f(0)=0,
```

then `h(0)=0`.  Model spaces are nearly invariant, so `h/z` belongs to
`K_(Theta_lambda)`, and hence

```text
f/z=m_j(h/z) in M_j.                                 (NI.8)
```

Thus every actual Euler-prefix Sonin range is nearly invariant.  This argument
uses only the range equality `(NI.6)` and analyticity/invertibility of the
causal multiplier.  It does not claim that `m_j` is an isometric multiplier in
the source coordinates.

## 5. Why this avoids the old carrier error

CCM24 Section 4.8 proves that the common entire-function set receives an
`S`-dependent de Branges norm.  It does not say that the displayed Euler weight
is the Hermite--Biehler generator of that norm.  Proof 340 correctly forbids
using such an identification.

Proof 375 does something weaker and sufficient:

```text
source de Branges model
  + actual bounded analytic Euler range transport
  -> nearly invariant endpoint range.               (NI.9)
```

No semilocal reproducing kernel, phase derivative, or explicit structure
function appears in `(NI.9)`.

## 6. Route readback

The endpoint quotient projection in Proof 373 is

```text
P_j=E-R_j.                                           (NI.10)
```

Under `F_log`, `R_j` becomes the orthogonal projection onto `M_j`, while `E`
becomes `P_+`.  Therefore the open commutator is

```text
F_log[C_g,P_j]F_log*
 =[M_(g_hat),P_+]-[M_(g_hat),P_(M_j)].               (NI.11)
```

Both projections in `(NI.11)` now belong to the Hardy/nearly-invariant class
handled uniformly by Proof 376.

## 7. Reproducible certificate

The companion probe builds a disk Hardy model space, transports it by several
literal analytic Euler factors, and checks the defining near-invariance defect
at every prefix.  It also verifies that scalar normalization does not change
the transported range.

Run only in the unified five-batch verification phase:

```text
OPENBLAS_NUM_THREADS=1 python3 -B \
  docs/proofs/375_sonin_nearly_invariant_transport_probe.py
```

The finite polynomial model checks the algebra in `(NI.7)--(NI.8)`.  The source
identification is Burnol's theorem plus CCM24's actual range transport, not the
finite calculation.

## 8. Route judgment

```text
+------------------------------------------------+---------------------------+
| layer                                          | judgment                  |
+------------------------------------------------+---------------------------+
| actual Sonin endpoint carrier                 | nearly invariant         |
| explicit semilocal HB generator              | unnecessary              |
| universal root commutator theorem             | Proof 376                |
| compact-root polynomial ledger                | Proof 377                |
| endpoint bound `(MR.6)`                        | not yet in this proof    |
| Gate 3U / finite-S sign / Burnol / RH           | open / open / open / open|
+------------------------------------------------+---------------------------+
```
