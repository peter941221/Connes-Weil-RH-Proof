# Proof 751: Gate Physical Normalized Real Trace Reduction

## Result

The result is useful but deliberately weaker than Gate 3U.  Proof 751 proves
that Proof 749/750's genuine pure-imaginary anomaly contributes zero only
under the real scalar readout.  It does not set the complex anomaly to zero.

Let

```text
T_S   =Tr_source(finiteEulerTargetCommutatorResponse_S),
Sym_S =Tr_source(finiteEulerNormalizedSymmetricBoundaryResponse_S),
A_S   =Tr_ambient(finiteEulerNormalizedPhysicalAnomalyBoundaryReadout_S),
K_S   =finiteEulerObliqueShearFullKernelTrace_S.
```

Lean proves

```text
Re(A_S)=0,
Sym_S=(Re(T_S):C)=(Re(K_S):C),
norm(Sym_S)=abs(Re(K_S)).                               (AC.1)
```

The full-kernel scalar `K_S` still contains the outer, reflected
second-support, and prolate branches in one signed `tsum`.  Compact-root
support therefore acts before the real part and before the first absolute
value.

```text
+--------------------------------------+----------------------------------+
| layer                                | result                           |
+--------------------------------------+----------------------------------+
| source Gram anomaly real trace       | zero                             |
| ambient physical anomaly real trace  | zero                             |
| symmetric response trace             | real                            |
| symmetric/full-kernel real readout   | exact                            |
| family-uniform real-bound interface  | exact equivalence                |
| full complex anomaly                 | retained                         |
| complex-norm Gate 3U                 | open                             |
| RH                                   | open                             |
+--------------------------------------+----------------------------------+
```

## 1. What Changed

Proof 749 gives, with

```text
b_S=Tr_source(sourceBandGramResponse_S),
```

the exact formulas

```text
Tr(SymmetricResponse_S)=-1/2(b_S+conj(b_S)),
Tr(Anomaly_S)=1/2(b_S-conj(b_S)).                      (AC.2)
```

The second scalar in `(AC.2)` is generally nonzero, but its real part is
zero.  The first scalar is exactly `-Re(b_S)` embedded in `C`.

The actual target orientation satisfies

```text
Tr(Target_S)=-conj(b_S).                               (AC.3)
```

Equations `(AC.2)` and `(AC.3)` yield

```text
Tr(SymmetricResponse_S)=(Re Tr(Target_S):C).           (AC.4)
```

No infinite-dimensional trace cycle is used here.  The identities reuse the
completed four-branch pair from Proof 749 and the legal source-to-ambient
cycle from Proof 750.

## 2. Support-First Readout

Proof 746 already identifies the target trace with one physical full-kernel
series:

```text
Tr(Target_S)=K_S.
```

Substitution into `(AC.4)` gives the central Proof 751 identity

```text
Tr(SymmetricResponse_S)=(Re K_S:C).                    (AC.5)
```

This order matters:

```text
complete physical full-kernel scalar
  -> compact-root support and branch cancellation
  -> real part
  -> one absolute value.                               (AC.6)
```

Taking real parts branch by branch or bounding the two leakage orientations
separately is still forbidden.

## 3. Scope

Proof 751 exposes a weaker real-trace contract:

```text
exists C, forall finite S, norm(Tr(Symmetric_S))<=C

  iff

exists C, forall finite S, abs(Re(K_S))<=C.             (AC.7)
```

The repository's current Gate 3U contract bounds `norm(K_S)`, not only its
real part.  Proof 751 does not silently replace that contract.  A successor
must audit the downstream finite-S limit and sign consumers before claiming
that `(AC.7)` is sufficient for the RH route.

The source module is

```text
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSGatePhysicalNormalizedRealTraceReduction.lean
```

The import-facing audit is

```text
ConnesWeilRH/Dev/
  CCM24FiniteSGatePhysicalNormalizedRealTraceReductionAudit.lean
```

## 4. Verification

The Windows source tree was copied to the Ubuntu-24.04 WSL2 ext4 verification
tree before building.  The accepted batches were

```text
+------------------------+-----------+
| batch                  | result    |
+------------------------+-----------+
| focused source + audit | 3395/3395 |
| aggregate + audit      | 4020/4020 |
| full repository        | 4100/4100 |
+------------------------+-----------+
```

The audit contains exactly seven `#print axioms` commands.  Every audited
public theorem reports exactly

```text
[propext, Classical.choice, Quot.sound]
```

Static checks found no `sorry`, `admit`, user `axiom` or `constant`, `unsafe`
declaration, heartbeat increase, recursion-limit increase, new linter warning,
line over 100 characters, or trailing whitespace in the new source and audit.

The final SHA-256 values matched between the Windows truth source and the WSL2
verification copy:

```text
source
a4707dfe07fae51c02a1924045548c9f63d04c5df58988df11497d4ce4900b37

audit
f7af0ff262ca8e6687c911c742c54c444c00e384859afaed57ec6b20f137b1ad

aggregate
6f274bcacc630fb11f23ce98c8b211b940f94b468596bb3711a1d041ffc4ab96
```

Gate 3U, the finite-S sign, the arithmetic same-object identity, Burnol's
identity, and `_root_.RiemannHypothesis` remain open.
