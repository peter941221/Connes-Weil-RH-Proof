# Proof 352: Julia dual-pairing Lean interface

Date: 2026-07-18

Status: axiom-clean Lean formalization of Proof 351's Julia defect telescope,
weighted range-row Bessel estimate, Hilbert--Schmidt basis amplification, and
the one legal finite direct-sum Cauchy--Schwarz consumer.  The complete
Proof 343 detector innovation identity and its source-side square estimate are
still open.  Therefore Gate 3U, the finite-S sign, Burnol's identity, and RH
remain unproved.

## 1. Result

```text
+------------------------------------------------+---------------------------+
| layer                                          | judgment                  |
+------------------------------------------------+---------------------------+
| Julia defect/survivor telescope                | Lean, exact               |
| weighted range energy <= defect energy         | Lean, exact               |
| weighted range energy <= source norm square    | Lean, exact               |
| basis-level Hilbert--Schmidt amplification     | Lean, exact               |
| finite direct-sum dual pairing                 | Lean, exact               |
| Proof 343 endpoint = detector/range pairing    | open                      |
| source detector square estimate                | open                      |
| Gate 3U / finite-S sign / Burnol / RH           | open / open / open / open|
+------------------------------------------------+---------------------------+
```

The interface is deliberately one-way:

```text
Julia colligation steps
        |
        v
exact defect telescope ----> weighted range Bessel row
                                      |
                                      v
Proof 343 detector producer ----> one finite dual pairing
          OPEN                        |
                                      v
                             Gate 3U near bound
                                  STILL OPEN
```

No theorem in this module constructs the missing detector row from a generic
bounded operator.

## 2. Lean owner

The source module is

```text
ConnesWeilRH/Source/CCM25Concrete/CCM24FiniteSJuliaBessel.lean
```

One pulled-back Julia step stores a transfer, a defect output, a normalized
range-sine output, and the two pointwise inequalities needed by Proof 351:

```lean
structure JuliaDefectStep (H G : Type*)
    [NormedAddCommGroup H] [InnerProductSpace C H]
    [NormedAddCommGroup G] [InnerProductSpace C G] where
  transfer : H ->L[C] H
  defect : H ->L[C] G
  rangeSine : H ->L[C] G
  weight : R
  weight_nonneg : 0 <= weight
  pythagorean : forall x : H,
    norm (transfer x) ^ 2 + norm (defect x) ^ 2 = norm x ^ 2
  rangeSine_weighted_le_defect : forall x : H,
    weight * norm (rangeSine x) ^ 2 <= norm (defect x) ^ 2
```

The displayed block uses ASCII mathematical aliases for readability.  The
actual Lean source uses Mathlib's bundled continuous-linear-map and norm
notations.

The exact telescope is

```lean
theorem juliaDefectEnergy_add_survivor_normSq
    (steps : List (JuliaDefectStep H G)) (x : H) :
    juliaDefectEnergy steps x + norm (juliaSurvivor steps x) ^ 2 =
      norm x ^ 2
```

It yields the constant-one range estimate

```lean
theorem juliaRangeEnergy_le_normSq
    (steps : List (JuliaDefectStep H G)) (x : H) :
    juliaRangeEnergy steps x <= norm x ^ 2
```

and its basis amplification

```lean
theorem tsum_juliaRangeEnergy_le ... :
  tsum (fun i => juliaRangeEnergy steps (vectors i)) <=
    tsum (fun i => norm (vectors i) ^ 2)
```

These statements require only inner-product spaces.  Completeness was removed
after Lean's unused-section-variable linter showed it was not used.

## 3. Final consumer

Proof 351 `(JB.22)` takes one absolute value only after the completed detector
and range rows have been formed.  Its finite direct-sum core is now:

```lean
theorem finite_dual_pairing_norm_le
    {iota : Type*} [Fintype iota]
    (left right : iota -> H) :
    norm (sum i, inner C (left i) (right i)) <=
      Real.sqrt (sum i, norm (left i) ^ 2) *
        Real.sqrt (sum i, norm (right i) ^ 2)
```

This theorem is only a consumer.  A route instantiation must prove, on the
literal Proof 343 quotient owner,

```text
Q_S(eta,xi)=sum_j <H_j,R_j>,                         (JD.1)

sum_j (p_j-1) norm(R_j)_2^2
  <=norm(A_(eta,xi))_2^2,                            (JD.2)

sum_j norm(H_j)_2^2/(p_j-1)
  <=C(1+B_root)^d
    norm(eta)_(H^r)^2 norm(xi)_(H^r)^2.             (JD.3)
```

The Lean module owns the abstract range half of `(JD.2)` and the final
Cauchy--Schwarz step.  It does not own `(JD.1)` or `(JD.3)`.

## 4. Verification

The focused source check, axiom audit, and narrow `CCM25Concrete` aggregate
import all pass in a Linux-side WSL2 verification environment.

```text
+------------------------------------------+-------------------------------+
| check                                    | result                        |
+------------------------------------------+-------------------------------+
| focused source elaboration               | PASS                          |
| audit elaboration                        | PASS                          |
| CCM25Concrete aggregate import           | PASS                          |
| linter warnings                          | none                          |
| audited theorem axiom set                | propext, Classical.choice,    |
|                                          | Quot.sound                    |
+------------------------------------------+-------------------------------+
```

The audit file is

```text
ConnesWeilRH/Dev/CCM24FiniteSJuliaBesselAudit.lean
```

Every printed theorem has exactly the project's allowed axiom set:

```text
[propext, Classical.choice, Quot.sound]
```

No full project build was run.

## 5. Active bottom

The next theorem must construct the actual `H_j` from the complete physical
bracket

```text
outer boundary
  - Sonin boundary
  + prolate correction
  + half-density residue cancellation
  + canonical and boundary-anomaly terms.           (JD.4)
```

The likely square budget is compatible with compact support: a root-smoothed
half-line crossing at displacement `log(p)` has Hilbert--Schmidt square cost
proportional to `log(p)`, while Julia normalization contributes `1/(p-1)`.
Thus the near arithmetic envelope is

```text
sum_(log(p)<=L) log(p)/(p-1) <=L(1+L).               (JD.5)
```

Equation `(JD.5)` is only the available budget.  It becomes a Gate estimate
only after `(JD.1)` proves that the complete detector innovations are
contractive images of those physical crossings.  Expanding the branches or
taking their trace norms separately would violate Proofs 260, 340, and 348.
