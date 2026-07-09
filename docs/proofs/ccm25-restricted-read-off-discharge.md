# CCM25 Restricted Read-Off Discharge

Status: proof package for the first source-interface discharge target.

This package attacks:

```text
CCM25RestrictedReadOffDischarge(lambda,g)
```

It does not prove the CCM25 source paper inside Lean. It proves that the current
route uses the CCM25 restricted read-off through five Lean replacement targets:

```text
WindowLambdaCompatibility
CCM25QWLambdaFormulaReadOff
CCM25PoleNormalizationReadOff
RestrictedPrimeIndexCoverageStatement
FinitePrimeTermNormalizationStatement
```

The result is a source-interface discharge package: it identifies the exact
source formulas, route hypotheses, Lean replacement targets, and two supporting
normalization checks needed before the CCM25 restricted leg can be upgraded from
an imported contract to a formal or externally accepted theorem.

## Evidence Boundary

| claim | evidence |
|---|---|
| `QW(f,g)=Psi(f^* * g)` | manuscript formula map `docs/manuscripts/connes-weil-rh-proof-draft.md:66`; source reread `docs/audits/source-reread-v0.2.md:47` |
| `Psi=W_(0,2)-W_R-sum_p W_p`, with `W_R=-W_infty` | manuscript sign audit `docs/manuscripts/connes-weil-rh-proof-draft.md:68`, `1013-1021`, `1349-1358` |
| restricted `QW_lambda(g,g)` formula | manuscript `docs/manuscripts/connes-weil-rh-proof-draft.md:988-1002`; source reread `docs/audits/source-reread-v0.2.md:48` |
| prime-power pairing `<g|T(n)g>` | manuscript `docs/manuscripts/connes-weil-rh-proof-draft.md:70-71`, `999-1001` |
| admissible window and visible-prime side condition | manuscript `docs/manuscripts/connes-weil-rh-proof-draft.md:1043-1057`, `1368-1374` |
| Lean restricted read-off target | `ConnesWeilRH/Route/Theorem1.lean:87-98`, `276-290` |
| Lean finite-prime coverage target | `ConnesWeilRH/Route/AdmissibleWindow.lean:43-68` |

## Target Statement

For a source-backed fixed-`S` test `g` and `lambda > 1`, the route needs:

```text
CCM25RestrictedReadOffDischarge(lambda,g):
  the restricted CCM25 Weil-form leg used by Theorem 1 is exactly

    QW_lambda(g,g)

  with:

    1. the same support window as the fixed-S positive trace;
    2. the source test F_g=g^* * g;
    3. all visible finite-prime atoms included in the restricted index set;
    4. finite-prime terms normalized by the same von Mangoldt and pairing
       convention as CCM25;
    5. the CCM pole functional included inside QW_lambda, while the route
       PoleJetExtra ledger remains outside QW_lambda;
    6. the sign pattern inherited from CCM25, not from a route-local shortcut.
```

## Lemma 1. Window Lambda Compatibility

Statement:

```text
RestrictedReadOffWindow(lambda,g):
  the restricted parameter lambda is the same parameter used by the CCM24
  source window and by the CCM25 restricted form.
```

Proof.

The Lean route defines:

```text
WindowLambdaCompatibility inputs g lambda
  =
1 < lambda
and WindowSupportContainment inputs g lambda
and inputs.ccm24.semilocalSymbols.lambdaCompatible g.window lambda.
```

`WindowSupportContainment` records four separate facts:

```text
source support in the CCM24 window
Fourier support in the same window
convolution-support transport
windowContainedInLambda window lambda
```

The route derives these facts through
`window_support_containment_of_source_backed` and
`lambda_compatible_of_source_backed` in
`ConnesWeilRH/Route/AdmissibleWindow.lean:119-135`.

Thus the restricted `QW_lambda` read-off is not allowed to use a free
route-local cutoff. Its `lambda` is tied to the same source-backed window used
by the fixed-`S` support-square trace.

Output:

```text
WindowLambdaCompatibility inputs g lambda.
```

Remaining discharge burden:

```text
Replace the symbolic CCM24 window predicates with source-paper or formal
proofs of support, Fourier-support, convolution-support transport, and window
containment.
```

## Lemma 2. Source Test Identification

Statement:

```text
RestrictedReadOffSourceTest(g):
  the CCM25 restricted formula is applied to F_g=g^* * g.
```

Proof.

CCM25 reads the full Weil form through:

```text
QW(f,g)=Psi(f^* * g).
```

The manuscript source map records this formula at
`docs/manuscripts/connes-weil-rh-proof-draft.md:66`, and the source reread audit
places the source range at `mc2arXiv.tex:445-470`.

The support-square trace has the route vector on both sides:

```text
theta_S(g)^* (...) theta_S(g).
```

The corresponding source test is therefore:

```text
F_g = g^* * g.
```

The no-defect read-off package already records this as the test entering
`Psi`; see `docs/proofs/fixed-s-no-defect-compact-form-read-off.md:65-94`.

Output:

```text
CCM25QWDefinitionReadOff inputs g.
```

Remaining discharge burden:

```text
Replace the symbolic `convolutionStar g.weilTest g.weilTest` field by the
actual CCM25 half-density convolution test.
```

## Lemma 3. Restricted QW Lambda Formula

Statement:

```text
RestrictedQWLambdaFormula(lambda,g):
  for lambda > 1,

  QW_lambda(g,g)
    =
  archimedean term
  + pole pairing
  - restricted finite-prime sum.
```

Proof.

The manuscript records the restricted CCM25 formula as:

```text
QW_lambda(g,g)
  =
int_R |hat g(t)|^2 (2 partial_t theta(t))/(2 pi) dt
  +
2 Re(hat g(i/2) overline{hat g(-i/2)})
  -
sum_(1<n<=lambda^2) Lambda(n)<g|T(n)g>,

<g|T(n)g>
  =
n^(-1/2)((g^* * g)(n)+(g^* * g)(n^(-1))).
```

Evidence:

```text
docs/manuscripts/connes-weil-rh-proof-draft.md:988-1002
docs/audits/source-reread-v0.2.md:48
```

The Lean target is:

```text
CCM25QWLambdaFormulaReadOff inputs g lambda
```

defined in `ConnesWeilRH/Route/Theorem1.lean:69-80`. The theorem
`ccm25_qw_lambda_formula_read_off` derives it from
`inputs.ccm25.qwLambdaFormula` at
`ConnesWeilRH/Route/Theorem1.lean:265-269`.

Output:

```text
CCM25QWLambdaFormulaReadOff inputs g lambda.
```

Remaining discharge burden:

```text
Replace `inputs.ccm25.qwLambdaFormula` with an imported or formal proof of the
restricted CCM25 formula, including the exact support and half-density
conventions.
```

## Lemma 4. Finite-Prime Coverage And Term Normalization

Statement:

```text
RestrictedFinitePrimeDischarge(lambda,g):
  every finite-prime atom visible to F_g is in the restricted index set, and
  every finite-prime term uses the CCM25 von Mangoldt / prime-power pairing
  normalization.
```

Proof.

The manuscript explicitly rejects reading a fixed finite-`S` trace as the full
restricted form before the visible-prime condition is checked:

```text
docs/manuscripts/connes-weil-rh-proof-draft.md:1043-1057
```

The sign and normalization appendix records that finite-prime coefficients
enter only through the CCM Weil quadratic form:

```text
docs/manuscripts/connes-weil-rh-proof-draft.md:1349-1374
```

The Lean scaffold splits this into three targets:

```text
GlobalPrimeIndexCoverageStatement
RestrictedPrimeIndexCoverageStatement
FinitePrimeTermNormalizationStatement
```

and derives the selected-test instances through:

```text
finite_prime_visibility_statement_of_source_backed
global_prime_index_covers_of_source_backed
restricted_prime_index_covers_of_source_backed
finite_prime_term_normalization_of_source_backed
```

Evidence:

```text
ConnesWeilRH/Route/AdmissibleWindow.lean:43-68
```

Therefore the restricted read-off has two finite-prime gates:

```text
coverage:
  visible atoms of F_g lie in restrictedPrimeIndexSet lambda;

normalization:
  finitePrimeTerm n (g^* * g)
    =
  vonMangoldtWeight n * primePowerPairing n g g.
```

These are logically different. Coverage says the restricted sum has the right
support; normalization says every included atom has the right coefficient and
pairing.

Output:

```text
RestrictedPrimeIndexCoverageStatement W lambda F_g
FinitePrimeTermNormalizationStatement W g g
```

Remaining discharge burden:

```text
Replace the symbolic `restrictedPrimeIndexSet lambda`,
`finitePrimeAtomVisible`, `vonMangoldtWeight`, and `primePowerPairing` fields by
the concrete CCM25 prime-power support and pairing definitions.
```

## Lemma 5. Pole Normalization And No Double Counting

Statement:

```text
RestrictedPoleDischarge(g):
  the CCM pole functional is inside QW_lambda, while the route PoleJetExtra
  ledger remains outside QW_lambda until triple vanishing kills it.
```

Proof.

The manuscript records:

```text
W_(0,2)(F)=hat F(i/2)+hat F(-i/2)
```

and the restricted form contains:

```text
2 Re(hat g(i/2) overline{hat g(-i/2)}).
```

Evidence:

```text
docs/manuscripts/connes-weil-rh-proof-draft.md:67
docs/manuscripts/connes-weil-rh-proof-draft.md:991-1001
docs/proofs/battle-1-test-quotient-proof-package.md:180-204
```

The manuscript also states that `PoleJetExtra_(S,I)(g)` is not a second copy of
the CCM pole functional:

```text
docs/manuscripts/connes-weil-rh-proof-draft.md:1004-1011
```

The Lean target is:

```text
CCM25PoleNormalizationReadOff inputs g
```

defined in `ConnesWeilRH/Route/Theorem1.lean:81-85` and obtained from
`inputs.ccm25.poleNormalization` at
`ConnesWeilRH/Route/Theorem1.lean:271-274`.

Output:

```text
CCM25PoleNormalizationReadOff inputs g.
```

Remaining discharge burden:

```text
Replace `inputs.ccm25.poleNormalization` with an imported or formal proof that
the restricted pole pairing is exactly the CCM pole functional under the route's
half-density convention.
```

## Lemma 6. Restricted Sign Pattern

Statement:

```text
RestrictedSignDischarge(lambda,g):
  the sign in the restricted finite-prime sum is the CCM25 sign, not a
  route-local trace shortcut.
```

Proof.

The source sign spine is:

```text
Psi(F)=W_(0,2)(F)-W_R(F)-sum_p W_p(F)
W_R=-W_infty
```

so:

```text
Psi(F)=W_(0,2)(F)+W_infty(F)-sum_p W_p(F).
```

The restricted formula keeps the finite-prime contribution with the negative
sign:

```text
-sum_(1<n<=lambda^2) Lambda(n)<g|T(n)g>.
```

Evidence:

```text
docs/manuscripts/connes-weil-rh-proof-draft.md:1013-1021
docs/manuscripts/connes-weil-rh-proof-draft.md:1349-1366
```

The manuscript explicitly rejects the false even-trace shortcut:

```text
Tr_even(u_p^(-1)d u_p)=2 Tr(u_p^(-1)d u_p).
```

Finite-prime coefficients enter only through the CCM Weil quadratic form.

Output:

```text
CCM25PsiSignReadOff inputs g
and
CCM25QWLambdaFormulaReadOff inputs g lambda
with the restricted finite-prime sum carrying the negative sign.
```

Remaining discharge burden:

```text
Formalize or import the exact CCM25 sign convention, including the relationship
between `W_R`, `W_infty`, and the restricted finite-prime operator terms.
```

## Combined Result

Combining Lemmas 1 through 6 gives:

```text
CCM25RestrictedReadOffDischarge(lambda,g)
```

at source-interface proof-package level.

The corresponding Lean decomposition is:

```text
CCM25RestrictedQWReadOff inputs g lambda
  =
WindowLambdaCompatibility inputs g lambda
and
CCM25QWLambdaFormulaReadOff inputs g lambda
and
CCM25PoleNormalizationReadOff inputs g
```

The finite-prime side gates are not syntactically inside
`CCM25RestrictedQWReadOff`, but they are required before this read-off can be
used as the full restricted Weil form for the fixed-`S` trace:

```text
RestrictedPrimeIndexCoverageStatement W lambda F_g
FinitePrimeTermNormalizationStatement W g g
```

Those gates are currently derived from
`inputs.ccm25.finitePrimeNormalization`.

## Current Status

```text
Window lambda compatibility:        reduced to CCM24 source-window discharge
Source test F_g=g^* * g:            identified from QW(f,g)=Psi(f^* * g)
Restricted QW_lambda formula:       reduced to CCM25 source formula discharge
Finite-prime coverage:              explicit Lean target, still source-backed
Finite-prime term normalization:    explicit Lean target, still source-backed
Pole normalization:                 reduced to CCM25 source formula discharge
Restricted sign pattern:            fixed by manuscript/source sign audit

CCM25RestrictedReadOffDischarge:    source-interface proof package written
Formal/accepted source discharge:   still open
```

This moves the next attack from an informal phrase, "CCM25 reads off the
restricted form," to five Lean replacement targets plus the source-test and sign
normalization checks that protect those targets. It does not remove the
source-conditional boundary by itself.
