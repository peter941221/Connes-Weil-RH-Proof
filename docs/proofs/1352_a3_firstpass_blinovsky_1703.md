# Record 1352 (AUDIT, first pass) - A3 prey arXiv:1703.03827v16 (Blinovsky)

```text
+---------------------------------------------------------------------+
| Task #8 (A3) FIRST PASS, completed in the 2026-09-12 parallel     |
| wave. Verdict at first pass; no deeper audit run (owner can        |
| re-open). MODEL grade (no machine-check of their claims - none     |
| exist to check); certifies nothing about RH either way.            |
+---------------------------------------------------------------------+
```

## 1. Prey identification (parsed, with sources)

| field | value |
|---|---|
| arXiv id | 1703.03827, v16 (v1 Mar 2017 ... v16 2026-08-10) |
| title | "Proof of Riemann hypothesis" |
| author | Vladimir Blinovsky |
| primary class | math.GM (general mathematics - not math.NT/FA) |
| size | ~9 KB |
| method (their own words) | show CONVEXITY of a function K(sigma,T) whose zeros in the open critical strip coincide with zeta's |
| URL | https://arxiv.org/abs/1703.03827 |

## 2. Species test against OUR gate (the only test that matters to this repo)

The live gate object (committed): 0 <= qw(g) on the vanishing class,
where qw is a QUADRATIC FORM in a test function f (f * f convolution
S3 in 1351, laplace/spectral terms S1/S4), machine-anchored iff RH by
C1WeilCriterionEquivalence.lean (d767a1d).

```text
  Their K(sigma,T) convexity argument contains:
    - no test-function quadratic form ......... absent
    - no Weil / positivity-of-trace structure . absent
    - no spectral side / zero-sum identity .... absent
  => NOT GATE SPECIES. The paper neither instantiates a potential
  counterexample to the gate nor supplies an input to it. No
  falsifier-lane entry (empty lane precedent: 1343), and no
  harvestable lemma either.
```

## 3. Verdict + customs stamp (external-safe wording)

First-pass verdict: CLOSED as not-in-scope for the A3 audit lane.
The audit was about verification-arbitrage prey (claims that, if
true, would breach or bypass our gate - 1345 portfolio note). This
prey makes no claim of that species; v16-v1 history (9 years, 16
versions, 9 KB, math.GM) is the standard customs profile.

Draft public-safe response stamp (plain text, no local paths, no
private artifact names - usable verbatim if the owner chooses to
post anywhere):

```text
  The claimed convexity property concerns a counting function
  K(sigma,T) and does not engage the Weil-positivity framework,
  its test-function quadratic forms, or any verified equivalence
  to RH in the Lean formalization sense. No counterexample to,
  or input for, that framework is identified; the argument is
  therefore outside the scope our audit covers.
```

## 4. Registration-vs-text mismatch (why the machine-audit never engaged)

Task #8 was registered as auditing a "Li-criterion positivity" claim
(1344:53 "2026-02 Li-positivity paper first"), and the prey was
concretized from the r/math thread 1rc0i3o quote "the key ... is to
get Weil's positivity condition" (1345:183). BOTH descriptions
attribute a Weil/Li-positivity species to the paper; the paper text
(v16) contains neither - its method is K(sigma,T) convexity (s1-s2
above). So the mismatch is NOT only a forum paraphrase: our own lane
label inherited it. No conspiracy claimed; recorded so a future
re-open (or any citation of this audit) starts from the paper text,
not from the register vocabulary. Consequence for the lane design:
the s2 species test must be applied to the PAPER, never to the
headline - the headline here sent us looking for a gate-species
claim that the text does not make.

## 5. Next steps

1. Task #8 first pass = DONE here; owner options: accept closure,
   or order a deeper pass (the deeper pass would audit their convexity
   claim internally - not our gate - so it is priced as generic
   refereeing effort, not verification-arbitrage).
2. Audit-lane residual value: the SPECIES TEST (s2) is reusable
   (and per s4 must run on paper text, not headline).
   machinery - any future "RH proof" headline gets screened against
   the gate-form inventory (1351 s1) in minutes.
3. Mainline unchanged: A1b (batch 1548) running; portfolio order
   per 1344 s3b.
