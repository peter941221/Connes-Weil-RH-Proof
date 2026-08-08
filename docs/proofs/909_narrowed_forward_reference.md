## STATUS UPDATE (2026-08-08, later same day): Option A LANDED + verified at Source layer

This narrowing patch has now been **applied and verified** (it is no longer just a captured reference):
- `ConnesWeilRH/Source/AnalyticCore.lean` narrowed per the diff below, **plus** a new
  `SourceWeilFormData.finitePrimeDominance` def and an `hdom` argument on
  `finite_prime_term_normalization_statement` (the dominance-law thread required by Option A).
- `ConnesWeilRH/Source/AnalyticSourceModel.lean`: `SourceWeilFormData.toCCM25SourceModel` and
  `SourceModelConstructorCore.ofSourceAnalyticCore` now thread `hdom`.
- Verified green on warm mirror cwr-h2probe1: `AnalyticCore` + `AnalyticSourceModel` build (2943 jobs),
  `#print axioms` on the two modified declarations = `[propext, Classical.choice, Quot.sound]`, zero `sorry`.
- ROUTE NAVIGATION CLOSED (same session): Dev/UnconditionalSkeleton.lean:688 now passes
  SourceWeilFormData.finitePrimeDominance_of_certificates (proven from concrete certs, axiom-clean) to
  ofSourceAnalyticCore. Full flock-guarded lake build ConnesWeilRH.Dev.UnconditionalSkeleton on
  cwr-h2probe1 completed exit 0, [3495/3495] Built; axiom audit of the Dev core cascades only into the two
  pre-existing ...Root axioms (no sorryAx, no new project axiom). RH not claimed.

# 909 - H2 forward-row narrowing: CORE works, ROUTE rim needs a dominance law (2026-08-08)

This file records the exact `AnalyticCore.lean` patch that narrows `PerCommonSourceFinitePrimeSupport`'s
forward rows from `\u2200 F` to per-`common` (S7l), which makes the structure *satisfiable* (unsatisfiable
with the old `\u2200 F` forward - S7j/7k). The repo was reverted to HEAD after capture so the tree stays
green; this is the reference for a follow-up session.

## Verified result
- The narrowing alone compiles (`AnalyticCore` builds green after tying the 3 internal call sites and the
  three `toWeilFormSymbols_*` wrappers to the `common` test).
- Real structural milestone: old `universal_impossible` proved the `\u2200 F` forward forces every prime
  into a finite Finset; the narrowed forward is satisfiable for compact-support `common`.
- **Blast radius**: the route's `finite_prime_term_normalization_statement` cannot be derived for arbitrary
  `f g` from per-common coverage; it needs a dominance law `\u2200 f g n, visible (scale.compatible Star f g) n -> visible (encode common) n`.
  That new hypothesis changes the public `FinitePrimeNormalizationStatement`, cascading into
  `AnalyticSourceModel:40`, `ObjectExpandedRows`, `UnconditionalSkeleton` consumers. Full green requires that
  re-wiring plus a cold build of the big modules, beyond one session.

## Design choice for follow-up
Option A (recommended): keep the narrowing + add the dominance hypothesis to `finite_prime_term_normalization_statement`.
Option B: make `WeilFormSymbols` index sets per-test (larger; removes the law need).

## Captured diff (AnalyticCore, pre-revert)
```diff
diff --git a/ConnesWeilRH/Source/AnalyticCore.lean b/ConnesWeilRH/Source/AnalyticCore.lean
index a4c7fcd..96ddee9 100644
--- a/ConnesWeilRH/Source/AnalyticCore.lean
+++ b/ConnesWeilRH/Source/AnalyticCore.lean
@@ -7463,17 +7463,19 @@ It does NOT replace the legacy structure (that is the separate Step-2 flip); it
 is added alongside so existing consumers build unchanged.
 -/
 /-- A finite-prime support carrier whose exactness is stated for a single common
-test, not for all tests.  Forward (visible -> member) is kept; reverse is
-per-common. -/
+test, not for all tests.  Forward and reverse are both per-common
+(§7k): the old `∀ F` forward row is carrier-agnostically unsatisfiable; narrowed
+here so a compact-support common makes `globalIndexSet = {n | term n common ≠ 0}` a
+finite, satisfiable Finset. -/
 structure PerCommonSourceFinitePrimeSupport
     (A : SourceTestAlgebra) (E : SourceEvaluationData A) (common : A.Test) where
   globalIndexSet : Finset ℕ
   restrictedIndexSet : ℝ → Finset ℕ
   sourceVisibleGlobalIndex :
-    ∀ n : ℕ, ∀ F : A.Test, E.sourceFinitePrimeTerm n F ≠ 0 -> n ∈ globalIndexSet
+    ∀ n : ℕ, E.sourceFinitePrimeTerm n common ≠ 0 -> n ∈ globalIndexSet
   sourceVisibleRestrictedIndex :
-    ∀ lambda : ℝ, ∀ n : ℕ, ∀ F : A.Test,
-      E.sourceFinitePrimeTerm n F ≠ 0 -> 1 < n -> (n : ℝ) ≤ lambda ^ 2 ->
+    ∀ lambda : ℝ, ∀ n : ℕ,
+      E.sourceFinitePrimeTerm n common ≠ 0 -> 1 < n -> (n : ℝ) ≤ lambda ^ 2 ->
         n ∈ restrictedIndexSet lambda
   commonGlobalIndex :
     ∀ n : ℕ, n ∈ globalIndexSet -> E.sourceFinitePrimeTerm n common ≠ 0
@@ -7484,14 +7486,14 @@ structure PerCommonSourceFinitePrimeSupport
 
 namespace PerCommonSourceFinitePrimeSupport
 
-/-- Forward direction is unaffected by the common scoping. -/
+/-- Forward direction: a visible term of the per-common test `common` is a member
+(the narrow per-common property; the old `∀ F` forward is gone, §7k). -/
 theorem visible_mem
     {A : SourceTestAlgebra} {E : SourceEvaluationData A} {common : A.Test}
     (S : PerCommonSourceFinitePrimeSupport A E common)
-    (n : ℕ) : (∃ F : A.Test, E.sourceFinitePrimeTerm n F ≠ 0) ->
-      n ∈ S.globalIndexSet := by
-  intro ⟨F, h⟩
-  exact S.sourceVisibleGlobalIndex n F h
+    (n : ℕ) : E.sourceFinitePrimeTerm n common ≠ 0 ->
+      n ∈ S.globalIndexSet :=
+  S.sourceVisibleGlobalIndex n
 
 /-- Per-common reverse: membership implies `common`'s term is really nonzero
 (no `∀ F`, so no zero-element forced step). -/
@@ -7558,7 +7560,7 @@ theorem globalExact
     have hVisible := P.support.commonGlobalIndex n hn
     exact ⟨E.sourceFinitePrimeTerm_nonzero_primePower hVisible, hVisible⟩
   · intro hdata
-    exact P.support.sourceVisibleGlobalIndex n common hdata.2
+    exact P.support.sourceVisibleGlobalIndex n hdata.2
 
 /-- Per-common restricted exactness, same scoping. -/
 theorem restrictedExact
@@ -7577,7 +7579,7 @@ theorem restrictedExact
         hdata.2⟩
   · intro hdata
     exact
-      P.support.sourceVisibleRestrictedIndex lambda n common
+      P.support.sourceVisibleRestrictedIndex lambda n
         hdata.2.1 hdata.2.2.1 hdata.2.2.2
 
 def sourcePrimePowerIndex
@@ -7714,14 +7716,15 @@ theorem globalPrimeIndex_visible
     P.sourceAtomVisible n common :=
   ((P.globalExact n).1 hn).2
 
-/-- Forward: visible at ANY F -> member (kept ∀ F, per S2 保正向收反向). -/
+/-- Forward: visible at the `common` test -> member (per-common, §7k; the old
+`∀ F` forward is gone because it forced the finite Finset to contain every prime). -/
 theorem globalPrimeIndex_mem_of_primePower_visible
     {A : SourceTestAlgebra} {E : SourceEvaluationData A} {common : A.Test}
     (P : SourceFinitePrimeData A E common)
-    (F : A.Test) {n : ℕ}
-    (hPrime : IsPrimePow n) (hVisible : P.sourceAtomVisible n F) :
+    {n : ℕ}
+    (hPrime : IsPrimePow n) (hVisible : P.sourceAtomVisible n common) :
     n ∈ P.globalPrimeIndexSet :=
-  P.support.sourceVisibleGlobalIndex n F hVisible
+  P.support.sourceVisibleGlobalIndex n hVisible
 
 theorem sourceAtomVisible_primePower_index
     {A : SourceTestAlgebra} {E : SourceEvaluationData A} {common : A.Test}
@@ -7733,12 +7736,12 @@ theorem sourceAtomVisible_primePower_index
 theorem globalCoverage
     {A : SourceTestAlgebra} {E : SourceEvaluationData A} {common : A.Test}
     (P : SourceFinitePrimeData A E common)
-    (F : A.Test) (n : ℕ) :
-    P.sourceAtomVisible n F → n ∈ P.globalPrimeIndexSet := by
+    (n : ℕ) :
+    P.sourceAtomVisible n common → n ∈ P.globalPrimeIndexSet := by
   intro hVisible
   exact
-    P.globalPrimeIndex_mem_of_primePower_visible F
-      (P.sourceAtomVisible_primePower_index F hVisible) hVisible
+    P.globalPrimeIndex_mem_of_primePower_visible
+      (P.sourceAtomVisible_primePower_index common hVisible) hVisible
 
 theorem restrictedPrimeIndex_primePower
     {A : SourceTestAlgebra} {E : SourceEvaluationData A} {common : A.Test}
@@ -7787,21 +7790,20 @@ per-common support's forward restricted witness. -/
 theorem restrictedPrimeIndex_mem_of_primePower_visible_cutoff
     {A : SourceTestAlgebra} {E : SourceEvaluationData A} {common : A.Test}
     (P : SourceFinitePrimeData A E common)
-    (lambda : ℝ) (F : A.Test) {n : ℕ}
-    (hPrime : IsPrimePow n) (hVisible : P.sourceAtomVisible n F)
+    (lambda : ℝ) {n : ℕ}
+    (hPrime : IsPrimePow n) (hVisible : P.sourceAtomVisible n common)
     (hOne : 1 < n) (hCut : (n : ℝ) ≤ lambda ^ 2) :
     n ∈ P.restrictedPrimeIndexSet lambda :=
-  P.support.sourceVisibleRestrictedIndex lambda n F hVisible hOne hCut
+  P.support.sourceVisibleRestrictedIndex lambda n hVisible hOne hCut
 
 theorem restrictedCoverage
     {A : SourceTestAlgebra} {E : SourceEvaluationData A} {common : A.Test}
     (P : SourceFinitePrimeData A E common)
-    (lambda : ℝ) (hlambda : 1 < lambda)
-    (F : A.Test) (n : ℕ) :
-    P.sourceAtomVisible n F → 1 < n → (n : ℝ) ≤ lambda ^ 2 →
+    (lambda : ℝ) (hlambda : 1 < lambda) {n : ℕ} :
+    P.sourceAtomVisible n common → 1 < n → (n : ℝ) ≤ lambda ^ 2 →
       n ∈ P.restrictedPrimeIndexSet lambda := by
   intro hVisible hOne hCut
-  exact P.support.sourceVisibleRestrictedIndex lambda n F hVisible hOne hCut
+  exact P.support.sourceVisibleRestrictedIndex lambda n hVisible hOne hCut
 
 theorem finitePrimeTerm_convolutionStar
     {A : SourceTestAlgebra} {E : SourceEvaluationData A} {common : A.Test} (P : SourceFinitePrimeData A E common)
@@ -8000,31 +8002,37 @@ theorem toWeilFormSymbols_finitePrimeAtomVisible_primePower
 
 theorem toWeilFormSymbols_globalPrimeIndex_mem_of_primePower_visible
     {A : SourceTestAlgebra} (W : SourceWeilFormData A)
-    (F : TestFunction) {n : ℕ}
+    {n : ℕ}
     (hPrime : IsPrimePow n)
-    (hVisible : W.toWeilFormSymbols.finitePrimeAtomVisible n F) :
+    (hVisible : W.toWeilFormSymbols.finitePrimeAtomVisible n
+        (A.legacy.encode W.common)) :
     n ∈ W.toWeilFormSymbols.globalPrimeIndexSet :=
-  W.finitePrime.globalPrimeIndex_mem_of_primePower_visible
-    (A.legacy.decode F) hPrime hVisible
+  (toWeilFormSymbols_globalPrimeIndex_exact W n).mpr ⟨hPrime, hVisible⟩
 
 theorem toWeilFormSymbols_restrictedPrimeIndex_mem_of_primePower_visible_cutoff
     {A : SourceTestAlgebra} (W : SourceWeilFormData A)
-    (lambda : ℝ) (F : TestFunction) {n : ℕ}
+    (lambda : ℝ) {n : ℕ}
     (hPrime : IsPrimePow n)
-    (hVisible : W.toWeilFormSymbols.finitePrimeAtomVisible n F)
+    (hVisible : W.toWeilFormSymbols.finitePrimeAtomVisible n
+        (A.legacy.encode W.common))
     (hOne : 1 < n) (hCutoff : (n : ℝ) ≤ lambda ^ 2) :
     n ∈ W.toWeilFormSymbols.restrictedPrimeIndexSet lambda :=
-  W.finitePrime.restrictedPrimeIndex_mem_of_primePower_visible_cutoff
-    lambda (A.legacy.decode F) hPrime hVisible hOne hCutoff
+  (toWeilFormSymbols_restrictedPrimeIndex_exact W lambda n).mpr
+    ⟨hPrime, hVisible, hOne, hCutoff⟩
 
 theorem toWeilFormSymbols_restrictedPrimeIndex_mem_of_visible
     {A : SourceTestAlgebra} (W : SourceWeilFormData A)
-    (lambda : ℝ) (hlambda : 1 < lambda) (F : TestFunction) {n : ℕ}
-    (hVisible : W.toWeilFormSymbols.finitePrimeAtomVisible n F)
+    (lambda : ℝ) (hlambda : 1 < lambda) {n : ℕ}
+    (hVisible : W.toWeilFormSymbols.finitePrimeAtomVisible n
+        (A.legacy.encode W.common))
     (hOne : 1 < n) (hCutoff : (n : ℝ) ≤ lambda ^ 2) :
     n ∈ W.toWeilFormSymbols.restrictedPrimeIndexSet lambda :=
-  W.finitePrime.restrictedCoverage lambda hlambda
-    (A.legacy.decode F) n hVisible hOne hCutoff
+      W.finitePrime.restrictedCoverage lambda hlambda
+        (by
+          simpa [toWeilFormSymbols_finitePrimeAtomVisible,
+            SourceFinitePrimeData.sourceAtomVisible,
+            A.legacy.decode_encode W.common] using hVisible)
+        hOne hCutoff
 
 theorem finitePrimeTerm_convolutionStar
     {A : SourceTestAlgebra} (W : SourceWeilFormData A)
@@ -8086,7 +8094,12 @@ theorem qw_lambda_formula_statement
     W.evaluation.polePairing_eq_poleFunctional_convolutionSquare]
 
 theorem finite_prime_term_normalization_statement
-    {A : SourceTestAlgebra} (W : SourceWeilFormData A) :
+    {A : SourceTestAlgebra} (W : SourceWeilFormData A)
+    (hdom : ∀ f g : TestFunction, ∀ n : ℕ,
+      W.toWeilFormSymbols.finitePrimeAtomVisible n
+        (W.toWeilFormSymbols.convolutionStar f g) ->
+        W.toWeilFormSymbols.finitePrimeAtomVisible n
+          (A.legacy.encode W.common)) :
     WeilFormSymbols.FinitePrimeNormalizationStatement W.toWeilFormSymbols := by
   intro f g
   refine
@@ -8094,11 +8107,21 @@ theorem finite_prime_term_normalization_statement
       restrictedPrimeIndexCoverage := ?_
       finitePrimeTermNormalization := ?_ }
   · intro n hn
-    exact W.finitePrime.globalCoverage
-      (A.legacy.decode (W.toWeilFormSymbols.convolutionStar f g)) n hn
+    have hc : W.toWeilFormSymbols.finitePrimeAtomVisible n
+        (A.legacy.encode W.common) := hdom f g n hn
+    exact W.finitePrime.globalCoverage n
+      (by
+        simpa [toWeilFormSymbols_finitePrimeAtomVisible,
+          SourceFinitePrimeData.sourceAtomVisible,
+          A.legacy.decode_encode W.common] using hc)
   · intro lambda hlambda n hn hOne hCutoff
+    have hc : W.toWeilFormSymbols.finitePrimeAtomVisible n
+        (A.legacy.encode W.common) := hdom f g n hn
     exact W.finitePrime.restrictedCoverage lambda hlambda
-      (A.legacy.decode (W.toWeilFormSymbols.convolutionStar f g)) n hn
+      (by
+        simpa [toWeilFormSymbols_finitePrimeAtomVisible,
+          SourceFinitePrimeData.sourceAtomVisible,
+          A.legacy.decode_encode W.common] using hc)
       hOne hCutoff
   · intro n
     simpa [toWeilFormSymbols, SourceTestAlgebra.legacyConvolutionStar,

```