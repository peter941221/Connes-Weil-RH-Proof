/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Source.CCM24SupportWindowPoint

/-!
# Shared source analytic core

This module introduces the common source-facing analytic objects needed by the
CCM24, CCM25, and CC20 source-model discharges.  It deliberately coexists with
the current `TestFunction := Type` scaffold: the `LegacyTestEquiv` field
connects a genuine source test object to the old carrier, so downstream modules
can migrate one theorem row at a time instead of replacing every route type at
once.
-/

namespace ConnesWeilRH
namespace Source
namespace AnalyticCore

open scoped ArithmeticFunction

namespace SourceSupportWindowData

structure SourceSupportWindowSupportWindowMembershipCoreData
    {A : SourceTestAlgebra} (S : SourceSupportWindowData A)
    (f : A.Test) (I : S.Window)
    (supportWindowSet : Type)
    (supportWindowMembership : supportWindowSet → Prop) where
  supportWindowPointMembershipCore :
    SourceSupportWindowSupportWindowPointMembershipCoreData
      S f I supportWindowSet supportWindowMembership

namespace SourceSupportWindowSupportWindowMembershipCoreData

theorem supportWindowMembershipRealizesSupportInWindow
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} {I : S.Window}
    {supportSet : Type} {supportMembership : supportSet → Prop}
    {supportWindowSet : Type}
    {supportWindowMembership : supportWindowSet → Prop}
    {supportToWindow : supportSet → supportWindowSet}
    (D :
      SourceSupportWindowSupportWindowMembershipCoreData
        S f I supportWindowSet supportWindowMembership) :
    ∀ point : supportSet,
      supportMembership point →
        supportWindowMembership (supportToWindow point) →
          S.supportInWindow f I := by
  intro point _hSupport hWindow
  exact
    D.supportWindowPointMembershipCore
      |>.supportWindowPointRealizesSupportInWindow

end SourceSupportWindowSupportWindowMembershipCoreData

structure SourceSupportWindowSupportMembershipConcreteSourceCoreData
    {A : SourceTestAlgebra} (S : SourceSupportWindowData A)
    (f : A.Test) (I : S.Window)
    (supportSet : Type) (supportMembership : supportSet → Prop)
    (supportWindowSet : Type)
    (supportWindowMembership : supportWindowSet → Prop)
    (supportToWindow : supportSet → supportWindowSet)
    (realizationWitness :
      ∀ point : supportSet,
        supportMembership point →
          supportWindowMembership (supportToWindow point) → Type)
    (supportWindowSourceObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            realizationWitness point hSupport hWindow → Type)
    (sourceMembershipWitness :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              supportWindowSourceObject
                point hSupport hWindow hRealization → Type)
    (supportMembershipProofObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                sourceMembershipWitness
                  point hSupport hWindow hRealization hSource → Type)
    (supportMembershipEvidenceObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  supportMembershipProofObject
                    point hSupport hWindow hRealization hSource hMembership →
                    Type)
    (supportMembershipConcreteObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    supportMembershipEvidenceObject
                      point hSupport hWindow hRealization hSource
                      hMembership hProof → Type)
    (supportMembershipFinalObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    ∀ hEvidence :
                      supportMembershipEvidenceObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof,
                      supportMembershipConcreteObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof hEvidence → Type)
    (supportMembershipSourceNormalForm :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    ∀ hEvidence :
                      supportMembershipEvidenceObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof,
                      ∀ hConcrete :
                        supportMembershipConcreteObject
                          point hSupport hWindow hRealization hSource
                          hMembership hProof hEvidence,
                        supportMembershipFinalObject
                          point hSupport hWindow hRealization hSource
                          hMembership hProof hEvidence hConcrete → Type)
    (supportMembershipConcreteSourceData :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    ∀ hEvidence :
                      supportMembershipEvidenceObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof,
                      ∀ hConcrete :
                        supportMembershipConcreteObject
                          point hSupport hWindow hRealization hSource
                          hMembership hProof hEvidence,
                        ∀ hFinal :
                          supportMembershipFinalObject
                            point hSupport hWindow hRealization hSource
                            hMembership hProof hEvidence hConcrete,
                          supportMembershipSourceNormalForm
                            point hSupport hWindow hRealization hSource
                            hMembership hProof hEvidence hConcrete hFinal →
                            Type) where
  supportMembershipConcreteSourceDataFor :
    ∀ point : supportSet,
      ∀ hSupport : supportMembership point,
        ∀ hWindow :
          supportWindowMembership (supportToWindow point),
          ∀ hRealization :
            realizationWitness point hSupport hWindow,
            ∀ hSource :
              supportWindowSourceObject
                point hSupport hWindow hRealization,
              ∀ hMembership :
                sourceMembershipWitness
                  point hSupport hWindow hRealization hSource,
                ∀ hProof :
                  supportMembershipProofObject
                    point hSupport hWindow hRealization hSource hMembership,
                  ∀ hEvidence :
                    supportMembershipEvidenceObject
                      point hSupport hWindow hRealization hSource
                      hMembership hProof,
                    ∀ hConcrete :
                      supportMembershipConcreteObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof hEvidence,
                      ∀ hFinal :
                        supportMembershipFinalObject
                          point hSupport hWindow hRealization hSource
                          hMembership hProof hEvidence hConcrete,
                        ∀ hNormal :
                          supportMembershipSourceNormalForm
                            point hSupport hWindow hRealization hSource
                            hMembership hProof hEvidence hConcrete hFinal,
                          supportMembershipConcreteSourceData
                            point hSupport hWindow hRealization hSource
                            hMembership hProof hEvidence hConcrete hFinal
                            hNormal
  supportWindowMembershipCore :
    SourceSupportWindowSupportWindowMembershipCoreData
      S f I supportWindowSet supportWindowMembership

namespace SourceSupportWindowSupportMembershipConcreteSourceCoreData

theorem supportMembershipSourceNormalFormRealizesSupportInWindow
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} {I : S.Window}
    {supportSet : Type} {supportMembership : supportSet → Prop}
    {supportWindowSet : Type}
    {supportWindowMembership : supportWindowSet → Prop}
    {supportToWindow : supportSet → supportWindowSet}
    {realizationWitness :
      ∀ point : supportSet,
        supportMembership point →
          supportWindowMembership (supportToWindow point) → Type}
    {supportWindowSourceObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            realizationWitness point hSupport hWindow → Type}
    {sourceMembershipWitness :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              supportWindowSourceObject
                point hSupport hWindow hRealization → Type}
    {supportMembershipProofObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                sourceMembershipWitness
                  point hSupport hWindow hRealization hSource → Type}
    {supportMembershipEvidenceObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
          ∀ hRealization :
            realizationWitness point hSupport hWindow,
            ∀ hSource :
              supportWindowSourceObject
                point hSupport hWindow hRealization,
              ∀ hMembership :
                sourceMembershipWitness
                  point hSupport hWindow hRealization hSource,
                supportMembershipProofObject
                  point hSupport hWindow hRealization hSource hMembership →
                  Type}
    {supportMembershipConcreteObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
          ∀ hRealization :
            realizationWitness point hSupport hWindow,
          ∀ hSource :
            supportWindowSourceObject
              point hSupport hWindow hRealization,
          ∀ hMembership :
            sourceMembershipWitness
              point hSupport hWindow hRealization hSource,
          ∀ hProof :
            supportMembershipProofObject
              point hSupport hWindow hRealization hSource hMembership,
            supportMembershipEvidenceObject
              point hSupport hWindow hRealization hSource
              hMembership hProof → Type}
    {supportMembershipFinalObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
          ∀ hRealization :
            realizationWitness point hSupport hWindow,
          ∀ hSource :
            supportWindowSourceObject
              point hSupport hWindow hRealization,
          ∀ hMembership :
            sourceMembershipWitness
              point hSupport hWindow hRealization hSource,
          ∀ hProof :
            supportMembershipProofObject
              point hSupport hWindow hRealization hSource hMembership,
          ∀ hEvidence :
            supportMembershipEvidenceObject
              point hSupport hWindow hRealization hSource
              hMembership hProof,
            supportMembershipConcreteObject
              point hSupport hWindow hRealization hSource
              hMembership hProof hEvidence → Type}
    {supportMembershipSourceNormalForm :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
          ∀ hRealization :
            realizationWitness point hSupport hWindow,
          ∀ hSource :
            supportWindowSourceObject
              point hSupport hWindow hRealization,
          ∀ hMembership :
            sourceMembershipWitness
              point hSupport hWindow hRealization hSource,
          ∀ hProof :
            supportMembershipProofObject
              point hSupport hWindow hRealization hSource hMembership,
          ∀ hEvidence :
            supportMembershipEvidenceObject
              point hSupport hWindow hRealization hSource
              hMembership hProof,
          ∀ hConcrete :
            supportMembershipConcreteObject
              point hSupport hWindow hRealization hSource
              hMembership hProof hEvidence,
            supportMembershipFinalObject
              point hSupport hWindow hRealization hSource
              hMembership hProof hEvidence hConcrete → Type}
    {supportMembershipConcreteSourceData :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
          ∀ hRealization :
            realizationWitness point hSupport hWindow,
          ∀ hSource :
            supportWindowSourceObject
              point hSupport hWindow hRealization,
          ∀ hMembership :
            sourceMembershipWitness
              point hSupport hWindow hRealization hSource,
          ∀ hProof :
            supportMembershipProofObject
              point hSupport hWindow hRealization hSource hMembership,
          ∀ hEvidence :
            supportMembershipEvidenceObject
              point hSupport hWindow hRealization hSource
              hMembership hProof,
          ∀ hConcrete :
            supportMembershipConcreteObject
              point hSupport hWindow hRealization hSource
              hMembership hProof hEvidence,
          ∀ hFinal :
            supportMembershipFinalObject
              point hSupport hWindow hRealization hSource
              hMembership hProof hEvidence hConcrete,
            supportMembershipSourceNormalForm
              point hSupport hWindow hRealization hSource
              hMembership hProof hEvidence hConcrete hFinal → Type}
    (D :
      SourceSupportWindowSupportMembershipConcreteSourceCoreData
        S f I supportSet supportMembership supportWindowSet
        supportWindowMembership supportToWindow realizationWitness
        supportWindowSourceObject sourceMembershipWitness
        supportMembershipProofObject supportMembershipEvidenceObject
        supportMembershipConcreteObject supportMembershipFinalObject
        supportMembershipSourceNormalForm supportMembershipConcreteSourceData) :
    ∀ point : supportSet,
      ∀ hSupport : supportMembership point,
        ∀ hWindow :
          supportWindowMembership (supportToWindow point),
          ∀ hRealization :
            realizationWitness point hSupport hWindow,
            ∀ hSource :
              supportWindowSourceObject
                point hSupport hWindow hRealization,
              ∀ hMembership :
                sourceMembershipWitness
                  point hSupport hWindow hRealization hSource,
                ∀ hProof :
                  supportMembershipProofObject
                    point hSupport hWindow hRealization hSource hMembership,
                  ∀ hEvidence :
                    supportMembershipEvidenceObject
                      point hSupport hWindow hRealization hSource
                      hMembership hProof,
                    ∀ hConcrete :
                      supportMembershipConcreteObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof hEvidence,
                      ∀ hFinal :
                        supportMembershipFinalObject
                          point hSupport hWindow hRealization hSource
                          hMembership hProof hEvidence hConcrete,
                        supportMembershipSourceNormalForm
                          point hSupport hWindow hRealization hSource
                          hMembership hProof hEvidence hConcrete hFinal →
                          S.supportInWindow f I := by
  intro point hSupport hWindow hRealization hSource hMembership hProof
    hEvidence hConcrete hFinal hNormal
  exact
    D.supportWindowMembershipCore.supportWindowMembershipRealizesSupportInWindow
      point hSupport hWindow

end SourceSupportWindowSupportMembershipConcreteSourceCoreData

structure SourceSupportWindowSupportMembershipSourceNormalFormCoreData
    {A : SourceTestAlgebra} (S : SourceSupportWindowData A)
    (f : A.Test) (I : S.Window)
    (supportSet : Type) (supportMembership : supportSet → Prop)
    (supportWindowSet : Type)
    (supportWindowMembership : supportWindowSet → Prop)
    (supportToWindow : supportSet → supportWindowSet)
    (realizationWitness :
      ∀ point : supportSet,
        supportMembership point →
          supportWindowMembership (supportToWindow point) → Type)
    (supportWindowSourceObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            realizationWitness point hSupport hWindow → Type)
    (sourceMembershipWitness :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              supportWindowSourceObject
                point hSupport hWindow hRealization → Type)
    (supportMembershipProofObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                sourceMembershipWitness
                  point hSupport hWindow hRealization hSource → Type)
    (supportMembershipEvidenceObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  supportMembershipProofObject
                    point hSupport hWindow hRealization hSource hMembership →
                    Type)
    (supportMembershipConcreteObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    supportMembershipEvidenceObject
                      point hSupport hWindow hRealization hSource
                      hMembership hProof → Type)
    (supportMembershipFinalObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    ∀ hEvidence :
                      supportMembershipEvidenceObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof,
                      supportMembershipConcreteObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof hEvidence → Type)
    (supportMembershipSourceNormalForm :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    ∀ hEvidence :
                      supportMembershipEvidenceObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof,
                      ∀ hConcrete :
                        supportMembershipConcreteObject
                          point hSupport hWindow hRealization hSource
                          hMembership hProof hEvidence,
                        supportMembershipFinalObject
                          point hSupport hWindow hRealization hSource
                          hMembership hProof hEvidence hConcrete → Type) where
  supportMembershipSourceNormalFormFor :
    ∀ point : supportSet,
      ∀ hSupport : supportMembership point,
        ∀ hWindow :
          supportWindowMembership (supportToWindow point),
          ∀ hRealization :
            realizationWitness point hSupport hWindow,
            ∀ hSource :
              supportWindowSourceObject
                point hSupport hWindow hRealization,
              ∀ hMembership :
                sourceMembershipWitness
                  point hSupport hWindow hRealization hSource,
                ∀ hProof :
                  supportMembershipProofObject
                    point hSupport hWindow hRealization hSource hMembership,
                  ∀ hEvidence :
                    supportMembershipEvidenceObject
                      point hSupport hWindow hRealization hSource
                      hMembership hProof,
                    ∀ hConcrete :
                      supportMembershipConcreteObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof hEvidence,
                      ∀ hFinal :
                        supportMembershipFinalObject
                          point hSupport hWindow hRealization hSource
                          hMembership hProof hEvidence hConcrete,
                        supportMembershipSourceNormalForm
                          point hSupport hWindow hRealization hSource
                          hMembership hProof hEvidence hConcrete hFinal
  supportMembershipConcreteSourceData :
    ∀ point : supportSet,
      ∀ hSupport : supportMembership point,
        ∀ hWindow :
          supportWindowMembership (supportToWindow point),
          ∀ hRealization :
            realizationWitness point hSupport hWindow,
            ∀ hSource :
              supportWindowSourceObject
                point hSupport hWindow hRealization,
              ∀ hMembership :
                sourceMembershipWitness
                  point hSupport hWindow hRealization hSource,
                ∀ hProof :
                  supportMembershipProofObject
                    point hSupport hWindow hRealization hSource hMembership,
                  ∀ hEvidence :
                    supportMembershipEvidenceObject
                      point hSupport hWindow hRealization hSource
                      hMembership hProof,
                    ∀ hConcrete :
                      supportMembershipConcreteObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof hEvidence,
                      ∀ hFinal :
                        supportMembershipFinalObject
                          point hSupport hWindow hRealization hSource
                          hMembership hProof hEvidence hConcrete,
                        supportMembershipSourceNormalForm
                          point hSupport hWindow hRealization hSource
                          hMembership hProof hEvidence hConcrete hFinal →
                          Type
  supportMembershipConcreteSourceCore :
    SourceSupportWindowSupportMembershipConcreteSourceCoreData
      S f I supportSet supportMembership supportWindowSet
      supportWindowMembership supportToWindow realizationWitness
      supportWindowSourceObject sourceMembershipWitness
      supportMembershipProofObject supportMembershipEvidenceObject
      supportMembershipConcreteObject supportMembershipFinalObject
      supportMembershipSourceNormalForm supportMembershipConcreteSourceData

namespace SourceSupportWindowSupportMembershipSourceNormalFormCoreData

theorem supportMembershipFinalRealizesSupportInWindow
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} {I : S.Window}
    {supportSet : Type} {supportMembership : supportSet → Prop}
    {supportWindowSet : Type}
    {supportWindowMembership : supportWindowSet → Prop}
    {supportToWindow : supportSet → supportWindowSet}
    {realizationWitness :
      ∀ point : supportSet,
        supportMembership point →
          supportWindowMembership (supportToWindow point) → Type}
    {supportWindowSourceObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            realizationWitness point hSupport hWindow → Type}
    {sourceMembershipWitness :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              supportWindowSourceObject
                point hSupport hWindow hRealization → Type}
    {supportMembershipProofObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                sourceMembershipWitness
                  point hSupport hWindow hRealization hSource → Type}
    {supportMembershipEvidenceObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
          ∀ hRealization :
            realizationWitness point hSupport hWindow,
            ∀ hSource :
              supportWindowSourceObject
                point hSupport hWindow hRealization,
              ∀ hMembership :
                sourceMembershipWitness
                  point hSupport hWindow hRealization hSource,
                supportMembershipProofObject
                  point hSupport hWindow hRealization hSource hMembership →
                  Type}
    {supportMembershipConcreteObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
          ∀ hRealization :
            realizationWitness point hSupport hWindow,
          ∀ hSource :
            supportWindowSourceObject
              point hSupport hWindow hRealization,
          ∀ hMembership :
            sourceMembershipWitness
              point hSupport hWindow hRealization hSource,
          ∀ hProof :
            supportMembershipProofObject
              point hSupport hWindow hRealization hSource hMembership,
            supportMembershipEvidenceObject
              point hSupport hWindow hRealization hSource
              hMembership hProof → Type}
    {supportMembershipFinalObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
          ∀ hRealization :
            realizationWitness point hSupport hWindow,
          ∀ hSource :
            supportWindowSourceObject
              point hSupport hWindow hRealization,
          ∀ hMembership :
            sourceMembershipWitness
              point hSupport hWindow hRealization hSource,
          ∀ hProof :
            supportMembershipProofObject
              point hSupport hWindow hRealization hSource hMembership,
          ∀ hEvidence :
            supportMembershipEvidenceObject
              point hSupport hWindow hRealization hSource
              hMembership hProof,
            supportMembershipConcreteObject
              point hSupport hWindow hRealization hSource
              hMembership hProof hEvidence → Type}
    {supportMembershipSourceNormalForm :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
          ∀ hRealization :
            realizationWitness point hSupport hWindow,
          ∀ hSource :
            supportWindowSourceObject
              point hSupport hWindow hRealization,
          ∀ hMembership :
            sourceMembershipWitness
              point hSupport hWindow hRealization hSource,
          ∀ hProof :
            supportMembershipProofObject
              point hSupport hWindow hRealization hSource hMembership,
          ∀ hEvidence :
            supportMembershipEvidenceObject
              point hSupport hWindow hRealization hSource
              hMembership hProof,
          ∀ hConcrete :
            supportMembershipConcreteObject
              point hSupport hWindow hRealization hSource
              hMembership hProof hEvidence,
            supportMembershipFinalObject
              point hSupport hWindow hRealization hSource
              hMembership hProof hEvidence hConcrete → Type}
    (D :
      SourceSupportWindowSupportMembershipSourceNormalFormCoreData
        S f I supportSet supportMembership supportWindowSet
        supportWindowMembership supportToWindow realizationWitness
        supportWindowSourceObject sourceMembershipWitness
        supportMembershipProofObject supportMembershipEvidenceObject
        supportMembershipConcreteObject supportMembershipFinalObject
        supportMembershipSourceNormalForm) :
    ∀ point : supportSet,
      ∀ hSupport : supportMembership point,
        ∀ hWindow :
          supportWindowMembership (supportToWindow point),
          ∀ hRealization :
            realizationWitness point hSupport hWindow,
            ∀ hSource :
              supportWindowSourceObject
                point hSupport hWindow hRealization,
              ∀ hMembership :
                sourceMembershipWitness
                  point hSupport hWindow hRealization hSource,
                ∀ hProof :
                  supportMembershipProofObject
                    point hSupport hWindow hRealization hSource hMembership,
                  ∀ hEvidence :
                    supportMembershipEvidenceObject
                      point hSupport hWindow hRealization hSource
                      hMembership hProof,
                    ∀ hConcrete :
                      supportMembershipConcreteObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof hEvidence,
                      supportMembershipFinalObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof hEvidence hConcrete →
                        S.supportInWindow f I := by
  intro point hSupport hWindow hRealization hSource hMembership hProof
    hEvidence hConcrete hFinal
  exact
    D.supportMembershipConcreteSourceCore.supportMembershipSourceNormalFormRealizesSupportInWindow
      point hSupport hWindow hRealization hSource hMembership hProof hEvidence
      hConcrete hFinal
      (D.supportMembershipSourceNormalFormFor
        point hSupport hWindow hRealization hSource hMembership hProof
        hEvidence hConcrete hFinal)

end SourceSupportWindowSupportMembershipSourceNormalFormCoreData

structure SourceSupportWindowSupportMembershipFinalCoreData
    {A : SourceTestAlgebra} (S : SourceSupportWindowData A)
    (f : A.Test) (I : S.Window)
    (supportSet : Type) (supportMembership : supportSet → Prop)
    (supportWindowSet : Type)
    (supportWindowMembership : supportWindowSet → Prop)
    (supportToWindow : supportSet → supportWindowSet)
    (realizationWitness :
      ∀ point : supportSet,
        supportMembership point →
          supportWindowMembership (supportToWindow point) → Type)
    (supportWindowSourceObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            realizationWitness point hSupport hWindow → Type)
    (sourceMembershipWitness :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              supportWindowSourceObject
                point hSupport hWindow hRealization → Type)
    (supportMembershipProofObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                sourceMembershipWitness
                  point hSupport hWindow hRealization hSource → Type)
    (supportMembershipEvidenceObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  supportMembershipProofObject
                    point hSupport hWindow hRealization hSource hMembership →
                    Type)
    (supportMembershipConcreteObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    supportMembershipEvidenceObject
                      point hSupport hWindow hRealization hSource
                      hMembership hProof → Type)
    (supportMembershipFinalObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    ∀ hEvidence :
                      supportMembershipEvidenceObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof,
                      supportMembershipConcreteObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof hEvidence → Type) where
  supportMembershipFinalFor :
    ∀ point : supportSet,
      ∀ hSupport : supportMembership point,
        ∀ hWindow :
          supportWindowMembership (supportToWindow point),
          ∀ hRealization :
            realizationWitness point hSupport hWindow,
            ∀ hSource :
              supportWindowSourceObject
                point hSupport hWindow hRealization,
              ∀ hMembership :
                sourceMembershipWitness
                  point hSupport hWindow hRealization hSource,
                ∀ hProof :
                  supportMembershipProofObject
                    point hSupport hWindow hRealization hSource hMembership,
                  ∀ hEvidence :
                    supportMembershipEvidenceObject
                      point hSupport hWindow hRealization hSource
                      hMembership hProof,
                    ∀ hConcrete :
                      supportMembershipConcreteObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof hEvidence,
                      supportMembershipFinalObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof hEvidence hConcrete
  supportMembershipSourceNormalForm :
    ∀ point : supportSet,
      ∀ hSupport : supportMembership point,
        ∀ hWindow :
          supportWindowMembership (supportToWindow point),
          ∀ hRealization :
            realizationWitness point hSupport hWindow,
            ∀ hSource :
              supportWindowSourceObject
                point hSupport hWindow hRealization,
              ∀ hMembership :
                sourceMembershipWitness
                  point hSupport hWindow hRealization hSource,
                ∀ hProof :
                  supportMembershipProofObject
                    point hSupport hWindow hRealization hSource hMembership,
                  ∀ hEvidence :
                    supportMembershipEvidenceObject
                      point hSupport hWindow hRealization hSource
                      hMembership hProof,
                    ∀ hConcrete :
                      supportMembershipConcreteObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof hEvidence,
                      supportMembershipFinalObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof hEvidence hConcrete → Type
  supportMembershipSourceNormalFormCore :
    SourceSupportWindowSupportMembershipSourceNormalFormCoreData
      S f I supportSet supportMembership supportWindowSet
      supportWindowMembership supportToWindow realizationWitness
      supportWindowSourceObject sourceMembershipWitness
      supportMembershipProofObject supportMembershipEvidenceObject
      supportMembershipConcreteObject supportMembershipFinalObject
      supportMembershipSourceNormalForm

namespace SourceSupportWindowSupportMembershipFinalCoreData

theorem supportMembershipConcreteRealizesSupportInWindow
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} {I : S.Window}
    {supportSet : Type} {supportMembership : supportSet → Prop}
    {supportWindowSet : Type}
    {supportWindowMembership : supportWindowSet → Prop}
    {supportToWindow : supportSet → supportWindowSet}
    {realizationWitness :
      ∀ point : supportSet,
        supportMembership point →
          supportWindowMembership (supportToWindow point) → Type}
    {supportWindowSourceObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            realizationWitness point hSupport hWindow → Type}
    {sourceMembershipWitness :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              supportWindowSourceObject
                point hSupport hWindow hRealization → Type}
    {supportMembershipProofObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                sourceMembershipWitness
                  point hSupport hWindow hRealization hSource → Type}
    {supportMembershipEvidenceObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
          ∀ hRealization :
            realizationWitness point hSupport hWindow,
            ∀ hSource :
              supportWindowSourceObject
                point hSupport hWindow hRealization,
              ∀ hMembership :
                sourceMembershipWitness
                  point hSupport hWindow hRealization hSource,
                supportMembershipProofObject
                  point hSupport hWindow hRealization hSource hMembership →
                  Type}
    {supportMembershipConcreteObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
          ∀ hRealization :
            realizationWitness point hSupport hWindow,
          ∀ hSource :
            supportWindowSourceObject
              point hSupport hWindow hRealization,
          ∀ hMembership :
            sourceMembershipWitness
              point hSupport hWindow hRealization hSource,
          ∀ hProof :
            supportMembershipProofObject
              point hSupport hWindow hRealization hSource hMembership,
            supportMembershipEvidenceObject
              point hSupport hWindow hRealization hSource
              hMembership hProof → Type}
    {supportMembershipFinalObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
          ∀ hRealization :
            realizationWitness point hSupport hWindow,
          ∀ hSource :
            supportWindowSourceObject
              point hSupport hWindow hRealization,
          ∀ hMembership :
            sourceMembershipWitness
              point hSupport hWindow hRealization hSource,
          ∀ hProof :
            supportMembershipProofObject
              point hSupport hWindow hRealization hSource hMembership,
          ∀ hEvidence :
            supportMembershipEvidenceObject
              point hSupport hWindow hRealization hSource
              hMembership hProof,
            supportMembershipConcreteObject
              point hSupport hWindow hRealization hSource
              hMembership hProof hEvidence → Type}
    (D :
      SourceSupportWindowSupportMembershipFinalCoreData
        S f I supportSet supportMembership supportWindowSet
        supportWindowMembership supportToWindow realizationWitness
        supportWindowSourceObject sourceMembershipWitness
        supportMembershipProofObject supportMembershipEvidenceObject
        supportMembershipConcreteObject supportMembershipFinalObject) :
    ∀ point : supportSet,
      ∀ hSupport : supportMembership point,
        ∀ hWindow :
          supportWindowMembership (supportToWindow point),
          ∀ hRealization :
            realizationWitness point hSupport hWindow,
            ∀ hSource :
              supportWindowSourceObject
                point hSupport hWindow hRealization,
              ∀ hMembership :
                sourceMembershipWitness
                  point hSupport hWindow hRealization hSource,
                ∀ hProof :
                  supportMembershipProofObject
                    point hSupport hWindow hRealization hSource hMembership,
                  ∀ hEvidence :
                    supportMembershipEvidenceObject
                      point hSupport hWindow hRealization hSource
                      hMembership hProof,
                    supportMembershipConcreteObject
                      point hSupport hWindow hRealization hSource
                      hMembership hProof hEvidence →
                      S.supportInWindow f I := by
  intro point hSupport hWindow hRealization hSource hMembership hProof
    hEvidence hConcrete
  exact
    D.supportMembershipSourceNormalFormCore.supportMembershipFinalRealizesSupportInWindow
      point hSupport hWindow hRealization hSource hMembership hProof hEvidence
      hConcrete
      (D.supportMembershipFinalFor
        point hSupport hWindow hRealization hSource hMembership hProof
        hEvidence hConcrete)

end SourceSupportWindowSupportMembershipFinalCoreData

structure SourceSupportWindowSupportMembershipConcreteCoreData
    {A : SourceTestAlgebra} (S : SourceSupportWindowData A)
    (f : A.Test) (I : S.Window)
    (supportSet : Type) (supportMembership : supportSet → Prop)
    (supportWindowSet : Type)
    (supportWindowMembership : supportWindowSet → Prop)
    (supportToWindow : supportSet → supportWindowSet)
    (realizationWitness :
      ∀ point : supportSet,
        supportMembership point →
          supportWindowMembership (supportToWindow point) → Type)
    (supportWindowSourceObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            realizationWitness point hSupport hWindow → Type)
    (sourceMembershipWitness :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              supportWindowSourceObject
                point hSupport hWindow hRealization → Type)
    (supportMembershipProofObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                sourceMembershipWitness
                  point hSupport hWindow hRealization hSource → Type)
    (supportMembershipEvidenceObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  supportMembershipProofObject
                    point hSupport hWindow hRealization hSource hMembership →
                    Type)
    (supportMembershipConcreteObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    supportMembershipEvidenceObject
                      point hSupport hWindow hRealization hSource
                      hMembership hProof → Type) where
  supportMembershipConcreteFor :
    ∀ point : supportSet,
      ∀ hSupport : supportMembership point,
        ∀ hWindow :
          supportWindowMembership (supportToWindow point),
          ∀ hRealization :
            realizationWitness point hSupport hWindow,
            ∀ hSource :
              supportWindowSourceObject
                point hSupport hWindow hRealization,
              ∀ hMembership :
                sourceMembershipWitness
                  point hSupport hWindow hRealization hSource,
                ∀ hProof :
                  supportMembershipProofObject
                    point hSupport hWindow hRealization hSource hMembership,
                  ∀ hEvidence :
                    supportMembershipEvidenceObject
                      point hSupport hWindow hRealization hSource
                      hMembership hProof,
                    supportMembershipConcreteObject
                      point hSupport hWindow hRealization hSource
                      hMembership hProof hEvidence
  supportMembershipFinalObject :
    ∀ point : supportSet,
      ∀ hSupport : supportMembership point,
        ∀ hWindow :
          supportWindowMembership (supportToWindow point),
          ∀ hRealization :
            realizationWitness point hSupport hWindow,
            ∀ hSource :
              supportWindowSourceObject
                point hSupport hWindow hRealization,
              ∀ hMembership :
                sourceMembershipWitness
                  point hSupport hWindow hRealization hSource,
                ∀ hProof :
                  supportMembershipProofObject
                    point hSupport hWindow hRealization hSource hMembership,
                  ∀ hEvidence :
                    supportMembershipEvidenceObject
                      point hSupport hWindow hRealization hSource
                      hMembership hProof,
                    supportMembershipConcreteObject
                      point hSupport hWindow hRealization hSource
                      hMembership hProof hEvidence → Type
  supportMembershipFinalCore :
    SourceSupportWindowSupportMembershipFinalCoreData
      S f I supportSet supportMembership supportWindowSet
      supportWindowMembership supportToWindow realizationWitness
      supportWindowSourceObject sourceMembershipWitness
      supportMembershipProofObject supportMembershipEvidenceObject
      supportMembershipConcreteObject supportMembershipFinalObject

namespace SourceSupportWindowSupportMembershipConcreteCoreData

theorem supportMembershipEvidenceRealizesSupportInWindow
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} {I : S.Window}
    {supportSet : Type} {supportMembership : supportSet → Prop}
    {supportWindowSet : Type}
    {supportWindowMembership : supportWindowSet → Prop}
    {supportToWindow : supportSet → supportWindowSet}
    {realizationWitness :
      ∀ point : supportSet,
        supportMembership point →
          supportWindowMembership (supportToWindow point) → Type}
    {supportWindowSourceObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            realizationWitness point hSupport hWindow → Type}
    {sourceMembershipWitness :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              supportWindowSourceObject
                point hSupport hWindow hRealization → Type}
    {supportMembershipProofObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                sourceMembershipWitness
                  point hSupport hWindow hRealization hSource → Type}
    {supportMembershipEvidenceObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
          ∀ hRealization :
            realizationWitness point hSupport hWindow,
            ∀ hSource :
              supportWindowSourceObject
                point hSupport hWindow hRealization,
              ∀ hMembership :
                sourceMembershipWitness
                  point hSupport hWindow hRealization hSource,
                supportMembershipProofObject
                  point hSupport hWindow hRealization hSource hMembership →
                  Type}
    {supportMembershipConcreteObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
          ∀ hRealization :
            realizationWitness point hSupport hWindow,
          ∀ hSource :
            supportWindowSourceObject
              point hSupport hWindow hRealization,
          ∀ hMembership :
            sourceMembershipWitness
              point hSupport hWindow hRealization hSource,
          ∀ hProof :
            supportMembershipProofObject
              point hSupport hWindow hRealization hSource hMembership,
            supportMembershipEvidenceObject
              point hSupport hWindow hRealization hSource
              hMembership hProof → Type}
    (D :
      SourceSupportWindowSupportMembershipConcreteCoreData
        S f I supportSet supportMembership supportWindowSet
        supportWindowMembership supportToWindow realizationWitness
        supportWindowSourceObject sourceMembershipWitness
        supportMembershipProofObject supportMembershipEvidenceObject
        supportMembershipConcreteObject) :
    ∀ point : supportSet,
      ∀ hSupport : supportMembership point,
        ∀ hWindow :
          supportWindowMembership (supportToWindow point),
          ∀ hRealization :
            realizationWitness point hSupport hWindow,
            ∀ hSource :
              supportWindowSourceObject
                point hSupport hWindow hRealization,
              ∀ hMembership :
                sourceMembershipWitness
                  point hSupport hWindow hRealization hSource,
                ∀ hProof :
                  supportMembershipProofObject
                    point hSupport hWindow hRealization hSource hMembership,
                  supportMembershipEvidenceObject
                    point hSupport hWindow hRealization hSource
                    hMembership hProof →
                    S.supportInWindow f I := by
  intro point hSupport hWindow hRealization hSource hMembership hProof hEvidence
  exact
    D.supportMembershipFinalCore.supportMembershipConcreteRealizesSupportInWindow
      point hSupport hWindow hRealization hSource hMembership hProof hEvidence
      (D.supportMembershipConcreteFor
        point hSupport hWindow hRealization hSource hMembership hProof
        hEvidence)

end SourceSupportWindowSupportMembershipConcreteCoreData

structure SourceSupportWindowSupportMembershipEvidenceCoreData
    {A : SourceTestAlgebra} (S : SourceSupportWindowData A)
    (f : A.Test) (I : S.Window)
    (supportSet : Type) (supportMembership : supportSet → Prop)
    (supportWindowSet : Type)
    (supportWindowMembership : supportWindowSet → Prop)
    (supportToWindow : supportSet → supportWindowSet)
    (realizationWitness :
      ∀ point : supportSet,
        supportMembership point →
          supportWindowMembership (supportToWindow point) → Type)
    (supportWindowSourceObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            realizationWitness point hSupport hWindow → Type)
    (sourceMembershipWitness :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              supportWindowSourceObject
                point hSupport hWindow hRealization → Type)
    (supportMembershipProofObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                sourceMembershipWitness
                  point hSupport hWindow hRealization hSource → Type)
    (supportMembershipEvidenceObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  supportMembershipProofObject
                    point hSupport hWindow hRealization hSource hMembership →
                    Type) where
  supportMembershipEvidenceFor :
    ∀ point : supportSet,
      ∀ hSupport : supportMembership point,
        ∀ hWindow :
          supportWindowMembership (supportToWindow point),
          ∀ hRealization :
            realizationWitness point hSupport hWindow,
            ∀ hSource :
              supportWindowSourceObject
                point hSupport hWindow hRealization,
              ∀ hMembership :
                sourceMembershipWitness
                  point hSupport hWindow hRealization hSource,
                ∀ hProof :
                  supportMembershipProofObject
                    point hSupport hWindow hRealization hSource hMembership,
                  supportMembershipEvidenceObject
                    point hSupport hWindow hRealization hSource
                    hMembership hProof
  supportMembershipConcreteObject :
    ∀ point : supportSet,
      ∀ hSupport : supportMembership point,
        ∀ hWindow :
          supportWindowMembership (supportToWindow point),
          ∀ hRealization :
            realizationWitness point hSupport hWindow,
            ∀ hSource :
              supportWindowSourceObject
                point hSupport hWindow hRealization,
              ∀ hMembership :
                sourceMembershipWitness
                  point hSupport hWindow hRealization hSource,
                ∀ hProof :
                  supportMembershipProofObject
                    point hSupport hWindow hRealization hSource hMembership,
                  supportMembershipEvidenceObject
                    point hSupport hWindow hRealization hSource
                    hMembership hProof → Type
  supportMembershipConcreteCore :
    SourceSupportWindowSupportMembershipConcreteCoreData
      S f I supportSet supportMembership supportWindowSet
      supportWindowMembership supportToWindow realizationWitness
      supportWindowSourceObject sourceMembershipWitness
      supportMembershipProofObject supportMembershipEvidenceObject
      supportMembershipConcreteObject

namespace SourceSupportWindowSupportMembershipEvidenceCoreData

theorem supportMembershipProofRealizesSupportInWindow
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} {I : S.Window}
    {supportSet : Type} {supportMembership : supportSet → Prop}
    {supportWindowSet : Type}
    {supportWindowMembership : supportWindowSet → Prop}
    {supportToWindow : supportSet → supportWindowSet}
    {realizationWitness :
      ∀ point : supportSet,
        supportMembership point →
          supportWindowMembership (supportToWindow point) → Type}
    {supportWindowSourceObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            realizationWitness point hSupport hWindow → Type}
    {sourceMembershipWitness :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              supportWindowSourceObject
                point hSupport hWindow hRealization → Type}
    {supportMembershipProofObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                sourceMembershipWitness
                  point hSupport hWindow hRealization hSource → Type}
    {supportMembershipEvidenceObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
          ∀ hRealization :
            realizationWitness point hSupport hWindow,
            ∀ hSource :
              supportWindowSourceObject
                point hSupport hWindow hRealization,
              ∀ hMembership :
                sourceMembershipWitness
                  point hSupport hWindow hRealization hSource,
                supportMembershipProofObject
                  point hSupport hWindow hRealization hSource hMembership →
                  Type}
    (D :
      SourceSupportWindowSupportMembershipEvidenceCoreData
        S f I supportSet supportMembership supportWindowSet
        supportWindowMembership supportToWindow realizationWitness
        supportWindowSourceObject sourceMembershipWitness
        supportMembershipProofObject supportMembershipEvidenceObject) :
    ∀ point : supportSet,
      ∀ hSupport : supportMembership point,
        ∀ hWindow :
          supportWindowMembership (supportToWindow point),
          ∀ hRealization :
            realizationWitness point hSupport hWindow,
            ∀ hSource :
              supportWindowSourceObject
                point hSupport hWindow hRealization,
              ∀ hMembership :
                sourceMembershipWitness
                  point hSupport hWindow hRealization hSource,
                supportMembershipProofObject
                  point hSupport hWindow hRealization hSource hMembership →
                  S.supportInWindow f I := by
  intro point hSupport hWindow hRealization hSource hMembership hProof
  exact
    D.supportMembershipConcreteCore.supportMembershipEvidenceRealizesSupportInWindow
      point hSupport hWindow hRealization hSource hMembership hProof
      (D.supportMembershipEvidenceFor
        point hSupport hWindow hRealization hSource hMembership hProof)

end SourceSupportWindowSupportMembershipEvidenceCoreData

structure SourceSupportWindowSupportMembershipProofCoreData
    {A : SourceTestAlgebra} (S : SourceSupportWindowData A)
    (f : A.Test) (I : S.Window)
    (supportSet : Type) (supportMembership : supportSet → Prop)
    (supportWindowSet : Type)
    (supportWindowMembership : supportWindowSet → Prop)
    (supportToWindow : supportSet → supportWindowSet)
    (realizationWitness :
      ∀ point : supportSet,
        supportMembership point →
          supportWindowMembership (supportToWindow point) → Type)
    (supportWindowSourceObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            realizationWitness point hSupport hWindow → Type)
    (sourceMembershipWitness :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              supportWindowSourceObject
                point hSupport hWindow hRealization → Type)
    (supportMembershipProofObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                sourceMembershipWitness
                  point hSupport hWindow hRealization hSource → Type) where
  supportMembershipProofFor :
    ∀ point : supportSet,
      ∀ hSupport : supportMembership point,
        ∀ hWindow :
          supportWindowMembership (supportToWindow point),
          ∀ hRealization :
            realizationWitness point hSupport hWindow,
            ∀ hSource :
              supportWindowSourceObject
                point hSupport hWindow hRealization,
              ∀ hMembership :
                sourceMembershipWitness
                  point hSupport hWindow hRealization hSource,
                supportMembershipProofObject
                  point hSupport hWindow hRealization hSource hMembership
  supportMembershipEvidenceObject :
    ∀ point : supportSet,
      ∀ hSupport : supportMembership point,
        ∀ hWindow :
          supportWindowMembership (supportToWindow point),
          ∀ hRealization :
            realizationWitness point hSupport hWindow,
            ∀ hSource :
              supportWindowSourceObject
                point hSupport hWindow hRealization,
              ∀ hMembership :
                sourceMembershipWitness
                  point hSupport hWindow hRealization hSource,
                supportMembershipProofObject
                  point hSupport hWindow hRealization hSource hMembership →
                  Type
  supportMembershipEvidenceCore :
    SourceSupportWindowSupportMembershipEvidenceCoreData
      S f I supportSet supportMembership supportWindowSet
      supportWindowMembership supportToWindow realizationWitness
      supportWindowSourceObject sourceMembershipWitness
      supportMembershipProofObject supportMembershipEvidenceObject

namespace SourceSupportWindowSupportMembershipProofCoreData

theorem sourceMembershipRealizesSupportInWindow
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} {I : S.Window}
    {supportSet : Type} {supportMembership : supportSet → Prop}
    {supportWindowSet : Type}
    {supportWindowMembership : supportWindowSet → Prop}
    {supportToWindow : supportSet → supportWindowSet}
    {realizationWitness :
      ∀ point : supportSet,
        supportMembership point →
          supportWindowMembership (supportToWindow point) → Type}
    {supportWindowSourceObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            realizationWitness point hSupport hWindow → Type}
    {sourceMembershipWitness :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              supportWindowSourceObject
                point hSupport hWindow hRealization → Type}
    {supportMembershipProofObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
          ∀ hRealization :
            realizationWitness point hSupport hWindow,
            ∀ hSource :
              supportWindowSourceObject
                point hSupport hWindow hRealization,
              sourceMembershipWitness
                point hSupport hWindow hRealization hSource → Type}
    (D :
      SourceSupportWindowSupportMembershipProofCoreData
        S f I supportSet supportMembership supportWindowSet
        supportWindowMembership supportToWindow realizationWitness
        supportWindowSourceObject sourceMembershipWitness
        supportMembershipProofObject) :
    ∀ point : supportSet,
      ∀ hSupport : supportMembership point,
        ∀ hWindow :
          supportWindowMembership (supportToWindow point),
          ∀ hRealization :
            realizationWitness point hSupport hWindow,
            ∀ hSource :
              supportWindowSourceObject
                point hSupport hWindow hRealization,
              sourceMembershipWitness
                point hSupport hWindow hRealization hSource →
                S.supportInWindow f I := by
  intro point hSupport hWindow hRealization hSource hMembership
  exact
    D.supportMembershipEvidenceCore.supportMembershipProofRealizesSupportInWindow
      point hSupport hWindow hRealization hSource hMembership
      (D.supportMembershipProofFor
        point hSupport hWindow hRealization hSource hMembership)

end SourceSupportWindowSupportMembershipProofCoreData

structure SourceSupportWindowSourceMembershipCoreData
    {A : SourceTestAlgebra} (S : SourceSupportWindowData A)
    (f : A.Test) (I : S.Window)
    (supportSet : Type) (supportMembership : supportSet → Prop)
    (supportWindowSet : Type)
    (supportWindowMembership : supportWindowSet → Prop)
    (supportToWindow : supportSet → supportWindowSet)
    (realizationWitness :
      ∀ point : supportSet,
        supportMembership point →
          supportWindowMembership (supportToWindow point) → Type)
    (supportWindowSourceObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            realizationWitness point hSupport hWindow → Type)
    (sourceMembershipWitness :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              supportWindowSourceObject
                point hSupport hWindow hRealization → Type) where
  sourceMembershipWitnessFor :
    ∀ point : supportSet,
      ∀ hSupport : supportMembership point,
        ∀ hWindow :
          supportWindowMembership (supportToWindow point),
          ∀ hRealization :
            realizationWitness point hSupport hWindow,
            ∀ hSource :
              supportWindowSourceObject point hSupport hWindow hRealization,
              sourceMembershipWitness point hSupport hWindow hRealization
                hSource
  supportMembershipProofObject :
    ∀ point : supportSet,
      ∀ hSupport : supportMembership point,
        ∀ hWindow :
          supportWindowMembership (supportToWindow point),
          ∀ hRealization :
            realizationWitness point hSupport hWindow,
            ∀ hSource :
              supportWindowSourceObject point hSupport hWindow hRealization,
              sourceMembershipWitness point hSupport hWindow hRealization
                hSource → Type
  supportMembershipProofCore :
    SourceSupportWindowSupportMembershipProofCoreData
      S f I supportSet supportMembership supportWindowSet
      supportWindowMembership supportToWindow realizationWitness
      supportWindowSourceObject sourceMembershipWitness
      supportMembershipProofObject

namespace SourceSupportWindowSourceMembershipCoreData

theorem sourceObjectRealizesSupportInWindow
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} {I : S.Window}
    {supportSet : Type} {supportMembership : supportSet → Prop}
    {supportWindowSet : Type}
    {supportWindowMembership : supportWindowSet → Prop}
    {supportToWindow : supportSet → supportWindowSet}
    {realizationWitness :
      ∀ point : supportSet,
        supportMembership point →
          supportWindowMembership (supportToWindow point) → Type}
    {supportWindowSourceObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            realizationWitness point hSupport hWindow → Type}
    {sourceMembershipWitness :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              supportWindowSourceObject
                point hSupport hWindow hRealization → Type}
    (D :
      SourceSupportWindowSourceMembershipCoreData
        S f I supportSet supportMembership supportWindowSet
        supportWindowMembership supportToWindow realizationWitness
        supportWindowSourceObject sourceMembershipWitness) :
    ∀ point : supportSet,
      ∀ hSupport : supportMembership point,
        ∀ hWindow :
          supportWindowMembership (supportToWindow point),
          ∀ hRealization :
            realizationWitness point hSupport hWindow,
            supportWindowSourceObject point hSupport hWindow hRealization →
              S.supportInWindow f I := by
  intro point hSupport hWindow hRealization hSource
  exact
    D.supportMembershipProofCore.sourceMembershipRealizesSupportInWindow
      point hSupport hWindow hRealization hSource
      (D.sourceMembershipWitnessFor
        point hSupport hWindow hRealization hSource)

end SourceSupportWindowSourceMembershipCoreData

structure SourceSupportWindowSourceObjectCoreData
    {A : SourceTestAlgebra} (S : SourceSupportWindowData A)
    (f : A.Test) (I : S.Window)
    (supportSet : Type) (supportMembership : supportSet → Prop)
    (supportWindowSet : Type)
    (supportWindowMembership : supportWindowSet → Prop)
    (supportToWindow : supportSet → supportWindowSet)
    (realizationWitness :
      ∀ point : supportSet,
        supportMembership point →
          supportWindowMembership (supportToWindow point) → Type)
    (supportWindowSourceObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            realizationWitness point hSupport hWindow → Type) where
  sourceMembershipWitness :
    ∀ point : supportSet,
      ∀ hSupport : supportMembership point,
        ∀ hWindow :
          supportWindowMembership (supportToWindow point),
          ∀ hRealization :
            realizationWitness point hSupport hWindow,
            supportWindowSourceObject
              point hSupport hWindow hRealization → Type
  sourceObjectFor :
    ∀ point : supportSet,
      ∀ hSupport : supportMembership point,
        ∀ hWindow :
          supportWindowMembership (supportToWindow point),
          ∀ hRealization :
            realizationWitness point hSupport hWindow,
            supportWindowSourceObject point hSupport hWindow hRealization
  sourceMembershipCore :
    SourceSupportWindowSourceMembershipCoreData
      S f I supportSet supportMembership supportWindowSet
      supportWindowMembership supportToWindow realizationWitness
      supportWindowSourceObject sourceMembershipWitness

namespace SourceSupportWindowSourceObjectCoreData

theorem realizationImpliesSupportInWindow
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} {I : S.Window}
    {supportSet : Type} {supportMembership : supportSet → Prop}
    {supportWindowSet : Type}
    {supportWindowMembership : supportWindowSet → Prop}
    {supportToWindow : supportSet → supportWindowSet}
    {realizationWitness :
      ∀ point : supportSet,
        supportMembership point →
          supportWindowMembership (supportToWindow point) → Type}
    {supportWindowSourceObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            realizationWitness point hSupport hWindow → Type}
    (D :
      SourceSupportWindowSourceObjectCoreData
        S f I supportSet supportMembership supportWindowSet
        supportWindowMembership supportToWindow realizationWitness
        supportWindowSourceObject) :
    ∀ point : supportSet,
      ∀ hSupport : supportMembership point,
        ∀ hWindow :
          supportWindowMembership (supportToWindow point),
            realizationWitness point hSupport hWindow →
              S.supportInWindow f I := by
  intro point hSupport hWindow hRealization
  exact
    D.sourceMembershipCore.sourceObjectRealizesSupportInWindow
      point hSupport hWindow hRealization
      (D.sourceObjectFor point hSupport hWindow hRealization)

end SourceSupportWindowSourceObjectCoreData

structure SourceSupportWindowRealizationCoreData
    {A : SourceTestAlgebra} (S : SourceSupportWindowData A)
    (f : A.Test) (I : S.Window)
    (supportSet : Type) (supportMembership : supportSet → Prop)
    (supportWindowSet : Type)
    (supportWindowMembership : supportWindowSet → Prop)
    (supportToWindow : supportSet → supportWindowSet)
    (realizationWitness :
      ∀ point : supportSet,
        supportMembership point →
          supportWindowMembership (supportToWindow point) → Type) where
  supportWindowSourceObject :
    ∀ point : supportSet,
      ∀ hSupport : supportMembership point,
        ∀ hWindow :
          supportWindowMembership (supportToWindow point),
            realizationWitness point hSupport hWindow → Type
  sourceObjectCore :
    SourceSupportWindowSourceObjectCoreData
      S f I supportSet supportMembership supportWindowSet
      supportWindowMembership supportToWindow realizationWitness
      supportWindowSourceObject

namespace SourceSupportWindowRealizationCoreData

theorem supportInWindow
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} {I : S.Window}
    {supportSet : Type} {supportMembership : supportSet → Prop}
    {supportWindowSet : Type}
    {supportWindowMembership : supportWindowSet → Prop}
    {supportToWindow : supportSet → supportWindowSet}
    {realizationWitness :
      ∀ point : supportSet,
        supportMembership point →
          supportWindowMembership (supportToWindow point) → Type}
    (D :
      SourceSupportWindowRealizationCoreData
        S f I supportSet supportMembership supportWindowSet
        supportWindowMembership supportToWindow realizationWitness) :
    ∀ point : supportSet,
      ∀ hSupport : supportMembership point,
        ∀ hWindow :
          supportWindowMembership (supportToWindow point),
            realizationWitness point hSupport hWindow →
              S.supportInWindow f I :=
  D.sourceObjectCore.realizationImpliesSupportInWindow

end SourceSupportWindowRealizationCoreData

structure SourceSupportWindowSupportMembershipConcreteSourceWitnessSupportWitnessEvidenceCertificateProofWitnessWitnessWitnessWitnessWitnessWitnessWitnessWitnessData
    {A : SourceTestAlgebra} (S : SourceSupportWindowData A)
    (f : A.Test) (I : S.Window)
    (supportSet : Type) (supportMembership : supportSet → Prop)
    (supportWindowSet : Type)
    (supportWindowMembership : supportWindowSet → Prop)
    (supportToWindow : supportSet → supportWindowSet)
    (realizationWitness :
      ∀ point : supportSet,
        supportMembership point →
          supportWindowMembership (supportToWindow point) → Type)
    (supportWindowSourceObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            realizationWitness point hSupport hWindow → Type)
    (sourceMembershipWitness :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              supportWindowSourceObject
                point hSupport hWindow hRealization → Type)
    (supportMembershipProofObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                sourceMembershipWitness
                  point hSupport hWindow hRealization hSource → Type)
    (supportMembershipEvidenceObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  supportMembershipProofObject
                    point hSupport hWindow hRealization hSource hMembership →
                    Type)
    (supportMembershipConcreteObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    supportMembershipEvidenceObject
                      point hSupport hWindow hRealization hSource
                      hMembership hProof → Type)
    (supportMembershipFinalObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    ∀ hEvidence :
                      supportMembershipEvidenceObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof,
                      supportMembershipConcreteObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof hEvidence → Type)
    (supportMembershipSourceNormalForm :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    ∀ hEvidence :
                      supportMembershipEvidenceObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof,
                      ∀ hConcrete :
                        supportMembershipConcreteObject
                          point hSupport hWindow hRealization hSource
                          hMembership hProof hEvidence,
                        supportMembershipFinalObject
                          point hSupport hWindow hRealization hSource
                          hMembership hProof hEvidence hConcrete → Type)
    (supportMembershipConcreteSourceData :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    ∀ hEvidence :
                      supportMembershipEvidenceObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof,
                      ∀ hConcrete :
                        supportMembershipConcreteObject
                          point hSupport hWindow hRealization hSource
                          hMembership hProof hEvidence,
                        ∀ hFinal :
                          supportMembershipFinalObject
                            point hSupport hWindow hRealization hSource
                            hMembership hProof hEvidence hConcrete,
                          supportMembershipSourceNormalForm
                            point hSupport hWindow hRealization hSource
                            hMembership hProof hEvidence hConcrete hFinal →
                            Type) where
  supportWindowRealizationCore :
    SourceSupportWindowRealizationCoreData
      S f I supportSet supportMembership supportWindowSet
      supportWindowMembership supportToWindow realizationWitness

namespace SourceSupportWindowSupportMembershipConcreteSourceWitnessSupportWitnessEvidenceCertificateProofWitnessWitnessWitnessWitnessWitnessWitnessWitnessWitnessData

theorem supportMembershipConcreteSourceDataRealizesSupportInWindow
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} {I : S.Window}
    {supportSet : Type} {supportMembership : supportSet → Prop}
    {supportWindowSet : Type}
    {supportWindowMembership : supportWindowSet → Prop}
    {supportToWindow : supportSet → supportWindowSet}
    {realizationWitness :
      ∀ point : supportSet,
        supportMembership point →
          supportWindowMembership (supportToWindow point) → Type}
    {supportWindowSourceObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            realizationWitness point hSupport hWindow → Type}
    {sourceMembershipWitness :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              supportWindowSourceObject
                point hSupport hWindow hRealization → Type}
    {supportMembershipProofObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                sourceMembershipWitness
                  point hSupport hWindow hRealization hSource → Type}
    {supportMembershipEvidenceObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  supportMembershipProofObject
                    point hSupport hWindow hRealization hSource hMembership →
                    Type}
    {supportMembershipConcreteObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    supportMembershipEvidenceObject
                      point hSupport hWindow hRealization hSource
                      hMembership hProof → Type}
    {supportMembershipFinalObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    ∀ hEvidence :
                      supportMembershipEvidenceObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof,
                      supportMembershipConcreteObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof hEvidence → Type}
    {supportMembershipSourceNormalForm :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    ∀ hEvidence :
                      supportMembershipEvidenceObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof,
                      ∀ hConcrete :
                        supportMembershipConcreteObject
                          point hSupport hWindow hRealization hSource
                          hMembership hProof hEvidence,
                        supportMembershipFinalObject
                          point hSupport hWindow hRealization hSource
                          hMembership hProof hEvidence hConcrete → Type}
    {supportMembershipConcreteSourceData :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    ∀ hEvidence :
                      supportMembershipEvidenceObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof,
                      ∀ hConcrete :
                        supportMembershipConcreteObject
                          point hSupport hWindow hRealization hSource
                          hMembership hProof hEvidence,
                        ∀ hFinal :
                          supportMembershipFinalObject
                            point hSupport hWindow hRealization hSource
                            hMembership hProof hEvidence hConcrete,
                          supportMembershipSourceNormalForm
                            point hSupport hWindow hRealization hSource
                            hMembership hProof hEvidence hConcrete hFinal →
                            Type}
    (D :
      SourceSupportWindowSupportMembershipConcreteSourceWitnessSupportWitnessEvidenceCertificateProofWitnessWitnessWitnessWitnessWitnessWitnessWitnessWitnessData
        S f I supportSet supportMembership supportWindowSet
        supportWindowMembership supportToWindow realizationWitness
        supportWindowSourceObject sourceMembershipWitness
        supportMembershipProofObject supportMembershipEvidenceObject
        supportMembershipConcreteObject supportMembershipFinalObject
        supportMembershipSourceNormalForm supportMembershipConcreteSourceData) :
    ∀ point : supportSet,
      ∀ hSupport : supportMembership point,
        ∀ hWindow :
          supportWindowMembership (supportToWindow point),
          ∀ hRealization :
            realizationWitness point hSupport hWindow,
            ∀ hSource :
              supportWindowSourceObject
                point hSupport hWindow hRealization,
              ∀ hMembership :
                sourceMembershipWitness
                  point hSupport hWindow hRealization hSource,
                ∀ hProof :
                  supportMembershipProofObject
                    point hSupport hWindow hRealization hSource hMembership,
                  ∀ hEvidence :
                    supportMembershipEvidenceObject
                      point hSupport hWindow hRealization hSource
                      hMembership hProof,
                    ∀ hConcrete :
                      supportMembershipConcreteObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof hEvidence,
                      ∀ hFinal :
                        supportMembershipFinalObject
                          point hSupport hWindow hRealization hSource
                          hMembership hProof hEvidence hConcrete,
                        ∀ hNormal :
                          supportMembershipSourceNormalForm
                            point hSupport hWindow hRealization hSource
                            hMembership hProof hEvidence hConcrete hFinal,
                          supportMembershipConcreteSourceData
                            point hSupport hWindow hRealization hSource
                            hMembership hProof hEvidence hConcrete hFinal
                            hNormal →
                            S.supportInWindow f I := by
  intro point hSupport hWindow hRealization hSource hMembership hProof
    hEvidence hConcrete hFinal hNormal hConcreteSource
  exact
    D.supportWindowRealizationCore.supportInWindow
      point hSupport hWindow hRealization

end SourceSupportWindowSupportMembershipConcreteSourceWitnessSupportWitnessEvidenceCertificateProofWitnessWitnessWitnessWitnessWitnessWitnessWitnessWitnessData

structure SourceSupportWindowSupportMembershipConcreteSourceWitnessSupportWitnessEvidenceCertificateProofWitnessWitnessWitnessWitnessWitnessWitnessWitnessData
    {A : SourceTestAlgebra} (S : SourceSupportWindowData A)
    (f : A.Test) (I : S.Window)
    (supportSet : Type) (supportMembership : supportSet → Prop)
    (supportWindowSet : Type)
    (supportWindowMembership : supportWindowSet → Prop)
    (supportToWindow : supportSet → supportWindowSet)
    (realizationWitness :
      ∀ point : supportSet,
        supportMembership point →
          supportWindowMembership (supportToWindow point) → Type)
    (supportWindowSourceObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            realizationWitness point hSupport hWindow → Type)
    (sourceMembershipWitness :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              supportWindowSourceObject
                point hSupport hWindow hRealization → Type)
    (supportMembershipProofObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                sourceMembershipWitness
                  point hSupport hWindow hRealization hSource → Type)
    (supportMembershipEvidenceObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  supportMembershipProofObject
                    point hSupport hWindow hRealization hSource hMembership →
                    Type)
    (supportMembershipConcreteObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    supportMembershipEvidenceObject
                      point hSupport hWindow hRealization hSource
                      hMembership hProof → Type)
    (supportMembershipFinalObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    ∀ hEvidence :
                      supportMembershipEvidenceObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof,
                      supportMembershipConcreteObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof hEvidence → Type)
    (supportMembershipSourceNormalForm :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    ∀ hEvidence :
                      supportMembershipEvidenceObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof,
                      ∀ hConcrete :
                        supportMembershipConcreteObject
                          point hSupport hWindow hRealization hSource
                          hMembership hProof hEvidence,
                        supportMembershipFinalObject
                          point hSupport hWindow hRealization hSource
                          hMembership hProof hEvidence hConcrete → Type)
    (supportMembershipConcreteSourceData :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    ∀ hEvidence :
                      supportMembershipEvidenceObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof,
                      ∀ hConcrete :
                        supportMembershipConcreteObject
                          point hSupport hWindow hRealization hSource
                          hMembership hProof hEvidence,
                        ∀ hFinal :
                          supportMembershipFinalObject
                            point hSupport hWindow hRealization hSource
                            hMembership hProof hEvidence hConcrete,
                          supportMembershipSourceNormalForm
                            point hSupport hWindow hRealization hSource
                            hMembership hProof hEvidence hConcrete hFinal →
                            Type) where
  supportMembershipConcreteSourceWitnessSupportWitnessEvidenceCertificateProofWitnessWitnessWitnessWitnessWitnessWitnessWitnessWitnessData :
    SourceSupportWindowSupportMembershipConcreteSourceWitnessSupportWitnessEvidenceCertificateProofWitnessWitnessWitnessWitnessWitnessWitnessWitnessWitnessData
      S f I supportSet supportMembership supportWindowSet
      supportWindowMembership supportToWindow realizationWitness
      supportWindowSourceObject sourceMembershipWitness
      supportMembershipProofObject supportMembershipEvidenceObject
      supportMembershipConcreteObject supportMembershipFinalObject
      supportMembershipSourceNormalForm supportMembershipConcreteSourceData

namespace SourceSupportWindowSupportMembershipConcreteSourceWitnessSupportWitnessEvidenceCertificateProofWitnessWitnessWitnessWitnessWitnessWitnessWitnessData

theorem supportMembershipConcreteSourceDataRealizesSupportInWindow
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} {I : S.Window}
    {supportSet : Type} {supportMembership : supportSet → Prop}
    {supportWindowSet : Type}
    {supportWindowMembership : supportWindowSet → Prop}
    {supportToWindow : supportSet → supportWindowSet}
    {realizationWitness :
      ∀ point : supportSet,
        supportMembership point →
          supportWindowMembership (supportToWindow point) → Type}
    {supportWindowSourceObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            realizationWitness point hSupport hWindow → Type}
    {sourceMembershipWitness :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              supportWindowSourceObject
                point hSupport hWindow hRealization → Type}
    {supportMembershipProofObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                sourceMembershipWitness
                  point hSupport hWindow hRealization hSource → Type}
    {supportMembershipEvidenceObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  supportMembershipProofObject
                    point hSupport hWindow hRealization hSource hMembership →
                    Type}
    {supportMembershipConcreteObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    supportMembershipEvidenceObject
                      point hSupport hWindow hRealization hSource
                      hMembership hProof → Type}
    {supportMembershipFinalObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    ∀ hEvidence :
                      supportMembershipEvidenceObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof,
                      supportMembershipConcreteObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof hEvidence → Type}
    {supportMembershipSourceNormalForm :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    ∀ hEvidence :
                      supportMembershipEvidenceObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof,
                      ∀ hConcrete :
                        supportMembershipConcreteObject
                          point hSupport hWindow hRealization hSource
                          hMembership hProof hEvidence,
                        supportMembershipFinalObject
                          point hSupport hWindow hRealization hSource
                          hMembership hProof hEvidence hConcrete → Type}
    {supportMembershipConcreteSourceData :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    ∀ hEvidence :
                      supportMembershipEvidenceObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof,
                      ∀ hConcrete :
                        supportMembershipConcreteObject
                          point hSupport hWindow hRealization hSource
                          hMembership hProof hEvidence,
                        ∀ hFinal :
                          supportMembershipFinalObject
                            point hSupport hWindow hRealization hSource
                            hMembership hProof hEvidence hConcrete,
                          supportMembershipSourceNormalForm
                            point hSupport hWindow hRealization hSource
                            hMembership hProof hEvidence hConcrete hFinal →
                            Type}
    (D :
      SourceSupportWindowSupportMembershipConcreteSourceWitnessSupportWitnessEvidenceCertificateProofWitnessWitnessWitnessWitnessWitnessWitnessWitnessData
        S f I supportSet supportMembership supportWindowSet
        supportWindowMembership supportToWindow realizationWitness
        supportWindowSourceObject sourceMembershipWitness
        supportMembershipProofObject supportMembershipEvidenceObject
        supportMembershipConcreteObject supportMembershipFinalObject
        supportMembershipSourceNormalForm supportMembershipConcreteSourceData) :
    ∀ point : supportSet,
      ∀ hSupport : supportMembership point,
        ∀ hWindow :
          supportWindowMembership (supportToWindow point),
          ∀ hRealization :
            realizationWitness point hSupport hWindow,
            ∀ hSource :
              supportWindowSourceObject
                point hSupport hWindow hRealization,
              ∀ hMembership :
                sourceMembershipWitness
                  point hSupport hWindow hRealization hSource,
                ∀ hProof :
                  supportMembershipProofObject
                    point hSupport hWindow hRealization hSource hMembership,
                  ∀ hEvidence :
                    supportMembershipEvidenceObject
                      point hSupport hWindow hRealization hSource
                      hMembership hProof,
                    ∀ hConcrete :
                      supportMembershipConcreteObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof hEvidence,
                      ∀ hFinal :
                        supportMembershipFinalObject
                          point hSupport hWindow hRealization hSource
                          hMembership hProof hEvidence hConcrete,
                        ∀ hNormal :
                          supportMembershipSourceNormalForm
                            point hSupport hWindow hRealization hSource
                            hMembership hProof hEvidence hConcrete hFinal,
                          supportMembershipConcreteSourceData
                            point hSupport hWindow hRealization hSource
                            hMembership hProof hEvidence hConcrete hFinal
                            hNormal →
                            S.supportInWindow f I := by
  intro point hSupport hWindow hRealization hSource hMembership hProof
    hEvidence hConcrete hFinal hNormal hConcreteSource
  exact
    D.supportMembershipConcreteSourceWitnessSupportWitnessEvidenceCertificateProofWitnessWitnessWitnessWitnessWitnessWitnessWitnessWitnessData
      |>.supportMembershipConcreteSourceDataRealizesSupportInWindow
        point hSupport hWindow hRealization hSource hMembership hProof
        hEvidence hConcrete hFinal hNormal hConcreteSource

end SourceSupportWindowSupportMembershipConcreteSourceWitnessSupportWitnessEvidenceCertificateProofWitnessWitnessWitnessWitnessWitnessWitnessWitnessData

structure SourceSupportWindowSupportMembershipConcreteSourceWitnessSupportWitnessEvidenceCertificateProofWitnessWitnessWitnessWitnessWitnessWitnessData
    {A : SourceTestAlgebra} (S : SourceSupportWindowData A)
    (f : A.Test) (I : S.Window)
    (supportSet : Type) (supportMembership : supportSet → Prop)
    (supportWindowSet : Type)
    (supportWindowMembership : supportWindowSet → Prop)
    (supportToWindow : supportSet → supportWindowSet)
    (realizationWitness :
      ∀ point : supportSet,
        supportMembership point →
          supportWindowMembership (supportToWindow point) → Type)
    (supportWindowSourceObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            realizationWitness point hSupport hWindow → Type)
    (sourceMembershipWitness :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              supportWindowSourceObject
                point hSupport hWindow hRealization → Type)
    (supportMembershipProofObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                sourceMembershipWitness
                  point hSupport hWindow hRealization hSource → Type)
    (supportMembershipEvidenceObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  supportMembershipProofObject
                    point hSupport hWindow hRealization hSource hMembership →
                    Type)
    (supportMembershipConcreteObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    supportMembershipEvidenceObject
                      point hSupport hWindow hRealization hSource
                      hMembership hProof → Type)
    (supportMembershipFinalObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    ∀ hEvidence :
                      supportMembershipEvidenceObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof,
                      supportMembershipConcreteObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof hEvidence → Type)
    (supportMembershipSourceNormalForm :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    ∀ hEvidence :
                      supportMembershipEvidenceObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof,
                      ∀ hConcrete :
                        supportMembershipConcreteObject
                          point hSupport hWindow hRealization hSource
                          hMembership hProof hEvidence,
                        supportMembershipFinalObject
                          point hSupport hWindow hRealization hSource
                          hMembership hProof hEvidence hConcrete → Type)
    (supportMembershipConcreteSourceData :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    ∀ hEvidence :
                      supportMembershipEvidenceObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof,
                      ∀ hConcrete :
                        supportMembershipConcreteObject
                          point hSupport hWindow hRealization hSource
                          hMembership hProof hEvidence,
                        ∀ hFinal :
                          supportMembershipFinalObject
                            point hSupport hWindow hRealization hSource
                            hMembership hProof hEvidence hConcrete,
                          supportMembershipSourceNormalForm
                            point hSupport hWindow hRealization hSource
                            hMembership hProof hEvidence hConcrete hFinal →
                            Type) where
  supportMembershipConcreteSourceWitnessSupportWitnessEvidenceCertificateProofWitnessWitnessWitnessWitnessWitnessWitnessWitnessData :
    SourceSupportWindowSupportMembershipConcreteSourceWitnessSupportWitnessEvidenceCertificateProofWitnessWitnessWitnessWitnessWitnessWitnessWitnessData
      S f I supportSet supportMembership supportWindowSet
      supportWindowMembership supportToWindow realizationWitness
      supportWindowSourceObject sourceMembershipWitness
      supportMembershipProofObject supportMembershipEvidenceObject
      supportMembershipConcreteObject supportMembershipFinalObject
      supportMembershipSourceNormalForm supportMembershipConcreteSourceData

namespace SourceSupportWindowSupportMembershipConcreteSourceWitnessSupportWitnessEvidenceCertificateProofWitnessWitnessWitnessWitnessWitnessWitnessData

theorem supportMembershipConcreteSourceDataRealizesSupportInWindow
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} {I : S.Window}
    {supportSet : Type} {supportMembership : supportSet → Prop}
    {supportWindowSet : Type}
    {supportWindowMembership : supportWindowSet → Prop}
    {supportToWindow : supportSet → supportWindowSet}
    {realizationWitness :
      ∀ point : supportSet,
        supportMembership point →
          supportWindowMembership (supportToWindow point) → Type}
    {supportWindowSourceObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            realizationWitness point hSupport hWindow → Type}
    {sourceMembershipWitness :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              supportWindowSourceObject
                point hSupport hWindow hRealization → Type}
    {supportMembershipProofObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                sourceMembershipWitness
                  point hSupport hWindow hRealization hSource → Type}
    {supportMembershipEvidenceObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  supportMembershipProofObject
                    point hSupport hWindow hRealization hSource hMembership →
                    Type}
    {supportMembershipConcreteObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    supportMembershipEvidenceObject
                      point hSupport hWindow hRealization hSource
                      hMembership hProof → Type}
    {supportMembershipFinalObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    ∀ hEvidence :
                      supportMembershipEvidenceObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof,
                      supportMembershipConcreteObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof hEvidence → Type}
    {supportMembershipSourceNormalForm :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    ∀ hEvidence :
                      supportMembershipEvidenceObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof,
                      ∀ hConcrete :
                        supportMembershipConcreteObject
                          point hSupport hWindow hRealization hSource
                          hMembership hProof hEvidence,
                        supportMembershipFinalObject
                          point hSupport hWindow hRealization hSource
                          hMembership hProof hEvidence hConcrete → Type}
    {supportMembershipConcreteSourceData :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    ∀ hEvidence :
                      supportMembershipEvidenceObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof,
                      ∀ hConcrete :
                        supportMembershipConcreteObject
                          point hSupport hWindow hRealization hSource
                          hMembership hProof hEvidence,
                        ∀ hFinal :
                          supportMembershipFinalObject
                            point hSupport hWindow hRealization hSource
                            hMembership hProof hEvidence hConcrete,
                          supportMembershipSourceNormalForm
                            point hSupport hWindow hRealization hSource
                            hMembership hProof hEvidence hConcrete hFinal →
                            Type}
    (D :
      SourceSupportWindowSupportMembershipConcreteSourceWitnessSupportWitnessEvidenceCertificateProofWitnessWitnessWitnessWitnessWitnessWitnessData
        S f I supportSet supportMembership supportWindowSet
        supportWindowMembership supportToWindow realizationWitness
        supportWindowSourceObject sourceMembershipWitness
        supportMembershipProofObject supportMembershipEvidenceObject
        supportMembershipConcreteObject supportMembershipFinalObject
        supportMembershipSourceNormalForm supportMembershipConcreteSourceData) :
    ∀ point : supportSet,
      ∀ hSupport : supportMembership point,
        ∀ hWindow :
          supportWindowMembership (supportToWindow point),
          ∀ hRealization :
            realizationWitness point hSupport hWindow,
            ∀ hSource :
              supportWindowSourceObject
                point hSupport hWindow hRealization,
              ∀ hMembership :
                sourceMembershipWitness
                  point hSupport hWindow hRealization hSource,
                ∀ hProof :
                  supportMembershipProofObject
                    point hSupport hWindow hRealization hSource hMembership,
                  ∀ hEvidence :
                    supportMembershipEvidenceObject
                      point hSupport hWindow hRealization hSource
                      hMembership hProof,
                    ∀ hConcrete :
                      supportMembershipConcreteObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof hEvidence,
                      ∀ hFinal :
                        supportMembershipFinalObject
                          point hSupport hWindow hRealization hSource
                          hMembership hProof hEvidence hConcrete,
                        ∀ hNormal :
                          supportMembershipSourceNormalForm
                            point hSupport hWindow hRealization hSource
                            hMembership hProof hEvidence hConcrete hFinal,
                          supportMembershipConcreteSourceData
                            point hSupport hWindow hRealization hSource
                            hMembership hProof hEvidence hConcrete hFinal
                            hNormal →
                            S.supportInWindow f I := by
  intro point hSupport hWindow hRealization hSource hMembership hProof
    hEvidence hConcrete hFinal hNormal hConcreteSource
  exact
    D.supportMembershipConcreteSourceWitnessSupportWitnessEvidenceCertificateProofWitnessWitnessWitnessWitnessWitnessWitnessWitnessData
      |>.supportMembershipConcreteSourceDataRealizesSupportInWindow
        point hSupport hWindow hRealization hSource hMembership hProof
        hEvidence hConcrete hFinal hNormal hConcreteSource

end SourceSupportWindowSupportMembershipConcreteSourceWitnessSupportWitnessEvidenceCertificateProofWitnessWitnessWitnessWitnessWitnessWitnessData

structure SourceSupportWindowSupportMembershipConcreteSourceWitnessSupportWitnessEvidenceCertificateProofWitnessWitnessWitnessWitnessWitnessData
    {A : SourceTestAlgebra} (S : SourceSupportWindowData A)
    (f : A.Test) (I : S.Window)
    (supportSet : Type) (supportMembership : supportSet → Prop)
    (supportWindowSet : Type)
    (supportWindowMembership : supportWindowSet → Prop)
    (supportToWindow : supportSet → supportWindowSet)
    (realizationWitness :
      ∀ point : supportSet,
        supportMembership point →
          supportWindowMembership (supportToWindow point) → Type)
    (supportWindowSourceObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            realizationWitness point hSupport hWindow → Type)
    (sourceMembershipWitness :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              supportWindowSourceObject
                point hSupport hWindow hRealization → Type)
    (supportMembershipProofObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                sourceMembershipWitness
                  point hSupport hWindow hRealization hSource → Type)
    (supportMembershipEvidenceObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  supportMembershipProofObject
                    point hSupport hWindow hRealization hSource hMembership →
                    Type)
    (supportMembershipConcreteObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    supportMembershipEvidenceObject
                      point hSupport hWindow hRealization hSource
                      hMembership hProof → Type)
    (supportMembershipFinalObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    ∀ hEvidence :
                      supportMembershipEvidenceObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof,
                      supportMembershipConcreteObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof hEvidence → Type)
    (supportMembershipSourceNormalForm :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    ∀ hEvidence :
                      supportMembershipEvidenceObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof,
                      ∀ hConcrete :
                        supportMembershipConcreteObject
                          point hSupport hWindow hRealization hSource
                          hMembership hProof hEvidence,
                        supportMembershipFinalObject
                          point hSupport hWindow hRealization hSource
                          hMembership hProof hEvidence hConcrete → Type)
    (supportMembershipConcreteSourceData :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    ∀ hEvidence :
                      supportMembershipEvidenceObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof,
                      ∀ hConcrete :
                        supportMembershipConcreteObject
                          point hSupport hWindow hRealization hSource
                          hMembership hProof hEvidence,
                        ∀ hFinal :
                          supportMembershipFinalObject
                            point hSupport hWindow hRealization hSource
                            hMembership hProof hEvidence hConcrete,
                          supportMembershipSourceNormalForm
                            point hSupport hWindow hRealization hSource
                            hMembership hProof hEvidence hConcrete hFinal →
                            Type) where
  supportMembershipConcreteSourceWitnessSupportWitnessEvidenceCertificateProofWitnessWitnessWitnessWitnessWitnessWitnessData :
    SourceSupportWindowSupportMembershipConcreteSourceWitnessSupportWitnessEvidenceCertificateProofWitnessWitnessWitnessWitnessWitnessWitnessData
      S f I supportSet supportMembership supportWindowSet
      supportWindowMembership supportToWindow realizationWitness
      supportWindowSourceObject sourceMembershipWitness
      supportMembershipProofObject supportMembershipEvidenceObject
      supportMembershipConcreteObject supportMembershipFinalObject
      supportMembershipSourceNormalForm supportMembershipConcreteSourceData

namespace SourceSupportWindowSupportMembershipConcreteSourceWitnessSupportWitnessEvidenceCertificateProofWitnessWitnessWitnessWitnessWitnessData

theorem supportMembershipConcreteSourceDataRealizesSupportInWindow
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} {I : S.Window}
    {supportSet : Type} {supportMembership : supportSet → Prop}
    {supportWindowSet : Type}
    {supportWindowMembership : supportWindowSet → Prop}
    {supportToWindow : supportSet → supportWindowSet}
    {realizationWitness :
      ∀ point : supportSet,
        supportMembership point →
          supportWindowMembership (supportToWindow point) → Type}
    {supportWindowSourceObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            realizationWitness point hSupport hWindow → Type}
    {sourceMembershipWitness :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              supportWindowSourceObject
                point hSupport hWindow hRealization → Type}
    {supportMembershipProofObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                sourceMembershipWitness
                  point hSupport hWindow hRealization hSource → Type}
    {supportMembershipEvidenceObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  supportMembershipProofObject
                    point hSupport hWindow hRealization hSource hMembership →
                    Type}
    {supportMembershipConcreteObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    supportMembershipEvidenceObject
                      point hSupport hWindow hRealization hSource
                      hMembership hProof → Type}
    {supportMembershipFinalObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    ∀ hEvidence :
                      supportMembershipEvidenceObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof,
                      supportMembershipConcreteObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof hEvidence → Type}
    {supportMembershipSourceNormalForm :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    ∀ hEvidence :
                      supportMembershipEvidenceObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof,
                      ∀ hConcrete :
                        supportMembershipConcreteObject
                          point hSupport hWindow hRealization hSource
                          hMembership hProof hEvidence,
                        supportMembershipFinalObject
                          point hSupport hWindow hRealization hSource
                          hMembership hProof hEvidence hConcrete → Type}
    {supportMembershipConcreteSourceData :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    ∀ hEvidence :
                      supportMembershipEvidenceObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof,
                      ∀ hConcrete :
                        supportMembershipConcreteObject
                          point hSupport hWindow hRealization hSource
                          hMembership hProof hEvidence,
                        ∀ hFinal :
                          supportMembershipFinalObject
                            point hSupport hWindow hRealization hSource
                            hMembership hProof hEvidence hConcrete,
                          supportMembershipSourceNormalForm
                            point hSupport hWindow hRealization hSource
                            hMembership hProof hEvidence hConcrete hFinal →
                            Type}
    (D :
      SourceSupportWindowSupportMembershipConcreteSourceWitnessSupportWitnessEvidenceCertificateProofWitnessWitnessWitnessWitnessWitnessData
        S f I supportSet supportMembership supportWindowSet
        supportWindowMembership supportToWindow realizationWitness
        supportWindowSourceObject sourceMembershipWitness
        supportMembershipProofObject supportMembershipEvidenceObject
        supportMembershipConcreteObject supportMembershipFinalObject
        supportMembershipSourceNormalForm supportMembershipConcreteSourceData) :
    ∀ point : supportSet,
      ∀ hSupport : supportMembership point,
        ∀ hWindow :
          supportWindowMembership (supportToWindow point),
          ∀ hRealization :
            realizationWitness point hSupport hWindow,
            ∀ hSource :
              supportWindowSourceObject
                point hSupport hWindow hRealization,
              ∀ hMembership :
                sourceMembershipWitness
                  point hSupport hWindow hRealization hSource,
                ∀ hProof :
                  supportMembershipProofObject
                    point hSupport hWindow hRealization hSource hMembership,
                  ∀ hEvidence :
                    supportMembershipEvidenceObject
                      point hSupport hWindow hRealization hSource
                      hMembership hProof,
                    ∀ hConcrete :
                      supportMembershipConcreteObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof hEvidence,
                      ∀ hFinal :
                        supportMembershipFinalObject
                          point hSupport hWindow hRealization hSource
                          hMembership hProof hEvidence hConcrete,
                        ∀ hNormal :
                          supportMembershipSourceNormalForm
                            point hSupport hWindow hRealization hSource
                            hMembership hProof hEvidence hConcrete hFinal,
                          supportMembershipConcreteSourceData
                            point hSupport hWindow hRealization hSource
                            hMembership hProof hEvidence hConcrete hFinal
                            hNormal →
                            S.supportInWindow f I := by
  intro point hSupport hWindow hRealization hSource hMembership hProof
    hEvidence hConcrete hFinal hNormal hConcreteSource
  exact
    D.supportMembershipConcreteSourceWitnessSupportWitnessEvidenceCertificateProofWitnessWitnessWitnessWitnessWitnessWitnessData
      |>.supportMembershipConcreteSourceDataRealizesSupportInWindow
        point hSupport hWindow hRealization hSource hMembership hProof
        hEvidence hConcrete hFinal hNormal hConcreteSource

end SourceSupportWindowSupportMembershipConcreteSourceWitnessSupportWitnessEvidenceCertificateProofWitnessWitnessWitnessWitnessWitnessData

structure SourceSupportWindowSupportMembershipConcreteSourceWitnessSupportWitnessEvidenceCertificateProofWitnessWitnessWitnessWitnessData
    {A : SourceTestAlgebra} (S : SourceSupportWindowData A)
    (f : A.Test) (I : S.Window)
    (supportSet : Type) (supportMembership : supportSet → Prop)
    (supportWindowSet : Type)
    (supportWindowMembership : supportWindowSet → Prop)
    (supportToWindow : supportSet → supportWindowSet)
    (realizationWitness :
      ∀ point : supportSet,
        supportMembership point →
          supportWindowMembership (supportToWindow point) → Type)
    (supportWindowSourceObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            realizationWitness point hSupport hWindow → Type)
    (sourceMembershipWitness :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              supportWindowSourceObject
                point hSupport hWindow hRealization → Type)
    (supportMembershipProofObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                sourceMembershipWitness
                  point hSupport hWindow hRealization hSource → Type)
    (supportMembershipEvidenceObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  supportMembershipProofObject
                    point hSupport hWindow hRealization hSource hMembership →
                    Type)
    (supportMembershipConcreteObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    supportMembershipEvidenceObject
                      point hSupport hWindow hRealization hSource
                      hMembership hProof → Type)
    (supportMembershipFinalObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    ∀ hEvidence :
                      supportMembershipEvidenceObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof,
                      supportMembershipConcreteObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof hEvidence → Type)
    (supportMembershipSourceNormalForm :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    ∀ hEvidence :
                      supportMembershipEvidenceObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof,
                      ∀ hConcrete :
                        supportMembershipConcreteObject
                          point hSupport hWindow hRealization hSource
                          hMembership hProof hEvidence,
                        supportMembershipFinalObject
                          point hSupport hWindow hRealization hSource
                          hMembership hProof hEvidence hConcrete → Type)
    (supportMembershipConcreteSourceData :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    ∀ hEvidence :
                      supportMembershipEvidenceObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof,
                      ∀ hConcrete :
                        supportMembershipConcreteObject
                          point hSupport hWindow hRealization hSource
                          hMembership hProof hEvidence,
                        ∀ hFinal :
                          supportMembershipFinalObject
                            point hSupport hWindow hRealization hSource
                            hMembership hProof hEvidence hConcrete,
                          supportMembershipSourceNormalForm
                            point hSupport hWindow hRealization hSource
                            hMembership hProof hEvidence hConcrete hFinal →
                            Type) where
  supportMembershipConcreteSourceWitnessSupportWitnessEvidenceCertificateProofWitnessWitnessWitnessWitnessWitnessData :
    SourceSupportWindowSupportMembershipConcreteSourceWitnessSupportWitnessEvidenceCertificateProofWitnessWitnessWitnessWitnessWitnessData
      S f I supportSet supportMembership supportWindowSet
      supportWindowMembership supportToWindow realizationWitness
      supportWindowSourceObject sourceMembershipWitness
      supportMembershipProofObject supportMembershipEvidenceObject
      supportMembershipConcreteObject supportMembershipFinalObject
      supportMembershipSourceNormalForm supportMembershipConcreteSourceData

namespace SourceSupportWindowSupportMembershipConcreteSourceWitnessSupportWitnessEvidenceCertificateProofWitnessWitnessWitnessWitnessData

theorem supportMembershipConcreteSourceDataRealizesSupportInWindow
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} {I : S.Window}
    {supportSet : Type} {supportMembership : supportSet → Prop}
    {supportWindowSet : Type}
    {supportWindowMembership : supportWindowSet → Prop}
    {supportToWindow : supportSet → supportWindowSet}
    {realizationWitness :
      ∀ point : supportSet,
        supportMembership point →
          supportWindowMembership (supportToWindow point) → Type}
    {supportWindowSourceObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            realizationWitness point hSupport hWindow → Type}
    {sourceMembershipWitness :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              supportWindowSourceObject
                point hSupport hWindow hRealization → Type}
    {supportMembershipProofObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                sourceMembershipWitness
                  point hSupport hWindow hRealization hSource → Type}
    {supportMembershipEvidenceObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  supportMembershipProofObject
                    point hSupport hWindow hRealization hSource hMembership →
                    Type}
    {supportMembershipConcreteObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    supportMembershipEvidenceObject
                      point hSupport hWindow hRealization hSource
                      hMembership hProof → Type}
    {supportMembershipFinalObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    ∀ hEvidence :
                      supportMembershipEvidenceObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof,
                      supportMembershipConcreteObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof hEvidence → Type}
    {supportMembershipSourceNormalForm :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    ∀ hEvidence :
                      supportMembershipEvidenceObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof,
                      ∀ hConcrete :
                        supportMembershipConcreteObject
                          point hSupport hWindow hRealization hSource
                          hMembership hProof hEvidence,
                        supportMembershipFinalObject
                          point hSupport hWindow hRealization hSource
                          hMembership hProof hEvidence hConcrete → Type}
    {supportMembershipConcreteSourceData :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    ∀ hEvidence :
                      supportMembershipEvidenceObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof,
                      ∀ hConcrete :
                        supportMembershipConcreteObject
                          point hSupport hWindow hRealization hSource
                          hMembership hProof hEvidence,
                        ∀ hFinal :
                          supportMembershipFinalObject
                            point hSupport hWindow hRealization hSource
                            hMembership hProof hEvidence hConcrete,
                          supportMembershipSourceNormalForm
                            point hSupport hWindow hRealization hSource
                            hMembership hProof hEvidence hConcrete hFinal →
                            Type}
    (D :
      SourceSupportWindowSupportMembershipConcreteSourceWitnessSupportWitnessEvidenceCertificateProofWitnessWitnessWitnessWitnessData
        S f I supportSet supportMembership supportWindowSet
        supportWindowMembership supportToWindow realizationWitness
        supportWindowSourceObject sourceMembershipWitness
        supportMembershipProofObject supportMembershipEvidenceObject
        supportMembershipConcreteObject supportMembershipFinalObject
        supportMembershipSourceNormalForm supportMembershipConcreteSourceData) :
    ∀ point : supportSet,
      ∀ hSupport : supportMembership point,
        ∀ hWindow :
          supportWindowMembership (supportToWindow point),
          ∀ hRealization :
            realizationWitness point hSupport hWindow,
            ∀ hSource :
              supportWindowSourceObject
                point hSupport hWindow hRealization,
              ∀ hMembership :
                sourceMembershipWitness
                  point hSupport hWindow hRealization hSource,
                ∀ hProof :
                  supportMembershipProofObject
                    point hSupport hWindow hRealization hSource hMembership,
                  ∀ hEvidence :
                    supportMembershipEvidenceObject
                      point hSupport hWindow hRealization hSource
                      hMembership hProof,
                    ∀ hConcrete :
                      supportMembershipConcreteObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof hEvidence,
                      ∀ hFinal :
                        supportMembershipFinalObject
                          point hSupport hWindow hRealization hSource
                          hMembership hProof hEvidence hConcrete,
                        ∀ hNormal :
                          supportMembershipSourceNormalForm
                            point hSupport hWindow hRealization hSource
                            hMembership hProof hEvidence hConcrete hFinal,
                          supportMembershipConcreteSourceData
                            point hSupport hWindow hRealization hSource
                            hMembership hProof hEvidence hConcrete hFinal
                            hNormal →
                            S.supportInWindow f I := by
  intro point hSupport hWindow hRealization hSource hMembership hProof
    hEvidence hConcrete hFinal hNormal hConcreteSource
  exact
    D.supportMembershipConcreteSourceWitnessSupportWitnessEvidenceCertificateProofWitnessWitnessWitnessWitnessWitnessData
      |>.supportMembershipConcreteSourceDataRealizesSupportInWindow
        point hSupport hWindow hRealization hSource hMembership hProof
        hEvidence hConcrete hFinal hNormal hConcreteSource

end SourceSupportWindowSupportMembershipConcreteSourceWitnessSupportWitnessEvidenceCertificateProofWitnessWitnessWitnessWitnessData

structure SourceSupportWindowSupportMembershipConcreteSourceWitnessSupportWitnessEvidenceCertificateProofWitnessWitnessWitnessData
    {A : SourceTestAlgebra} (S : SourceSupportWindowData A)
    (f : A.Test) (I : S.Window)
    (supportSet : Type) (supportMembership : supportSet → Prop)
    (supportWindowSet : Type)
    (supportWindowMembership : supportWindowSet → Prop)
    (supportToWindow : supportSet → supportWindowSet)
    (realizationWitness :
      ∀ point : supportSet,
        supportMembership point →
          supportWindowMembership (supportToWindow point) → Type)
    (supportWindowSourceObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            realizationWitness point hSupport hWindow → Type)
    (sourceMembershipWitness :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              supportWindowSourceObject
                point hSupport hWindow hRealization → Type)
    (supportMembershipProofObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                sourceMembershipWitness
                  point hSupport hWindow hRealization hSource → Type)
    (supportMembershipEvidenceObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  supportMembershipProofObject
                    point hSupport hWindow hRealization hSource hMembership →
                    Type)
    (supportMembershipConcreteObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    supportMembershipEvidenceObject
                      point hSupport hWindow hRealization hSource
                      hMembership hProof → Type)
    (supportMembershipFinalObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    ∀ hEvidence :
                      supportMembershipEvidenceObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof,
                      supportMembershipConcreteObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof hEvidence → Type)
    (supportMembershipSourceNormalForm :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    ∀ hEvidence :
                      supportMembershipEvidenceObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof,
                      ∀ hConcrete :
                        supportMembershipConcreteObject
                          point hSupport hWindow hRealization hSource
                          hMembership hProof hEvidence,
                        supportMembershipFinalObject
                          point hSupport hWindow hRealization hSource
                          hMembership hProof hEvidence hConcrete → Type)
    (supportMembershipConcreteSourceData :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    ∀ hEvidence :
                      supportMembershipEvidenceObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof,
                      ∀ hConcrete :
                        supportMembershipConcreteObject
                          point hSupport hWindow hRealization hSource
                          hMembership hProof hEvidence,
                        ∀ hFinal :
                          supportMembershipFinalObject
                            point hSupport hWindow hRealization hSource
                            hMembership hProof hEvidence hConcrete,
                          supportMembershipSourceNormalForm
                            point hSupport hWindow hRealization hSource
                            hMembership hProof hEvidence hConcrete hFinal →
                            Type) where
  supportMembershipConcreteSourceWitnessSupportWitnessEvidenceCertificateProofWitnessWitnessWitnessWitnessData :
    SourceSupportWindowSupportMembershipConcreteSourceWitnessSupportWitnessEvidenceCertificateProofWitnessWitnessWitnessWitnessData
      S f I supportSet supportMembership supportWindowSet
      supportWindowMembership supportToWindow realizationWitness
      supportWindowSourceObject sourceMembershipWitness
      supportMembershipProofObject supportMembershipEvidenceObject
      supportMembershipConcreteObject supportMembershipFinalObject
      supportMembershipSourceNormalForm supportMembershipConcreteSourceData

namespace SourceSupportWindowSupportMembershipConcreteSourceWitnessSupportWitnessEvidenceCertificateProofWitnessWitnessWitnessData

theorem supportMembershipConcreteSourceDataRealizesSupportInWindow
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} {I : S.Window}
    {supportSet : Type} {supportMembership : supportSet → Prop}
    {supportWindowSet : Type}
    {supportWindowMembership : supportWindowSet → Prop}
    {supportToWindow : supportSet → supportWindowSet}
    {realizationWitness :
      ∀ point : supportSet,
        supportMembership point →
          supportWindowMembership (supportToWindow point) → Type}
    {supportWindowSourceObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            realizationWitness point hSupport hWindow → Type}
    {sourceMembershipWitness :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              supportWindowSourceObject
                point hSupport hWindow hRealization → Type}
    {supportMembershipProofObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                sourceMembershipWitness
                  point hSupport hWindow hRealization hSource → Type}
    {supportMembershipEvidenceObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  supportMembershipProofObject
                    point hSupport hWindow hRealization hSource hMembership →
                    Type}
    {supportMembershipConcreteObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    supportMembershipEvidenceObject
                      point hSupport hWindow hRealization hSource
                      hMembership hProof → Type}
    {supportMembershipFinalObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    ∀ hEvidence :
                      supportMembershipEvidenceObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof,
                      supportMembershipConcreteObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof hEvidence → Type}
    {supportMembershipSourceNormalForm :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    ∀ hEvidence :
                      supportMembershipEvidenceObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof,
                      ∀ hConcrete :
                        supportMembershipConcreteObject
                          point hSupport hWindow hRealization hSource
                          hMembership hProof hEvidence,
                        supportMembershipFinalObject
                          point hSupport hWindow hRealization hSource
                          hMembership hProof hEvidence hConcrete → Type}
    {supportMembershipConcreteSourceData :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    ∀ hEvidence :
                      supportMembershipEvidenceObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof,
                      ∀ hConcrete :
                        supportMembershipConcreteObject
                          point hSupport hWindow hRealization hSource
                          hMembership hProof hEvidence,
                        ∀ hFinal :
                          supportMembershipFinalObject
                            point hSupport hWindow hRealization hSource
                            hMembership hProof hEvidence hConcrete,
                          supportMembershipSourceNormalForm
                            point hSupport hWindow hRealization hSource
                            hMembership hProof hEvidence hConcrete hFinal →
                            Type}
    (D :
      SourceSupportWindowSupportMembershipConcreteSourceWitnessSupportWitnessEvidenceCertificateProofWitnessWitnessWitnessData
        S f I supportSet supportMembership supportWindowSet
        supportWindowMembership supportToWindow realizationWitness
        supportWindowSourceObject sourceMembershipWitness
        supportMembershipProofObject supportMembershipEvidenceObject
        supportMembershipConcreteObject supportMembershipFinalObject
        supportMembershipSourceNormalForm supportMembershipConcreteSourceData) :
    ∀ point : supportSet,
      ∀ hSupport : supportMembership point,
        ∀ hWindow :
          supportWindowMembership (supportToWindow point),
          ∀ hRealization :
            realizationWitness point hSupport hWindow,
            ∀ hSource :
              supportWindowSourceObject
                point hSupport hWindow hRealization,
              ∀ hMembership :
                sourceMembershipWitness
                  point hSupport hWindow hRealization hSource,
                ∀ hProof :
                  supportMembershipProofObject
                    point hSupport hWindow hRealization hSource hMembership,
                  ∀ hEvidence :
                    supportMembershipEvidenceObject
                      point hSupport hWindow hRealization hSource
                      hMembership hProof,
                    ∀ hConcrete :
                      supportMembershipConcreteObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof hEvidence,
                      ∀ hFinal :
                        supportMembershipFinalObject
                          point hSupport hWindow hRealization hSource
                          hMembership hProof hEvidence hConcrete,
                        ∀ hNormal :
                          supportMembershipSourceNormalForm
                            point hSupport hWindow hRealization hSource
                            hMembership hProof hEvidence hConcrete hFinal,
                          supportMembershipConcreteSourceData
                            point hSupport hWindow hRealization hSource
                            hMembership hProof hEvidence hConcrete hFinal
                            hNormal →
                            S.supportInWindow f I := by
  intro point hSupport hWindow hRealization hSource hMembership hProof
    hEvidence hConcrete hFinal hNormal hConcreteSource
  exact
    D.supportMembershipConcreteSourceWitnessSupportWitnessEvidenceCertificateProofWitnessWitnessWitnessWitnessData
      |>.supportMembershipConcreteSourceDataRealizesSupportInWindow
        point hSupport hWindow hRealization hSource hMembership hProof
        hEvidence hConcrete hFinal hNormal hConcreteSource

end SourceSupportWindowSupportMembershipConcreteSourceWitnessSupportWitnessEvidenceCertificateProofWitnessWitnessWitnessData

structure SourceSupportWindowSupportMembershipConcreteSourceWitnessSupportWitnessEvidenceCertificateProofWitnessWitnessData
    {A : SourceTestAlgebra} (S : SourceSupportWindowData A)
    (f : A.Test) (I : S.Window)
    (supportSet : Type) (supportMembership : supportSet → Prop)
    (supportWindowSet : Type)
    (supportWindowMembership : supportWindowSet → Prop)
    (supportToWindow : supportSet → supportWindowSet)
    (realizationWitness :
      ∀ point : supportSet,
        supportMembership point →
          supportWindowMembership (supportToWindow point) → Type)
    (supportWindowSourceObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            realizationWitness point hSupport hWindow → Type)
    (sourceMembershipWitness :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              supportWindowSourceObject
                point hSupport hWindow hRealization → Type)
    (supportMembershipProofObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                sourceMembershipWitness
                  point hSupport hWindow hRealization hSource → Type)
    (supportMembershipEvidenceObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  supportMembershipProofObject
                    point hSupport hWindow hRealization hSource hMembership →
                    Type)
    (supportMembershipConcreteObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    supportMembershipEvidenceObject
                      point hSupport hWindow hRealization hSource
                      hMembership hProof → Type)
    (supportMembershipFinalObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    ∀ hEvidence :
                      supportMembershipEvidenceObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof,
                      supportMembershipConcreteObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof hEvidence → Type)
    (supportMembershipSourceNormalForm :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    ∀ hEvidence :
                      supportMembershipEvidenceObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof,
                      ∀ hConcrete :
                        supportMembershipConcreteObject
                          point hSupport hWindow hRealization hSource
                          hMembership hProof hEvidence,
                        supportMembershipFinalObject
                          point hSupport hWindow hRealization hSource
                          hMembership hProof hEvidence hConcrete → Type)
    (supportMembershipConcreteSourceData :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    ∀ hEvidence :
                      supportMembershipEvidenceObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof,
                      ∀ hConcrete :
                        supportMembershipConcreteObject
                          point hSupport hWindow hRealization hSource
                          hMembership hProof hEvidence,
                        ∀ hFinal :
                          supportMembershipFinalObject
                            point hSupport hWindow hRealization hSource
                            hMembership hProof hEvidence hConcrete,
                          supportMembershipSourceNormalForm
                            point hSupport hWindow hRealization hSource
                            hMembership hProof hEvidence hConcrete hFinal →
                            Type) where
  supportMembershipConcreteSourceWitnessSupportWitnessEvidenceCertificateProofWitnessWitnessWitnessData :
    SourceSupportWindowSupportMembershipConcreteSourceWitnessSupportWitnessEvidenceCertificateProofWitnessWitnessWitnessData
      S f I supportSet supportMembership supportWindowSet
      supportWindowMembership supportToWindow realizationWitness
      supportWindowSourceObject sourceMembershipWitness
      supportMembershipProofObject supportMembershipEvidenceObject
      supportMembershipConcreteObject supportMembershipFinalObject
      supportMembershipSourceNormalForm supportMembershipConcreteSourceData

namespace SourceSupportWindowSupportMembershipConcreteSourceWitnessSupportWitnessEvidenceCertificateProofWitnessWitnessData

theorem supportMembershipConcreteSourceDataRealizesSupportInWindow
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} {I : S.Window}
    {supportSet : Type} {supportMembership : supportSet → Prop}
    {supportWindowSet : Type}
    {supportWindowMembership : supportWindowSet → Prop}
    {supportToWindow : supportSet → supportWindowSet}
    {realizationWitness :
      ∀ point : supportSet,
        supportMembership point →
          supportWindowMembership (supportToWindow point) → Type}
    {supportWindowSourceObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            realizationWitness point hSupport hWindow → Type}
    {sourceMembershipWitness :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              supportWindowSourceObject
                point hSupport hWindow hRealization → Type}
    {supportMembershipProofObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                sourceMembershipWitness
                  point hSupport hWindow hRealization hSource → Type}
    {supportMembershipEvidenceObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  supportMembershipProofObject
                    point hSupport hWindow hRealization hSource hMembership →
                    Type}
    {supportMembershipConcreteObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    supportMembershipEvidenceObject
                      point hSupport hWindow hRealization hSource
                      hMembership hProof → Type}
    {supportMembershipFinalObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    ∀ hEvidence :
                      supportMembershipEvidenceObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof,
                      supportMembershipConcreteObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof hEvidence → Type}
    {supportMembershipSourceNormalForm :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    ∀ hEvidence :
                      supportMembershipEvidenceObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof,
                      ∀ hConcrete :
                        supportMembershipConcreteObject
                          point hSupport hWindow hRealization hSource
                          hMembership hProof hEvidence,
                        supportMembershipFinalObject
                          point hSupport hWindow hRealization hSource
                          hMembership hProof hEvidence hConcrete → Type}
    {supportMembershipConcreteSourceData :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    ∀ hEvidence :
                      supportMembershipEvidenceObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof,
                      ∀ hConcrete :
                        supportMembershipConcreteObject
                          point hSupport hWindow hRealization hSource
                          hMembership hProof hEvidence,
                        ∀ hFinal :
                          supportMembershipFinalObject
                            point hSupport hWindow hRealization hSource
                            hMembership hProof hEvidence hConcrete,
                          supportMembershipSourceNormalForm
                            point hSupport hWindow hRealization hSource
                            hMembership hProof hEvidence hConcrete hFinal →
                            Type}
    (D :
      SourceSupportWindowSupportMembershipConcreteSourceWitnessSupportWitnessEvidenceCertificateProofWitnessWitnessData
        S f I supportSet supportMembership supportWindowSet
        supportWindowMembership supportToWindow realizationWitness
        supportWindowSourceObject sourceMembershipWitness
        supportMembershipProofObject supportMembershipEvidenceObject
        supportMembershipConcreteObject supportMembershipFinalObject
        supportMembershipSourceNormalForm supportMembershipConcreteSourceData) :
    ∀ point : supportSet,
      ∀ hSupport : supportMembership point,
        ∀ hWindow :
          supportWindowMembership (supportToWindow point),
          ∀ hRealization :
            realizationWitness point hSupport hWindow,
            ∀ hSource :
              supportWindowSourceObject
                point hSupport hWindow hRealization,
              ∀ hMembership :
                sourceMembershipWitness
                  point hSupport hWindow hRealization hSource,
                ∀ hProof :
                  supportMembershipProofObject
                    point hSupport hWindow hRealization hSource hMembership,
                  ∀ hEvidence :
                    supportMembershipEvidenceObject
                      point hSupport hWindow hRealization hSource
                      hMembership hProof,
                    ∀ hConcrete :
                      supportMembershipConcreteObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof hEvidence,
                      ∀ hFinal :
                        supportMembershipFinalObject
                          point hSupport hWindow hRealization hSource
                          hMembership hProof hEvidence hConcrete,
                        ∀ hNormal :
                          supportMembershipSourceNormalForm
                            point hSupport hWindow hRealization hSource
                            hMembership hProof hEvidence hConcrete hFinal,
                          supportMembershipConcreteSourceData
                            point hSupport hWindow hRealization hSource
                            hMembership hProof hEvidence hConcrete hFinal
                            hNormal →
                            S.supportInWindow f I := by
  intro point hSupport hWindow hRealization hSource hMembership hProof
    hEvidence hConcrete hFinal hNormal hConcreteSource
  exact
    D.supportMembershipConcreteSourceWitnessSupportWitnessEvidenceCertificateProofWitnessWitnessWitnessData
      |>.supportMembershipConcreteSourceDataRealizesSupportInWindow
        point hSupport hWindow hRealization hSource hMembership hProof
        hEvidence hConcrete hFinal hNormal hConcreteSource

end SourceSupportWindowSupportMembershipConcreteSourceWitnessSupportWitnessEvidenceCertificateProofWitnessWitnessData

structure SourceSupportWindowSupportMembershipConcreteSourceWitnessSupportWitnessEvidenceCertificateProofWitnessData
    {A : SourceTestAlgebra} (S : SourceSupportWindowData A)
    (f : A.Test) (I : S.Window)
    (supportSet : Type) (supportMembership : supportSet → Prop)
    (supportWindowSet : Type)
    (supportWindowMembership : supportWindowSet → Prop)
    (supportToWindow : supportSet → supportWindowSet)
    (realizationWitness :
      ∀ point : supportSet,
        supportMembership point →
          supportWindowMembership (supportToWindow point) → Type)
    (supportWindowSourceObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            realizationWitness point hSupport hWindow → Type)
    (sourceMembershipWitness :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              supportWindowSourceObject
                point hSupport hWindow hRealization → Type)
    (supportMembershipProofObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                sourceMembershipWitness
                  point hSupport hWindow hRealization hSource → Type)
    (supportMembershipEvidenceObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  supportMembershipProofObject
                    point hSupport hWindow hRealization hSource hMembership →
                    Type)
    (supportMembershipConcreteObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    supportMembershipEvidenceObject
                      point hSupport hWindow hRealization hSource
                      hMembership hProof → Type)
    (supportMembershipFinalObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    ∀ hEvidence :
                      supportMembershipEvidenceObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof,
                      supportMembershipConcreteObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof hEvidence → Type)
    (supportMembershipSourceNormalForm :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    ∀ hEvidence :
                      supportMembershipEvidenceObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof,
                      ∀ hConcrete :
                        supportMembershipConcreteObject
                          point hSupport hWindow hRealization hSource
                          hMembership hProof hEvidence,
                        supportMembershipFinalObject
                          point hSupport hWindow hRealization hSource
                          hMembership hProof hEvidence hConcrete → Type)
    (supportMembershipConcreteSourceData :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    ∀ hEvidence :
                      supportMembershipEvidenceObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof,
                      ∀ hConcrete :
                        supportMembershipConcreteObject
                          point hSupport hWindow hRealization hSource
                          hMembership hProof hEvidence,
                        ∀ hFinal :
                          supportMembershipFinalObject
                            point hSupport hWindow hRealization hSource
                            hMembership hProof hEvidence hConcrete,
                          supportMembershipSourceNormalForm
                            point hSupport hWindow hRealization hSource
                            hMembership hProof hEvidence hConcrete hFinal →
                            Type) where
  supportMembershipConcreteSourceWitnessSupportWitnessEvidenceCertificateProofWitnessWitnessData :
    SourceSupportWindowSupportMembershipConcreteSourceWitnessSupportWitnessEvidenceCertificateProofWitnessWitnessData
      S f I supportSet supportMembership supportWindowSet
      supportWindowMembership supportToWindow realizationWitness
      supportWindowSourceObject sourceMembershipWitness
      supportMembershipProofObject supportMembershipEvidenceObject
      supportMembershipConcreteObject supportMembershipFinalObject
      supportMembershipSourceNormalForm supportMembershipConcreteSourceData

namespace SourceSupportWindowSupportMembershipConcreteSourceWitnessSupportWitnessEvidenceCertificateProofWitnessData

theorem supportMembershipConcreteSourceDataRealizesSupportInWindow
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} {I : S.Window}
    {supportSet : Type} {supportMembership : supportSet → Prop}
    {supportWindowSet : Type}
    {supportWindowMembership : supportWindowSet → Prop}
    {supportToWindow : supportSet → supportWindowSet}
    {realizationWitness :
      ∀ point : supportSet,
        supportMembership point →
          supportWindowMembership (supportToWindow point) → Type}
    {supportWindowSourceObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            realizationWitness point hSupport hWindow → Type}
    {sourceMembershipWitness :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              supportWindowSourceObject
                point hSupport hWindow hRealization → Type}
    {supportMembershipProofObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                sourceMembershipWitness
                  point hSupport hWindow hRealization hSource → Type}
    {supportMembershipEvidenceObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  supportMembershipProofObject
                    point hSupport hWindow hRealization hSource hMembership →
                    Type}
    {supportMembershipConcreteObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    supportMembershipEvidenceObject
                      point hSupport hWindow hRealization hSource
                      hMembership hProof → Type}
    {supportMembershipFinalObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    ∀ hEvidence :
                      supportMembershipEvidenceObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof,
                      supportMembershipConcreteObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof hEvidence → Type}
    {supportMembershipSourceNormalForm :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    ∀ hEvidence :
                      supportMembershipEvidenceObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof,
                      ∀ hConcrete :
                        supportMembershipConcreteObject
                          point hSupport hWindow hRealization hSource
                          hMembership hProof hEvidence,
                        supportMembershipFinalObject
                          point hSupport hWindow hRealization hSource
                          hMembership hProof hEvidence hConcrete → Type}
    {supportMembershipConcreteSourceData :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    ∀ hEvidence :
                      supportMembershipEvidenceObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof,
                      ∀ hConcrete :
                        supportMembershipConcreteObject
                          point hSupport hWindow hRealization hSource
                          hMembership hProof hEvidence,
                        ∀ hFinal :
                          supportMembershipFinalObject
                            point hSupport hWindow hRealization hSource
                            hMembership hProof hEvidence hConcrete,
                          supportMembershipSourceNormalForm
                            point hSupport hWindow hRealization hSource
                            hMembership hProof hEvidence hConcrete hFinal →
                            Type}
    (D :
      SourceSupportWindowSupportMembershipConcreteSourceWitnessSupportWitnessEvidenceCertificateProofWitnessData
        S f I supportSet supportMembership supportWindowSet
        supportWindowMembership supportToWindow realizationWitness
        supportWindowSourceObject sourceMembershipWitness
        supportMembershipProofObject supportMembershipEvidenceObject
        supportMembershipConcreteObject supportMembershipFinalObject
        supportMembershipSourceNormalForm supportMembershipConcreteSourceData) :
    ∀ point : supportSet,
      ∀ hSupport : supportMembership point,
        ∀ hWindow :
          supportWindowMembership (supportToWindow point),
          ∀ hRealization :
            realizationWitness point hSupport hWindow,
            ∀ hSource :
              supportWindowSourceObject
                point hSupport hWindow hRealization,
              ∀ hMembership :
                sourceMembershipWitness
                  point hSupport hWindow hRealization hSource,
                ∀ hProof :
                  supportMembershipProofObject
                    point hSupport hWindow hRealization hSource hMembership,
                  ∀ hEvidence :
                    supportMembershipEvidenceObject
                      point hSupport hWindow hRealization hSource
                      hMembership hProof,
                    ∀ hConcrete :
                      supportMembershipConcreteObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof hEvidence,
                      ∀ hFinal :
                        supportMembershipFinalObject
                          point hSupport hWindow hRealization hSource
                          hMembership hProof hEvidence hConcrete,
                        ∀ hNormal :
                          supportMembershipSourceNormalForm
                            point hSupport hWindow hRealization hSource
                            hMembership hProof hEvidence hConcrete hFinal,
                          supportMembershipConcreteSourceData
                            point hSupport hWindow hRealization hSource
                            hMembership hProof hEvidence hConcrete hFinal
                            hNormal →
                            S.supportInWindow f I := by
  intro point hSupport hWindow hRealization hSource hMembership hProof
    hEvidence hConcrete hFinal hNormal hConcreteSource
  exact
    D.supportMembershipConcreteSourceWitnessSupportWitnessEvidenceCertificateProofWitnessWitnessData
      |>.supportMembershipConcreteSourceDataRealizesSupportInWindow
        point hSupport hWindow hRealization hSource hMembership hProof
        hEvidence hConcrete hFinal hNormal hConcreteSource

end SourceSupportWindowSupportMembershipConcreteSourceWitnessSupportWitnessEvidenceCertificateProofWitnessData

structure SourceSupportWindowSupportMembershipConcreteSourceWitnessSupportWitnessEvidenceCertificateProofData
    {A : SourceTestAlgebra} (S : SourceSupportWindowData A)
    (f : A.Test) (I : S.Window)
    (supportSet : Type) (supportMembership : supportSet → Prop)
    (supportWindowSet : Type)
    (supportWindowMembership : supportWindowSet → Prop)
    (supportToWindow : supportSet → supportWindowSet)
    (realizationWitness :
      ∀ point : supportSet,
        supportMembership point →
          supportWindowMembership (supportToWindow point) → Type)
    (supportWindowSourceObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            realizationWitness point hSupport hWindow → Type)
    (sourceMembershipWitness :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              supportWindowSourceObject
                point hSupport hWindow hRealization → Type)
    (supportMembershipProofObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                sourceMembershipWitness
                  point hSupport hWindow hRealization hSource → Type)
    (supportMembershipEvidenceObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  supportMembershipProofObject
                    point hSupport hWindow hRealization hSource hMembership →
                    Type)
    (supportMembershipConcreteObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    supportMembershipEvidenceObject
                      point hSupport hWindow hRealization hSource
                      hMembership hProof → Type)
    (supportMembershipFinalObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    ∀ hEvidence :
                      supportMembershipEvidenceObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof,
                      supportMembershipConcreteObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof hEvidence → Type)
    (supportMembershipSourceNormalForm :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    ∀ hEvidence :
                      supportMembershipEvidenceObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof,
                      ∀ hConcrete :
                        supportMembershipConcreteObject
                          point hSupport hWindow hRealization hSource
                          hMembership hProof hEvidence,
                        supportMembershipFinalObject
                          point hSupport hWindow hRealization hSource
                          hMembership hProof hEvidence hConcrete → Type)
    (supportMembershipConcreteSourceData :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    ∀ hEvidence :
                      supportMembershipEvidenceObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof,
                      ∀ hConcrete :
                        supportMembershipConcreteObject
                          point hSupport hWindow hRealization hSource
                          hMembership hProof hEvidence,
                        ∀ hFinal :
                          supportMembershipFinalObject
                            point hSupport hWindow hRealization hSource
                            hMembership hProof hEvidence hConcrete,
                          supportMembershipSourceNormalForm
                            point hSupport hWindow hRealization hSource
                            hMembership hProof hEvidence hConcrete hFinal →
                            Type) where
  supportMembershipConcreteSourceWitnessSupportWitnessEvidenceCertificateProofWitnessData :
    SourceSupportWindowSupportMembershipConcreteSourceWitnessSupportWitnessEvidenceCertificateProofWitnessData
      S f I supportSet supportMembership supportWindowSet
      supportWindowMembership supportToWindow realizationWitness
      supportWindowSourceObject sourceMembershipWitness
      supportMembershipProofObject supportMembershipEvidenceObject
      supportMembershipConcreteObject supportMembershipFinalObject
      supportMembershipSourceNormalForm supportMembershipConcreteSourceData
namespace SourceSupportWindowSupportMembershipConcreteSourceWitnessSupportWitnessEvidenceCertificateProofData

theorem supportMembershipConcreteSourceDataRealizesSupportInWindow
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} {I : S.Window}
    {supportSet : Type} {supportMembership : supportSet → Prop}
    {supportWindowSet : Type}
    {supportWindowMembership : supportWindowSet → Prop}
    {supportToWindow : supportSet → supportWindowSet}
    {realizationWitness :
      ∀ point : supportSet,
        supportMembership point →
          supportWindowMembership (supportToWindow point) → Type}
    {supportWindowSourceObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            realizationWitness point hSupport hWindow → Type}
    {sourceMembershipWitness :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              supportWindowSourceObject
                point hSupport hWindow hRealization → Type}
    {supportMembershipProofObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                sourceMembershipWitness
                  point hSupport hWindow hRealization hSource → Type}
    {supportMembershipEvidenceObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  supportMembershipProofObject
                    point hSupport hWindow hRealization hSource hMembership →
                    Type}
    {supportMembershipConcreteObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    supportMembershipEvidenceObject
                      point hSupport hWindow hRealization hSource
                      hMembership hProof → Type}
    {supportMembershipFinalObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    ∀ hEvidence :
                      supportMembershipEvidenceObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof,
                      supportMembershipConcreteObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof hEvidence → Type}
    {supportMembershipSourceNormalForm :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    ∀ hEvidence :
                      supportMembershipEvidenceObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof,
                      ∀ hConcrete :
                        supportMembershipConcreteObject
                          point hSupport hWindow hRealization hSource
                          hMembership hProof hEvidence,
                        supportMembershipFinalObject
                          point hSupport hWindow hRealization hSource
                          hMembership hProof hEvidence hConcrete → Type}
    {supportMembershipConcreteSourceData :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    ∀ hEvidence :
                      supportMembershipEvidenceObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof,
                      ∀ hConcrete :
                        supportMembershipConcreteObject
                          point hSupport hWindow hRealization hSource
                          hMembership hProof hEvidence,
                        ∀ hFinal :
                          supportMembershipFinalObject
                            point hSupport hWindow hRealization hSource
                            hMembership hProof hEvidence hConcrete,
                          supportMembershipSourceNormalForm
                            point hSupport hWindow hRealization hSource
                            hMembership hProof hEvidence hConcrete hFinal →
                            Type}
    (D :
      SourceSupportWindowSupportMembershipConcreteSourceWitnessSupportWitnessEvidenceCertificateProofData
        S f I supportSet supportMembership supportWindowSet
        supportWindowMembership supportToWindow realizationWitness
        supportWindowSourceObject sourceMembershipWitness
        supportMembershipProofObject supportMembershipEvidenceObject
        supportMembershipConcreteObject supportMembershipFinalObject
        supportMembershipSourceNormalForm supportMembershipConcreteSourceData) :
    ∀ point : supportSet,
      ∀ hSupport : supportMembership point,
        ∀ hWindow :
          supportWindowMembership (supportToWindow point),
          ∀ hRealization :
            realizationWitness point hSupport hWindow,
            ∀ hSource :
              supportWindowSourceObject
                point hSupport hWindow hRealization,
              ∀ hMembership :
                sourceMembershipWitness
                  point hSupport hWindow hRealization hSource,
                ∀ hProof :
                  supportMembershipProofObject
                    point hSupport hWindow hRealization hSource hMembership,
                  ∀ hEvidence :
                    supportMembershipEvidenceObject
                      point hSupport hWindow hRealization hSource
                      hMembership hProof,
                    ∀ hConcrete :
                      supportMembershipConcreteObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof hEvidence,
                      ∀ hFinal :
                        supportMembershipFinalObject
                          point hSupport hWindow hRealization hSource
                          hMembership hProof hEvidence hConcrete,
                        ∀ hNormal :
                          supportMembershipSourceNormalForm
                            point hSupport hWindow hRealization hSource
                            hMembership hProof hEvidence hConcrete hFinal,
                          supportMembershipConcreteSourceData
                            point hSupport hWindow hRealization hSource
                            hMembership hProof hEvidence hConcrete hFinal
                            hNormal →
                            S.supportInWindow f I := by
  intro point hSupport hWindow hRealization hSource hMembership hProof
    hEvidence hConcrete hFinal hNormal hConcreteSource
  exact
    D.supportMembershipConcreteSourceWitnessSupportWitnessEvidenceCertificateProofWitnessData
      |>.supportMembershipConcreteSourceDataRealizesSupportInWindow
        point hSupport hWindow hRealization hSource hMembership hProof
        hEvidence hConcrete hFinal hNormal hConcreteSource

end SourceSupportWindowSupportMembershipConcreteSourceWitnessSupportWitnessEvidenceCertificateProofData

structure SourceSupportWindowSupportMembershipConcreteSourceWitnessSupportWitnessEvidenceCertificateData
    {A : SourceTestAlgebra} (S : SourceSupportWindowData A)
    (f : A.Test) (I : S.Window)
    (supportSet : Type) (supportMembership : supportSet → Prop)
    (supportWindowSet : Type)
    (supportWindowMembership : supportWindowSet → Prop)
    (supportToWindow : supportSet → supportWindowSet)
    (realizationWitness :
      ∀ point : supportSet,
        supportMembership point →
          supportWindowMembership (supportToWindow point) → Type)
    (supportWindowSourceObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            realizationWitness point hSupport hWindow → Type)
    (sourceMembershipWitness :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              supportWindowSourceObject
                point hSupport hWindow hRealization → Type)
    (supportMembershipProofObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                sourceMembershipWitness
                  point hSupport hWindow hRealization hSource → Type)
    (supportMembershipEvidenceObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  supportMembershipProofObject
                    point hSupport hWindow hRealization hSource hMembership →
                    Type)
    (supportMembershipConcreteObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    supportMembershipEvidenceObject
                      point hSupport hWindow hRealization hSource
                      hMembership hProof → Type)
    (supportMembershipFinalObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    ∀ hEvidence :
                      supportMembershipEvidenceObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof,
                      supportMembershipConcreteObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof hEvidence → Type)
    (supportMembershipSourceNormalForm :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    ∀ hEvidence :
                      supportMembershipEvidenceObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof,
                      ∀ hConcrete :
                        supportMembershipConcreteObject
                          point hSupport hWindow hRealization hSource
                          hMembership hProof hEvidence,
                        supportMembershipFinalObject
                          point hSupport hWindow hRealization hSource
                          hMembership hProof hEvidence hConcrete → Type)
    (supportMembershipConcreteSourceData :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    ∀ hEvidence :
                      supportMembershipEvidenceObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof,
                      ∀ hConcrete :
                        supportMembershipConcreteObject
                          point hSupport hWindow hRealization hSource
                          hMembership hProof hEvidence,
                        ∀ hFinal :
                          supportMembershipFinalObject
                            point hSupport hWindow hRealization hSource
                            hMembership hProof hEvidence hConcrete,
                          supportMembershipSourceNormalForm
                            point hSupport hWindow hRealization hSource
                            hMembership hProof hEvidence hConcrete hFinal →
                            Type) where
  supportMembershipConcreteSourceWitnessSupportWitnessEvidenceCertificateProofData :
    SourceSupportWindowSupportMembershipConcreteSourceWitnessSupportWitnessEvidenceCertificateProofData
      S f I supportSet supportMembership supportWindowSet
      supportWindowMembership supportToWindow realizationWitness
      supportWindowSourceObject sourceMembershipWitness
      supportMembershipProofObject supportMembershipEvidenceObject
      supportMembershipConcreteObject supportMembershipFinalObject
      supportMembershipSourceNormalForm supportMembershipConcreteSourceData
namespace SourceSupportWindowSupportMembershipConcreteSourceWitnessSupportWitnessEvidenceCertificateData

theorem supportMembershipConcreteSourceDataRealizesSupportInWindow
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} {I : S.Window}
    {supportSet : Type} {supportMembership : supportSet → Prop}
    {supportWindowSet : Type}
    {supportWindowMembership : supportWindowSet → Prop}
    {supportToWindow : supportSet → supportWindowSet}
    {realizationWitness :
      ∀ point : supportSet,
        supportMembership point →
          supportWindowMembership (supportToWindow point) → Type}
    {supportWindowSourceObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            realizationWitness point hSupport hWindow → Type}
    {sourceMembershipWitness :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              supportWindowSourceObject
                point hSupport hWindow hRealization → Type}
    {supportMembershipProofObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                sourceMembershipWitness
                  point hSupport hWindow hRealization hSource → Type}
    {supportMembershipEvidenceObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  supportMembershipProofObject
                    point hSupport hWindow hRealization hSource hMembership →
                    Type}
    {supportMembershipConcreteObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    supportMembershipEvidenceObject
                      point hSupport hWindow hRealization hSource
                      hMembership hProof → Type}
    {supportMembershipFinalObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    ∀ hEvidence :
                      supportMembershipEvidenceObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof,
                      supportMembershipConcreteObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof hEvidence → Type}
    {supportMembershipSourceNormalForm :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    ∀ hEvidence :
                      supportMembershipEvidenceObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof,
                      ∀ hConcrete :
                        supportMembershipConcreteObject
                          point hSupport hWindow hRealization hSource
                          hMembership hProof hEvidence,
                        supportMembershipFinalObject
                          point hSupport hWindow hRealization hSource
                          hMembership hProof hEvidence hConcrete → Type}
    {supportMembershipConcreteSourceData :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    ∀ hEvidence :
                      supportMembershipEvidenceObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof,
                      ∀ hConcrete :
                        supportMembershipConcreteObject
                          point hSupport hWindow hRealization hSource
                          hMembership hProof hEvidence,
                        ∀ hFinal :
                          supportMembershipFinalObject
                            point hSupport hWindow hRealization hSource
                            hMembership hProof hEvidence hConcrete,
                          supportMembershipSourceNormalForm
                            point hSupport hWindow hRealization hSource
                            hMembership hProof hEvidence hConcrete hFinal →
                            Type}
    (D :
      SourceSupportWindowSupportMembershipConcreteSourceWitnessSupportWitnessEvidenceCertificateData
        S f I supportSet supportMembership supportWindowSet
        supportWindowMembership supportToWindow realizationWitness
        supportWindowSourceObject sourceMembershipWitness
        supportMembershipProofObject supportMembershipEvidenceObject
        supportMembershipConcreteObject supportMembershipFinalObject
        supportMembershipSourceNormalForm supportMembershipConcreteSourceData) :
    ∀ point : supportSet,
      ∀ hSupport : supportMembership point,
        ∀ hWindow :
          supportWindowMembership (supportToWindow point),
          ∀ hRealization :
            realizationWitness point hSupport hWindow,
            ∀ hSource :
              supportWindowSourceObject
                point hSupport hWindow hRealization,
              ∀ hMembership :
                sourceMembershipWitness
                  point hSupport hWindow hRealization hSource,
                ∀ hProof :
                  supportMembershipProofObject
                    point hSupport hWindow hRealization hSource hMembership,
                  ∀ hEvidence :
                    supportMembershipEvidenceObject
                      point hSupport hWindow hRealization hSource
                      hMembership hProof,
                    ∀ hConcrete :
                      supportMembershipConcreteObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof hEvidence,
                      ∀ hFinal :
                        supportMembershipFinalObject
                          point hSupport hWindow hRealization hSource
                          hMembership hProof hEvidence hConcrete,
                        ∀ hNormal :
                          supportMembershipSourceNormalForm
                            point hSupport hWindow hRealization hSource
                            hMembership hProof hEvidence hConcrete hFinal,
                          supportMembershipConcreteSourceData
                            point hSupport hWindow hRealization hSource
                            hMembership hProof hEvidence hConcrete hFinal
                            hNormal →
                            S.supportInWindow f I := by
  intro point hSupport hWindow hRealization hSource hMembership hProof
    hEvidence hConcrete hFinal hNormal hConcreteSource
  exact
    D.supportMembershipConcreteSourceWitnessSupportWitnessEvidenceCertificateProofData
      |>.supportMembershipConcreteSourceDataRealizesSupportInWindow
        point hSupport hWindow hRealization hSource hMembership hProof
        hEvidence hConcrete hFinal hNormal hConcreteSource

end SourceSupportWindowSupportMembershipConcreteSourceWitnessSupportWitnessEvidenceCertificateData

structure SourceSupportWindowSupportMembershipConcreteSourceWitnessSupportWitnessEvidenceData
    {A : SourceTestAlgebra} (S : SourceSupportWindowData A)
    (f : A.Test) (I : S.Window)
    (supportSet : Type) (supportMembership : supportSet → Prop)
    (supportWindowSet : Type)
    (supportWindowMembership : supportWindowSet → Prop)
    (supportToWindow : supportSet → supportWindowSet)
    (realizationWitness :
      ∀ point : supportSet,
        supportMembership point →
          supportWindowMembership (supportToWindow point) → Type)
    (supportWindowSourceObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            realizationWitness point hSupport hWindow → Type)
    (sourceMembershipWitness :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              supportWindowSourceObject
                point hSupport hWindow hRealization → Type)
    (supportMembershipProofObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                sourceMembershipWitness
                  point hSupport hWindow hRealization hSource → Type)
    (supportMembershipEvidenceObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  supportMembershipProofObject
                    point hSupport hWindow hRealization hSource hMembership →
                    Type)
    (supportMembershipConcreteObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    supportMembershipEvidenceObject
                      point hSupport hWindow hRealization hSource
                      hMembership hProof → Type)
    (supportMembershipFinalObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    ∀ hEvidence :
                      supportMembershipEvidenceObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof,
                      supportMembershipConcreteObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof hEvidence → Type)
    (supportMembershipSourceNormalForm :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    ∀ hEvidence :
                      supportMembershipEvidenceObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof,
                      ∀ hConcrete :
                        supportMembershipConcreteObject
                          point hSupport hWindow hRealization hSource
                          hMembership hProof hEvidence,
                        supportMembershipFinalObject
                          point hSupport hWindow hRealization hSource
                          hMembership hProof hEvidence hConcrete → Type)
    (supportMembershipConcreteSourceData :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    ∀ hEvidence :
                      supportMembershipEvidenceObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof,
                      ∀ hConcrete :
                        supportMembershipConcreteObject
                          point hSupport hWindow hRealization hSource
                          hMembership hProof hEvidence,
                        ∀ hFinal :
                          supportMembershipFinalObject
                            point hSupport hWindow hRealization hSource
                            hMembership hProof hEvidence hConcrete,
                          supportMembershipSourceNormalForm
                            point hSupport hWindow hRealization hSource
                            hMembership hProof hEvidence hConcrete hFinal →
                            Type) where
  supportMembershipConcreteSourceWitnessSupportWitnessEvidenceCertificateData :
    SourceSupportWindowSupportMembershipConcreteSourceWitnessSupportWitnessEvidenceCertificateData
      S f I supportSet supportMembership supportWindowSet
      supportWindowMembership supportToWindow realizationWitness
      supportWindowSourceObject sourceMembershipWitness
      supportMembershipProofObject supportMembershipEvidenceObject
      supportMembershipConcreteObject supportMembershipFinalObject
      supportMembershipSourceNormalForm supportMembershipConcreteSourceData
namespace SourceSupportWindowSupportMembershipConcreteSourceWitnessSupportWitnessEvidenceData

theorem supportMembershipConcreteSourceDataRealizesSupportInWindow
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} {I : S.Window}
    {supportSet : Type} {supportMembership : supportSet → Prop}
    {supportWindowSet : Type}
    {supportWindowMembership : supportWindowSet → Prop}
    {supportToWindow : supportSet → supportWindowSet}
    {realizationWitness :
      ∀ point : supportSet,
        supportMembership point →
          supportWindowMembership (supportToWindow point) → Type}
    {supportWindowSourceObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            realizationWitness point hSupport hWindow → Type}
    {sourceMembershipWitness :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              supportWindowSourceObject
                point hSupport hWindow hRealization → Type}
    {supportMembershipProofObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                sourceMembershipWitness
                  point hSupport hWindow hRealization hSource → Type}
    {supportMembershipEvidenceObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  supportMembershipProofObject
                    point hSupport hWindow hRealization hSource hMembership →
                    Type}
    {supportMembershipConcreteObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    supportMembershipEvidenceObject
                      point hSupport hWindow hRealization hSource
                      hMembership hProof → Type}
    {supportMembershipFinalObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    ∀ hEvidence :
                      supportMembershipEvidenceObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof,
                      supportMembershipConcreteObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof hEvidence → Type}
    {supportMembershipSourceNormalForm :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    ∀ hEvidence :
                      supportMembershipEvidenceObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof,
                      ∀ hConcrete :
                        supportMembershipConcreteObject
                          point hSupport hWindow hRealization hSource
                          hMembership hProof hEvidence,
                        supportMembershipFinalObject
                          point hSupport hWindow hRealization hSource
                          hMembership hProof hEvidence hConcrete → Type}
    {supportMembershipConcreteSourceData :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    ∀ hEvidence :
                      supportMembershipEvidenceObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof,
                      ∀ hConcrete :
                        supportMembershipConcreteObject
                          point hSupport hWindow hRealization hSource
                          hMembership hProof hEvidence,
                        ∀ hFinal :
                          supportMembershipFinalObject
                            point hSupport hWindow hRealization hSource
                            hMembership hProof hEvidence hConcrete,
                          supportMembershipSourceNormalForm
                            point hSupport hWindow hRealization hSource
                            hMembership hProof hEvidence hConcrete hFinal →
                            Type}
    (D :
      SourceSupportWindowSupportMembershipConcreteSourceWitnessSupportWitnessEvidenceData
        S f I supportSet supportMembership supportWindowSet
        supportWindowMembership supportToWindow realizationWitness
        supportWindowSourceObject sourceMembershipWitness
        supportMembershipProofObject supportMembershipEvidenceObject
        supportMembershipConcreteObject supportMembershipFinalObject
        supportMembershipSourceNormalForm supportMembershipConcreteSourceData) :
    ∀ point : supportSet,
      ∀ hSupport : supportMembership point,
        ∀ hWindow :
          supportWindowMembership (supportToWindow point),
          ∀ hRealization :
            realizationWitness point hSupport hWindow,
            ∀ hSource :
              supportWindowSourceObject
                point hSupport hWindow hRealization,
              ∀ hMembership :
                sourceMembershipWitness
                  point hSupport hWindow hRealization hSource,
                ∀ hProof :
                  supportMembershipProofObject
                    point hSupport hWindow hRealization hSource hMembership,
                  ∀ hEvidence :
                    supportMembershipEvidenceObject
                      point hSupport hWindow hRealization hSource
                      hMembership hProof,
                    ∀ hConcrete :
                      supportMembershipConcreteObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof hEvidence,
                      ∀ hFinal :
                        supportMembershipFinalObject
                          point hSupport hWindow hRealization hSource
                          hMembership hProof hEvidence hConcrete,
                        ∀ hNormal :
                          supportMembershipSourceNormalForm
                            point hSupport hWindow hRealization hSource
                            hMembership hProof hEvidence hConcrete hFinal,
                          supportMembershipConcreteSourceData
                            point hSupport hWindow hRealization hSource
                            hMembership hProof hEvidence hConcrete hFinal
                            hNormal →
                            S.supportInWindow f I := by
  intro point hSupport hWindow hRealization hSource hMembership hProof
    hEvidence hConcrete hFinal hNormal hConcreteSource
  exact
    D.supportMembershipConcreteSourceWitnessSupportWitnessEvidenceCertificateData
      |>.supportMembershipConcreteSourceDataRealizesSupportInWindow
        point hSupport hWindow hRealization hSource hMembership hProof
        hEvidence hConcrete hFinal hNormal hConcreteSource

end SourceSupportWindowSupportMembershipConcreteSourceWitnessSupportWitnessEvidenceData

structure SourceSupportWindowSupportMembershipConcreteSourceWitnessSupportWitnessData
    {A : SourceTestAlgebra} (S : SourceSupportWindowData A)
    (f : A.Test) (I : S.Window)
    (supportSet : Type) (supportMembership : supportSet → Prop)
    (supportWindowSet : Type)
    (supportWindowMembership : supportWindowSet → Prop)
    (supportToWindow : supportSet → supportWindowSet)
    (realizationWitness :
      ∀ point : supportSet,
        supportMembership point →
          supportWindowMembership (supportToWindow point) → Type)
    (supportWindowSourceObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            realizationWitness point hSupport hWindow → Type)
    (sourceMembershipWitness :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              supportWindowSourceObject
                point hSupport hWindow hRealization → Type)
    (supportMembershipProofObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                sourceMembershipWitness
                  point hSupport hWindow hRealization hSource → Type)
    (supportMembershipEvidenceObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  supportMembershipProofObject
                    point hSupport hWindow hRealization hSource hMembership →
                    Type)
    (supportMembershipConcreteObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    supportMembershipEvidenceObject
                      point hSupport hWindow hRealization hSource
                      hMembership hProof → Type)
    (supportMembershipFinalObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    ∀ hEvidence :
                      supportMembershipEvidenceObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof,
                      supportMembershipConcreteObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof hEvidence → Type)
    (supportMembershipSourceNormalForm :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    ∀ hEvidence :
                      supportMembershipEvidenceObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof,
                      ∀ hConcrete :
                        supportMembershipConcreteObject
                          point hSupport hWindow hRealization hSource
                          hMembership hProof hEvidence,
                        supportMembershipFinalObject
                          point hSupport hWindow hRealization hSource
                          hMembership hProof hEvidence hConcrete → Type)
    (supportMembershipConcreteSourceData :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    ∀ hEvidence :
                      supportMembershipEvidenceObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof,
                      ∀ hConcrete :
                        supportMembershipConcreteObject
                          point hSupport hWindow hRealization hSource
                          hMembership hProof hEvidence,
                        ∀ hFinal :
                          supportMembershipFinalObject
                            point hSupport hWindow hRealization hSource
                            hMembership hProof hEvidence hConcrete,
                          supportMembershipSourceNormalForm
                            point hSupport hWindow hRealization hSource
                            hMembership hProof hEvidence hConcrete hFinal →
                            Type) where
  supportMembershipConcreteSourceWitnessSupportWitnessEvidenceData :
    SourceSupportWindowSupportMembershipConcreteSourceWitnessSupportWitnessEvidenceData
      S f I supportSet supportMembership supportWindowSet
      supportWindowMembership supportToWindow realizationWitness
      supportWindowSourceObject sourceMembershipWitness
      supportMembershipProofObject supportMembershipEvidenceObject
      supportMembershipConcreteObject supportMembershipFinalObject
      supportMembershipSourceNormalForm supportMembershipConcreteSourceData

namespace SourceSupportWindowSupportMembershipConcreteSourceWitnessSupportWitnessData
theorem supportMembershipConcreteSourceDataRealizesSupportInWindow
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} {I : S.Window}
    {supportSet : Type} {supportMembership : supportSet → Prop}
    {supportWindowSet : Type}
    {supportWindowMembership : supportWindowSet → Prop}
    {supportToWindow : supportSet → supportWindowSet}
    {realizationWitness :
      ∀ point : supportSet,
        supportMembership point →
          supportWindowMembership (supportToWindow point) → Type}
    {supportWindowSourceObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            realizationWitness point hSupport hWindow → Type}
    {sourceMembershipWitness :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              supportWindowSourceObject
                point hSupport hWindow hRealization → Type}
    {supportMembershipProofObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                sourceMembershipWitness
                  point hSupport hWindow hRealization hSource → Type}
    {supportMembershipEvidenceObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  supportMembershipProofObject
                    point hSupport hWindow hRealization hSource hMembership →
                    Type}
    {supportMembershipConcreteObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    supportMembershipEvidenceObject
                      point hSupport hWindow hRealization hSource
                      hMembership hProof → Type}
    {supportMembershipFinalObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    ∀ hEvidence :
                      supportMembershipEvidenceObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof,
                      supportMembershipConcreteObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof hEvidence → Type}
    {supportMembershipSourceNormalForm :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    ∀ hEvidence :
                      supportMembershipEvidenceObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof,
                      ∀ hConcrete :
                        supportMembershipConcreteObject
                          point hSupport hWindow hRealization hSource
                          hMembership hProof hEvidence,
                        supportMembershipFinalObject
                          point hSupport hWindow hRealization hSource
                          hMembership hProof hEvidence hConcrete → Type}
    {supportMembershipConcreteSourceData :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    ∀ hEvidence :
                      supportMembershipEvidenceObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof,
                      ∀ hConcrete :
                        supportMembershipConcreteObject
                          point hSupport hWindow hRealization hSource
                          hMembership hProof hEvidence,
                        ∀ hFinal :
                          supportMembershipFinalObject
                            point hSupport hWindow hRealization hSource
                            hMembership hProof hEvidence hConcrete,
                          supportMembershipSourceNormalForm
                            point hSupport hWindow hRealization hSource
                            hMembership hProof hEvidence hConcrete hFinal →
                            Type}
    (D :
      SourceSupportWindowSupportMembershipConcreteSourceWitnessSupportWitnessData
        S f I supportSet supportMembership supportWindowSet
        supportWindowMembership supportToWindow realizationWitness
        supportWindowSourceObject sourceMembershipWitness
        supportMembershipProofObject supportMembershipEvidenceObject
        supportMembershipConcreteObject supportMembershipFinalObject
        supportMembershipSourceNormalForm supportMembershipConcreteSourceData) :
    ∀ point : supportSet,
      ∀ hSupport : supportMembership point,
        ∀ hWindow :
          supportWindowMembership (supportToWindow point),
          ∀ hRealization :
            realizationWitness point hSupport hWindow,
            ∀ hSource :
              supportWindowSourceObject
                point hSupport hWindow hRealization,
              ∀ hMembership :
                sourceMembershipWitness
                  point hSupport hWindow hRealization hSource,
                ∀ hProof :
                  supportMembershipProofObject
                    point hSupport hWindow hRealization hSource hMembership,
                  ∀ hEvidence :
                    supportMembershipEvidenceObject
                      point hSupport hWindow hRealization hSource
                      hMembership hProof,
                    ∀ hConcrete :
                      supportMembershipConcreteObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof hEvidence,
                      ∀ hFinal :
                        supportMembershipFinalObject
                          point hSupport hWindow hRealization hSource
                          hMembership hProof hEvidence hConcrete,
                        ∀ hNormal :
                          supportMembershipSourceNormalForm
                            point hSupport hWindow hRealization hSource
                            hMembership hProof hEvidence hConcrete hFinal,
                          supportMembershipConcreteSourceData
                            point hSupport hWindow hRealization hSource
                            hMembership hProof hEvidence hConcrete hFinal
                            hNormal →
                            S.supportInWindow f I := by
  exact
    D.supportMembershipConcreteSourceWitnessSupportWitnessEvidenceData
      |>.supportMembershipConcreteSourceDataRealizesSupportInWindow
end SourceSupportWindowSupportMembershipConcreteSourceWitnessSupportWitnessData

structure SourceSupportWindowSupportMembershipConcreteSourceWitnessSupportCertificateData
    {A : SourceTestAlgebra} (S : SourceSupportWindowData A)
    (f : A.Test) (I : S.Window)
    (supportSet : Type) (supportMembership : supportSet → Prop)
    (supportWindowSet : Type)
    (supportWindowMembership : supportWindowSet → Prop)
    (supportToWindow : supportSet → supportWindowSet)
    (realizationWitness :
      ∀ point : supportSet,
        supportMembership point →
          supportWindowMembership (supportToWindow point) → Type)
    (supportWindowSourceObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            realizationWitness point hSupport hWindow → Type)
    (sourceMembershipWitness :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              supportWindowSourceObject
                point hSupport hWindow hRealization → Type)
    (supportMembershipProofObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                sourceMembershipWitness
                  point hSupport hWindow hRealization hSource → Type)
    (supportMembershipEvidenceObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  supportMembershipProofObject
                    point hSupport hWindow hRealization hSource hMembership →
                    Type)
    (supportMembershipConcreteObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    supportMembershipEvidenceObject
                      point hSupport hWindow hRealization hSource
                      hMembership hProof → Type)
    (supportMembershipFinalObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    ∀ hEvidence :
                      supportMembershipEvidenceObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof,
                      supportMembershipConcreteObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof hEvidence → Type)
    (supportMembershipSourceNormalForm :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    ∀ hEvidence :
                      supportMembershipEvidenceObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof,
                      ∀ hConcrete :
                        supportMembershipConcreteObject
                          point hSupport hWindow hRealization hSource
                          hMembership hProof hEvidence,
                        supportMembershipFinalObject
                          point hSupport hWindow hRealization hSource
                          hMembership hProof hEvidence hConcrete → Type)
    (supportMembershipConcreteSourceData :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    ∀ hEvidence :
                      supportMembershipEvidenceObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof,
                      ∀ hConcrete :
                        supportMembershipConcreteObject
                          point hSupport hWindow hRealization hSource
                          hMembership hProof hEvidence,
                        ∀ hFinal :
                          supportMembershipFinalObject
                            point hSupport hWindow hRealization hSource
                            hMembership hProof hEvidence hConcrete,
                          supportMembershipSourceNormalForm
                            point hSupport hWindow hRealization hSource
                            hMembership hProof hEvidence hConcrete hFinal →
                            Type) where
  supportMembershipConcreteSourceWitnessSupportWitnessData :
    SourceSupportWindowSupportMembershipConcreteSourceWitnessSupportWitnessData
      S f I supportSet supportMembership supportWindowSet
      supportWindowMembership supportToWindow realizationWitness
      supportWindowSourceObject sourceMembershipWitness
      supportMembershipProofObject supportMembershipEvidenceObject
      supportMembershipConcreteObject supportMembershipFinalObject
      supportMembershipSourceNormalForm supportMembershipConcreteSourceData

namespace SourceSupportWindowSupportMembershipConcreteSourceWitnessSupportCertificateData
theorem supportMembershipConcreteSourceDataRealizesSupportInWindow
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} {I : S.Window}
    {supportSet : Type} {supportMembership : supportSet → Prop}
    {supportWindowSet : Type}
    {supportWindowMembership : supportWindowSet → Prop}
    {supportToWindow : supportSet → supportWindowSet}
    {realizationWitness :
      ∀ point : supportSet,
        supportMembership point →
          supportWindowMembership (supportToWindow point) → Type}
    {supportWindowSourceObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            realizationWitness point hSupport hWindow → Type}
    {sourceMembershipWitness :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              supportWindowSourceObject
                point hSupport hWindow hRealization → Type}
    {supportMembershipProofObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                sourceMembershipWitness
                  point hSupport hWindow hRealization hSource → Type}
    {supportMembershipEvidenceObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  supportMembershipProofObject
                    point hSupport hWindow hRealization hSource hMembership →
                    Type}
    {supportMembershipConcreteObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    supportMembershipEvidenceObject
                      point hSupport hWindow hRealization hSource
                      hMembership hProof → Type}
    {supportMembershipFinalObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    ∀ hEvidence :
                      supportMembershipEvidenceObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof,
                      supportMembershipConcreteObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof hEvidence → Type}
    {supportMembershipSourceNormalForm :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    ∀ hEvidence :
                      supportMembershipEvidenceObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof,
                      ∀ hConcrete :
                        supportMembershipConcreteObject
                          point hSupport hWindow hRealization hSource
                          hMembership hProof hEvidence,
                        supportMembershipFinalObject
                          point hSupport hWindow hRealization hSource
                          hMembership hProof hEvidence hConcrete → Type}
    {supportMembershipConcreteSourceData :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    ∀ hEvidence :
                      supportMembershipEvidenceObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof,
                      ∀ hConcrete :
                        supportMembershipConcreteObject
                          point hSupport hWindow hRealization hSource
                          hMembership hProof hEvidence,
                        ∀ hFinal :
                          supportMembershipFinalObject
                            point hSupport hWindow hRealization hSource
                            hMembership hProof hEvidence hConcrete,
                          supportMembershipSourceNormalForm
                            point hSupport hWindow hRealization hSource
                            hMembership hProof hEvidence hConcrete hFinal →
                            Type}
    (D :
      SourceSupportWindowSupportMembershipConcreteSourceWitnessSupportCertificateData
        S f I supportSet supportMembership supportWindowSet
        supportWindowMembership supportToWindow realizationWitness
        supportWindowSourceObject sourceMembershipWitness
        supportMembershipProofObject supportMembershipEvidenceObject
        supportMembershipConcreteObject supportMembershipFinalObject
        supportMembershipSourceNormalForm supportMembershipConcreteSourceData) :
    ∀ point : supportSet,
      ∀ hSupport : supportMembership point,
        ∀ hWindow :
          supportWindowMembership (supportToWindow point),
          ∀ hRealization :
            realizationWitness point hSupport hWindow,
            ∀ hSource :
              supportWindowSourceObject
                point hSupport hWindow hRealization,
              ∀ hMembership :
                sourceMembershipWitness
                  point hSupport hWindow hRealization hSource,
                ∀ hProof :
                  supportMembershipProofObject
                    point hSupport hWindow hRealization hSource hMembership,
                  ∀ hEvidence :
                    supportMembershipEvidenceObject
                      point hSupport hWindow hRealization hSource
                      hMembership hProof,
                    ∀ hConcrete :
                      supportMembershipConcreteObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof hEvidence,
                      ∀ hFinal :
                        supportMembershipFinalObject
                          point hSupport hWindow hRealization hSource
                          hMembership hProof hEvidence hConcrete,
                        ∀ hNormal :
                          supportMembershipSourceNormalForm
                            point hSupport hWindow hRealization hSource
                            hMembership hProof hEvidence hConcrete hFinal,
                          supportMembershipConcreteSourceData
                            point hSupport hWindow hRealization hSource
                            hMembership hProof hEvidence hConcrete hFinal
                            hNormal →
                            S.supportInWindow f I := by
  exact
    D.supportMembershipConcreteSourceWitnessSupportWitnessData
      |>.supportMembershipConcreteSourceDataRealizesSupportInWindow
end SourceSupportWindowSupportMembershipConcreteSourceWitnessSupportCertificateData

structure SourceSupportWindowSupportMembershipConcreteSourceWitnessSupportProofData
    {A : SourceTestAlgebra} (S : SourceSupportWindowData A)
    (f : A.Test) (I : S.Window)
    (supportSet : Type) (supportMembership : supportSet → Prop)
    (supportWindowSet : Type)
    (supportWindowMembership : supportWindowSet → Prop)
    (supportToWindow : supportSet → supportWindowSet)
    (realizationWitness :
      ∀ point : supportSet,
        supportMembership point →
          supportWindowMembership (supportToWindow point) → Type)
    (supportWindowSourceObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            realizationWitness point hSupport hWindow → Type)
    (sourceMembershipWitness :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              supportWindowSourceObject
                point hSupport hWindow hRealization → Type)
    (supportMembershipProofObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                sourceMembershipWitness
                  point hSupport hWindow hRealization hSource → Type)
    (supportMembershipEvidenceObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  supportMembershipProofObject
                    point hSupport hWindow hRealization hSource hMembership →
                    Type)
    (supportMembershipConcreteObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    supportMembershipEvidenceObject
                      point hSupport hWindow hRealization hSource
                      hMembership hProof → Type)
    (supportMembershipFinalObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    ∀ hEvidence :
                      supportMembershipEvidenceObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof,
                      supportMembershipConcreteObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof hEvidence → Type)
    (supportMembershipSourceNormalForm :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    ∀ hEvidence :
                      supportMembershipEvidenceObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof,
                      ∀ hConcrete :
                        supportMembershipConcreteObject
                          point hSupport hWindow hRealization hSource
                          hMembership hProof hEvidence,
                        supportMembershipFinalObject
                          point hSupport hWindow hRealization hSource
                          hMembership hProof hEvidence hConcrete → Type)
    (supportMembershipConcreteSourceData :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    ∀ hEvidence :
                      supportMembershipEvidenceObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof,
                      ∀ hConcrete :
                        supportMembershipConcreteObject
                          point hSupport hWindow hRealization hSource
                          hMembership hProof hEvidence,
                        ∀ hFinal :
                          supportMembershipFinalObject
                            point hSupport hWindow hRealization hSource
                            hMembership hProof hEvidence hConcrete,
                          supportMembershipSourceNormalForm
                            point hSupport hWindow hRealization hSource
                            hMembership hProof hEvidence hConcrete hFinal →
                            Type) where
  supportMembershipConcreteSourceWitnessSupportCertificateData :
    SourceSupportWindowSupportMembershipConcreteSourceWitnessSupportCertificateData
      S f I supportSet supportMembership supportWindowSet
      supportWindowMembership supportToWindow realizationWitness
      supportWindowSourceObject sourceMembershipWitness
      supportMembershipProofObject supportMembershipEvidenceObject
      supportMembershipConcreteObject supportMembershipFinalObject
      supportMembershipSourceNormalForm supportMembershipConcreteSourceData

namespace SourceSupportWindowSupportMembershipConcreteSourceWitnessSupportProofData
theorem supportMembershipConcreteSourceDataRealizesSupportInWindow
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} {I : S.Window}
    {supportSet : Type} {supportMembership : supportSet → Prop}
    {supportWindowSet : Type}
    {supportWindowMembership : supportWindowSet → Prop}
    {supportToWindow : supportSet → supportWindowSet}
    {realizationWitness :
      ∀ point : supportSet,
        supportMembership point →
          supportWindowMembership (supportToWindow point) → Type}
    {supportWindowSourceObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            realizationWitness point hSupport hWindow → Type}
    {sourceMembershipWitness :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              supportWindowSourceObject
                point hSupport hWindow hRealization → Type}
    {supportMembershipProofObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                sourceMembershipWitness
                  point hSupport hWindow hRealization hSource → Type}
    {supportMembershipEvidenceObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  supportMembershipProofObject
                    point hSupport hWindow hRealization hSource hMembership →
                    Type}
    {supportMembershipConcreteObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    supportMembershipEvidenceObject
                      point hSupport hWindow hRealization hSource
                      hMembership hProof → Type}
    {supportMembershipFinalObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    ∀ hEvidence :
                      supportMembershipEvidenceObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof,
                      supportMembershipConcreteObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof hEvidence → Type}
    {supportMembershipSourceNormalForm :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    ∀ hEvidence :
                      supportMembershipEvidenceObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof,
                      ∀ hConcrete :
                        supportMembershipConcreteObject
                          point hSupport hWindow hRealization hSource
                          hMembership hProof hEvidence,
                        supportMembershipFinalObject
                          point hSupport hWindow hRealization hSource
                          hMembership hProof hEvidence hConcrete → Type}
    {supportMembershipConcreteSourceData :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    ∀ hEvidence :
                      supportMembershipEvidenceObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof,
                      ∀ hConcrete :
                        supportMembershipConcreteObject
                          point hSupport hWindow hRealization hSource
                          hMembership hProof hEvidence,
                        ∀ hFinal :
                          supportMembershipFinalObject
                            point hSupport hWindow hRealization hSource
                            hMembership hProof hEvidence hConcrete,
                          supportMembershipSourceNormalForm
                            point hSupport hWindow hRealization hSource
                            hMembership hProof hEvidence hConcrete hFinal →
                            Type}
    (D :
      SourceSupportWindowSupportMembershipConcreteSourceWitnessSupportProofData
        S f I supportSet supportMembership supportWindowSet
        supportWindowMembership supportToWindow realizationWitness
        supportWindowSourceObject sourceMembershipWitness
        supportMembershipProofObject supportMembershipEvidenceObject
        supportMembershipConcreteObject supportMembershipFinalObject
        supportMembershipSourceNormalForm supportMembershipConcreteSourceData) :
    ∀ point : supportSet,
      ∀ hSupport : supportMembership point,
        ∀ hWindow :
          supportWindowMembership (supportToWindow point),
          ∀ hRealization :
            realizationWitness point hSupport hWindow,
            ∀ hSource :
              supportWindowSourceObject
                point hSupport hWindow hRealization,
              ∀ hMembership :
                sourceMembershipWitness
                  point hSupport hWindow hRealization hSource,
                ∀ hProof :
                  supportMembershipProofObject
                    point hSupport hWindow hRealization hSource hMembership,
                  ∀ hEvidence :
                    supportMembershipEvidenceObject
                      point hSupport hWindow hRealization hSource
                      hMembership hProof,
                    ∀ hConcrete :
                      supportMembershipConcreteObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof hEvidence,
                      ∀ hFinal :
                        supportMembershipFinalObject
                          point hSupport hWindow hRealization hSource
                          hMembership hProof hEvidence hConcrete,
                        ∀ hNormal :
                          supportMembershipSourceNormalForm
                            point hSupport hWindow hRealization hSource
                            hMembership hProof hEvidence hConcrete hFinal,
                          supportMembershipConcreteSourceData
                            point hSupport hWindow hRealization hSource
                            hMembership hProof hEvidence hConcrete hFinal
                            hNormal →
                            S.supportInWindow f I := by
  exact
    D.supportMembershipConcreteSourceWitnessSupportCertificateData
      |>.supportMembershipConcreteSourceDataRealizesSupportInWindow
end SourceSupportWindowSupportMembershipConcreteSourceWitnessSupportProofData

structure SourceSupportWindowSupportMembershipConcreteSourceWitnessSupportRealizationData
    {A : SourceTestAlgebra} (S : SourceSupportWindowData A)
    (f : A.Test) (I : S.Window)
    (supportSet : Type) (supportMembership : supportSet → Prop)
    (supportWindowSet : Type)
    (supportWindowMembership : supportWindowSet → Prop)
    (supportToWindow : supportSet → supportWindowSet)
    (realizationWitness :
      ∀ point : supportSet,
        supportMembership point →
          supportWindowMembership (supportToWindow point) → Type)
    (supportWindowSourceObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            realizationWitness point hSupport hWindow → Type)
    (sourceMembershipWitness :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              supportWindowSourceObject
                point hSupport hWindow hRealization → Type)
    (supportMembershipProofObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                sourceMembershipWitness
                  point hSupport hWindow hRealization hSource → Type)
    (supportMembershipEvidenceObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  supportMembershipProofObject
                    point hSupport hWindow hRealization hSource hMembership →
                    Type)
    (supportMembershipConcreteObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    supportMembershipEvidenceObject
                      point hSupport hWindow hRealization hSource
                      hMembership hProof → Type)
    (supportMembershipFinalObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    ∀ hEvidence :
                      supportMembershipEvidenceObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof,
                      supportMembershipConcreteObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof hEvidence → Type)
    (supportMembershipSourceNormalForm :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    ∀ hEvidence :
                      supportMembershipEvidenceObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof,
                      ∀ hConcrete :
                        supportMembershipConcreteObject
                          point hSupport hWindow hRealization hSource
                          hMembership hProof hEvidence,
                        supportMembershipFinalObject
                          point hSupport hWindow hRealization hSource
                          hMembership hProof hEvidence hConcrete → Type)
    (supportMembershipConcreteSourceData :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    ∀ hEvidence :
                      supportMembershipEvidenceObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof,
                      ∀ hConcrete :
                        supportMembershipConcreteObject
                          point hSupport hWindow hRealization hSource
                          hMembership hProof hEvidence,
                        ∀ hFinal :
                          supportMembershipFinalObject
                            point hSupport hWindow hRealization hSource
                            hMembership hProof hEvidence hConcrete,
                          supportMembershipSourceNormalForm
                            point hSupport hWindow hRealization hSource
                            hMembership hProof hEvidence hConcrete hFinal →
                            Type) where
  supportMembershipConcreteSourceWitnessSupportProofData :
    SourceSupportWindowSupportMembershipConcreteSourceWitnessSupportProofData
      S f I supportSet supportMembership supportWindowSet
      supportWindowMembership supportToWindow realizationWitness
      supportWindowSourceObject sourceMembershipWitness
      supportMembershipProofObject supportMembershipEvidenceObject
      supportMembershipConcreteObject supportMembershipFinalObject
      supportMembershipSourceNormalForm supportMembershipConcreteSourceData

namespace SourceSupportWindowSupportMembershipConcreteSourceWitnessSupportRealizationData

theorem supportMembershipConcreteSourceDataRealizesSupportInWindow
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} {I : S.Window}
    {supportSet : Type} {supportMembership : supportSet → Prop}
    {supportWindowSet : Type}
    {supportWindowMembership : supportWindowSet → Prop}
    {supportToWindow : supportSet → supportWindowSet}
    {realizationWitness :
      ∀ point : supportSet,
        supportMembership point →
          supportWindowMembership (supportToWindow point) → Type}
    {supportWindowSourceObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            realizationWitness point hSupport hWindow → Type}
    {sourceMembershipWitness :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              supportWindowSourceObject
                point hSupport hWindow hRealization → Type}
    {supportMembershipProofObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                sourceMembershipWitness
                  point hSupport hWindow hRealization hSource → Type}
    {supportMembershipEvidenceObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  supportMembershipProofObject
                    point hSupport hWindow hRealization hSource hMembership →
                    Type}
    {supportMembershipConcreteObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    supportMembershipEvidenceObject
                      point hSupport hWindow hRealization hSource
                      hMembership hProof → Type}
    {supportMembershipFinalObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    ∀ hEvidence :
                      supportMembershipEvidenceObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof,
                      supportMembershipConcreteObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof hEvidence → Type}
    {supportMembershipSourceNormalForm :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    ∀ hEvidence :
                      supportMembershipEvidenceObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof,
                      ∀ hConcrete :
                        supportMembershipConcreteObject
                          point hSupport hWindow hRealization hSource
                          hMembership hProof hEvidence,
                        supportMembershipFinalObject
                          point hSupport hWindow hRealization hSource
                          hMembership hProof hEvidence hConcrete → Type}
    {supportMembershipConcreteSourceData :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    ∀ hEvidence :
                      supportMembershipEvidenceObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof,
                      ∀ hConcrete :
                        supportMembershipConcreteObject
                          point hSupport hWindow hRealization hSource
                          hMembership hProof hEvidence,
                        ∀ hFinal :
                          supportMembershipFinalObject
                            point hSupport hWindow hRealization hSource
                            hMembership hProof hEvidence hConcrete,
                          supportMembershipSourceNormalForm
                            point hSupport hWindow hRealization hSource
                            hMembership hProof hEvidence hConcrete hFinal →
                            Type}
    (D :
      SourceSupportWindowSupportMembershipConcreteSourceWitnessSupportRealizationData
        S f I supportSet supportMembership supportWindowSet
        supportWindowMembership supportToWindow realizationWitness
        supportWindowSourceObject sourceMembershipWitness
        supportMembershipProofObject supportMembershipEvidenceObject
        supportMembershipConcreteObject supportMembershipFinalObject
        supportMembershipSourceNormalForm supportMembershipConcreteSourceData) :
    ∀ point : supportSet,
      ∀ hSupport : supportMembership point,
        ∀ hWindow :
          supportWindowMembership (supportToWindow point),
          ∀ hRealization :
            realizationWitness point hSupport hWindow,
            ∀ hSource :
              supportWindowSourceObject
                point hSupport hWindow hRealization,
              ∀ hMembership :
                sourceMembershipWitness
                  point hSupport hWindow hRealization hSource,
                ∀ hProof :
                  supportMembershipProofObject
                    point hSupport hWindow hRealization hSource hMembership,
                  ∀ hEvidence :
                    supportMembershipEvidenceObject
                      point hSupport hWindow hRealization hSource
                      hMembership hProof,
                    ∀ hConcrete :
                      supportMembershipConcreteObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof hEvidence,
                      ∀ hFinal :
                        supportMembershipFinalObject
                          point hSupport hWindow hRealization hSource
                          hMembership hProof hEvidence hConcrete,
                        ∀ hNormal :
                          supportMembershipSourceNormalForm
                            point hSupport hWindow hRealization hSource
                            hMembership hProof hEvidence hConcrete hFinal,
                          supportMembershipConcreteSourceData
                            point hSupport hWindow hRealization hSource
                            hMembership hProof hEvidence hConcrete hFinal
                            hNormal →
                            S.supportInWindow f I := by
  intro point hSupport hWindow hRealization hSource hMembership hProof
    hEvidence hConcrete hFinal hNormal hConcreteSource
  exact
    D.supportMembershipConcreteSourceWitnessSupportProofData
      |>.supportMembershipConcreteSourceDataRealizesSupportInWindow
      point hSupport hWindow hRealization hSource hMembership hProof
      hEvidence hConcrete hFinal hNormal hConcreteSource

end SourceSupportWindowSupportMembershipConcreteSourceWitnessSupportRealizationData

structure SourceSupportWindowSupportMembershipConcreteSourceWitnessRealizationData
    {A : SourceTestAlgebra} (S : SourceSupportWindowData A)
    (f : A.Test) (I : S.Window)
    (supportSet : Type) (supportMembership : supportSet → Prop)
    (supportWindowSet : Type)
    (supportWindowMembership : supportWindowSet → Prop)
    (supportToWindow : supportSet → supportWindowSet)
    (realizationWitness :
      ∀ point : supportSet,
        supportMembership point →
          supportWindowMembership (supportToWindow point) → Type)
    (supportWindowSourceObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            realizationWitness point hSupport hWindow → Type)
    (sourceMembershipWitness :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              supportWindowSourceObject
                point hSupport hWindow hRealization → Type)
    (supportMembershipProofObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                sourceMembershipWitness
                  point hSupport hWindow hRealization hSource → Type)
    (supportMembershipEvidenceObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  supportMembershipProofObject
                    point hSupport hWindow hRealization hSource hMembership →
                    Type)
    (supportMembershipConcreteObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    supportMembershipEvidenceObject
                      point hSupport hWindow hRealization hSource
                      hMembership hProof → Type)
    (supportMembershipFinalObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    ∀ hEvidence :
                      supportMembershipEvidenceObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof,
                      supportMembershipConcreteObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof hEvidence → Type)
    (supportMembershipSourceNormalForm :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    ∀ hEvidence :
                      supportMembershipEvidenceObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof,
                      ∀ hConcrete :
                        supportMembershipConcreteObject
                          point hSupport hWindow hRealization hSource
                          hMembership hProof hEvidence,
                        supportMembershipFinalObject
                          point hSupport hWindow hRealization hSource
                          hMembership hProof hEvidence hConcrete → Type)
    (supportMembershipConcreteSourceData :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    ∀ hEvidence :
                      supportMembershipEvidenceObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof,
                      ∀ hConcrete :
                        supportMembershipConcreteObject
                          point hSupport hWindow hRealization hSource
                          hMembership hProof hEvidence,
                        ∀ hFinal :
                          supportMembershipFinalObject
                            point hSupport hWindow hRealization hSource
                            hMembership hProof hEvidence hConcrete,
                          supportMembershipSourceNormalForm
                            point hSupport hWindow hRealization hSource
                            hMembership hProof hEvidence hConcrete hFinal →
                            Type) where
  supportMembershipConcreteSourceWitnessSupportRealizationData :
    SourceSupportWindowSupportMembershipConcreteSourceWitnessSupportRealizationData
      S f I supportSet supportMembership supportWindowSet
      supportWindowMembership supportToWindow realizationWitness
      supportWindowSourceObject sourceMembershipWitness
      supportMembershipProofObject supportMembershipEvidenceObject
      supportMembershipConcreteObject supportMembershipFinalObject
      supportMembershipSourceNormalForm supportMembershipConcreteSourceData

namespace SourceSupportWindowSupportMembershipConcreteSourceWitnessRealizationData

theorem supportMembershipConcreteSourceDataRealizesSupportInWindow
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} {I : S.Window}
    {supportSet : Type} {supportMembership : supportSet → Prop}
    {supportWindowSet : Type}
    {supportWindowMembership : supportWindowSet → Prop}
    {supportToWindow : supportSet → supportWindowSet}
    {realizationWitness :
      ∀ point : supportSet,
        supportMembership point →
          supportWindowMembership (supportToWindow point) → Type}
    {supportWindowSourceObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            realizationWitness point hSupport hWindow → Type}
    {sourceMembershipWitness :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              supportWindowSourceObject
                point hSupport hWindow hRealization → Type}
    {supportMembershipProofObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                sourceMembershipWitness
                  point hSupport hWindow hRealization hSource → Type}
    {supportMembershipEvidenceObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  supportMembershipProofObject
                    point hSupport hWindow hRealization hSource hMembership →
                    Type}
    {supportMembershipConcreteObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    supportMembershipEvidenceObject
                      point hSupport hWindow hRealization hSource
                      hMembership hProof → Type}
    {supportMembershipFinalObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    ∀ hEvidence :
                      supportMembershipEvidenceObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof,
                      supportMembershipConcreteObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof hEvidence → Type}
    {supportMembershipSourceNormalForm :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    ∀ hEvidence :
                      supportMembershipEvidenceObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof,
                      ∀ hConcrete :
                        supportMembershipConcreteObject
                          point hSupport hWindow hRealization hSource
                          hMembership hProof hEvidence,
                        supportMembershipFinalObject
                          point hSupport hWindow hRealization hSource
                          hMembership hProof hEvidence hConcrete → Type}
    {supportMembershipConcreteSourceData :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    ∀ hEvidence :
                      supportMembershipEvidenceObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof,
                      ∀ hConcrete :
                        supportMembershipConcreteObject
                          point hSupport hWindow hRealization hSource
                          hMembership hProof hEvidence,
                        ∀ hFinal :
                          supportMembershipFinalObject
                            point hSupport hWindow hRealization hSource
                            hMembership hProof hEvidence hConcrete,
                          supportMembershipSourceNormalForm
                            point hSupport hWindow hRealization hSource
                            hMembership hProof hEvidence hConcrete hFinal →
                            Type}
    (D :
      SourceSupportWindowSupportMembershipConcreteSourceWitnessRealizationData
        S f I supportSet supportMembership supportWindowSet
        supportWindowMembership supportToWindow realizationWitness
        supportWindowSourceObject sourceMembershipWitness
        supportMembershipProofObject supportMembershipEvidenceObject
        supportMembershipConcreteObject supportMembershipFinalObject
        supportMembershipSourceNormalForm supportMembershipConcreteSourceData) :
    ∀ point : supportSet,
      ∀ hSupport : supportMembership point,
        ∀ hWindow :
          supportWindowMembership (supportToWindow point),
          ∀ hRealization :
            realizationWitness point hSupport hWindow,
            ∀ hSource :
              supportWindowSourceObject
                point hSupport hWindow hRealization,
              ∀ hMembership :
                sourceMembershipWitness
                  point hSupport hWindow hRealization hSource,
                ∀ hProof :
                  supportMembershipProofObject
                    point hSupport hWindow hRealization hSource hMembership,
                  ∀ hEvidence :
                    supportMembershipEvidenceObject
                      point hSupport hWindow hRealization hSource
                      hMembership hProof,
                    ∀ hConcrete :
                      supportMembershipConcreteObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof hEvidence,
                      ∀ hFinal :
                        supportMembershipFinalObject
                          point hSupport hWindow hRealization hSource
                          hMembership hProof hEvidence hConcrete,
                        ∀ hNormal :
                          supportMembershipSourceNormalForm
                            point hSupport hWindow hRealization hSource
                            hMembership hProof hEvidence hConcrete hFinal,
                          supportMembershipConcreteSourceData
                            point hSupport hWindow hRealization hSource
                            hMembership hProof hEvidence hConcrete hFinal
                            hNormal →
                            S.supportInWindow f I := by
  intro point hSupport hWindow hRealization hSource hMembership hProof
    hEvidence hConcrete hFinal hNormal hConcreteSource
  exact
    D.supportMembershipConcreteSourceWitnessSupportRealizationData
      |>.supportMembershipConcreteSourceDataRealizesSupportInWindow
      point hSupport hWindow hRealization hSource hMembership hProof
      hEvidence hConcrete hFinal hNormal hConcreteSource

end SourceSupportWindowSupportMembershipConcreteSourceWitnessRealizationData

structure SourceSupportWindowSupportMembershipConcreteSourceDataRealizationData
    {A : SourceTestAlgebra} (S : SourceSupportWindowData A)
    (f : A.Test) (I : S.Window)
    (supportSet : Type) (supportMembership : supportSet → Prop)
    (supportWindowSet : Type)
    (supportWindowMembership : supportWindowSet → Prop)
    (supportToWindow : supportSet → supportWindowSet)
    (realizationWitness :
      ∀ point : supportSet,
        supportMembership point →
          supportWindowMembership (supportToWindow point) → Type)
    (supportWindowSourceObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            realizationWitness point hSupport hWindow → Type)
    (sourceMembershipWitness :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              supportWindowSourceObject
                point hSupport hWindow hRealization → Type)
    (supportMembershipProofObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                sourceMembershipWitness
                  point hSupport hWindow hRealization hSource → Type)
    (supportMembershipEvidenceObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  supportMembershipProofObject
                    point hSupport hWindow hRealization hSource hMembership →
                    Type)
    (supportMembershipConcreteObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    supportMembershipEvidenceObject
                      point hSupport hWindow hRealization hSource
                      hMembership hProof → Type)
    (supportMembershipFinalObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    ∀ hEvidence :
                      supportMembershipEvidenceObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof,
                      supportMembershipConcreteObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof hEvidence → Type)
    (supportMembershipSourceNormalForm :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    ∀ hEvidence :
                      supportMembershipEvidenceObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof,
                      ∀ hConcrete :
                        supportMembershipConcreteObject
                          point hSupport hWindow hRealization hSource
                          hMembership hProof hEvidence,
                        supportMembershipFinalObject
                          point hSupport hWindow hRealization hSource
                          hMembership hProof hEvidence hConcrete → Type)
    (supportMembershipConcreteSourceData :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    ∀ hEvidence :
                      supportMembershipEvidenceObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof,
                      ∀ hConcrete :
                        supportMembershipConcreteObject
                          point hSupport hWindow hRealization hSource
                          hMembership hProof hEvidence,
                        ∀ hFinal :
                          supportMembershipFinalObject
                            point hSupport hWindow hRealization hSource
                            hMembership hProof hEvidence hConcrete,
                          supportMembershipSourceNormalForm
                            point hSupport hWindow hRealization hSource
                            hMembership hProof hEvidence hConcrete hFinal →
                            Type) where
  supportMembershipConcreteSourceWitnessRealizationData :
    SourceSupportWindowSupportMembershipConcreteSourceWitnessRealizationData
      S f I supportSet supportMembership supportWindowSet
      supportWindowMembership supportToWindow realizationWitness
      supportWindowSourceObject sourceMembershipWitness
      supportMembershipProofObject supportMembershipEvidenceObject
      supportMembershipConcreteObject supportMembershipFinalObject
      supportMembershipSourceNormalForm supportMembershipConcreteSourceData

namespace SourceSupportWindowSupportMembershipConcreteSourceDataRealizationData

theorem supportMembershipConcreteSourceDataRealizesSupportInWindow
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} {I : S.Window}
    {supportSet : Type} {supportMembership : supportSet → Prop}
    {supportWindowSet : Type}
    {supportWindowMembership : supportWindowSet → Prop}
    {supportToWindow : supportSet → supportWindowSet}
    {realizationWitness :
      ∀ point : supportSet,
        supportMembership point →
          supportWindowMembership (supportToWindow point) → Type}
    {supportWindowSourceObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            realizationWitness point hSupport hWindow → Type}
    {sourceMembershipWitness :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              supportWindowSourceObject
                point hSupport hWindow hRealization → Type}
    {supportMembershipProofObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                sourceMembershipWitness
                  point hSupport hWindow hRealization hSource → Type}
    {supportMembershipEvidenceObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  supportMembershipProofObject
                    point hSupport hWindow hRealization hSource hMembership →
                    Type}
    {supportMembershipConcreteObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    supportMembershipEvidenceObject
                      point hSupport hWindow hRealization hSource
                      hMembership hProof → Type}
    {supportMembershipFinalObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    ∀ hEvidence :
                      supportMembershipEvidenceObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof,
                      supportMembershipConcreteObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof hEvidence → Type}
    {supportMembershipSourceNormalForm :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    ∀ hEvidence :
                      supportMembershipEvidenceObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof,
                      ∀ hConcrete :
                        supportMembershipConcreteObject
                          point hSupport hWindow hRealization hSource
                          hMembership hProof hEvidence,
                        supportMembershipFinalObject
                          point hSupport hWindow hRealization hSource
                          hMembership hProof hEvidence hConcrete → Type}
    {supportMembershipConcreteSourceData :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    ∀ hEvidence :
                      supportMembershipEvidenceObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof,
                      ∀ hConcrete :
                        supportMembershipConcreteObject
                          point hSupport hWindow hRealization hSource
                          hMembership hProof hEvidence,
                        ∀ hFinal :
                          supportMembershipFinalObject
                            point hSupport hWindow hRealization hSource
                            hMembership hProof hEvidence hConcrete,
                          supportMembershipSourceNormalForm
                            point hSupport hWindow hRealization hSource
                            hMembership hProof hEvidence hConcrete hFinal →
                            Type}
    (D :
      SourceSupportWindowSupportMembershipConcreteSourceDataRealizationData
        S f I supportSet supportMembership supportWindowSet
        supportWindowMembership supportToWindow realizationWitness
        supportWindowSourceObject sourceMembershipWitness
        supportMembershipProofObject supportMembershipEvidenceObject
        supportMembershipConcreteObject supportMembershipFinalObject
        supportMembershipSourceNormalForm supportMembershipConcreteSourceData) :
    ∀ point : supportSet,
      ∀ hSupport : supportMembership point,
        ∀ hWindow :
          supportWindowMembership (supportToWindow point),
          ∀ hRealization :
            realizationWitness point hSupport hWindow,
            ∀ hSource :
              supportWindowSourceObject
                point hSupport hWindow hRealization,
              ∀ hMembership :
                sourceMembershipWitness
                  point hSupport hWindow hRealization hSource,
                ∀ hProof :
                  supportMembershipProofObject
                    point hSupport hWindow hRealization hSource hMembership,
                  ∀ hEvidence :
                    supportMembershipEvidenceObject
                      point hSupport hWindow hRealization hSource
                      hMembership hProof,
                    ∀ hConcrete :
                      supportMembershipConcreteObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof hEvidence,
                      ∀ hFinal :
                        supportMembershipFinalObject
                          point hSupport hWindow hRealization hSource
                          hMembership hProof hEvidence hConcrete,
                        ∀ hNormal :
                          supportMembershipSourceNormalForm
                            point hSupport hWindow hRealization hSource
                            hMembership hProof hEvidence hConcrete hFinal,
                          supportMembershipConcreteSourceData
                            point hSupport hWindow hRealization hSource
                            hMembership hProof hEvidence hConcrete hFinal
                            hNormal →
                            S.supportInWindow f I := by
  intro point hSupport hWindow hRealization hSource hMembership hProof
    hEvidence hConcrete hFinal hNormal hConcreteSource
  exact
    D.supportMembershipConcreteSourceWitnessRealizationData
      |>.supportMembershipConcreteSourceDataRealizesSupportInWindow
      point hSupport hWindow hRealization hSource hMembership hProof
      hEvidence hConcrete hFinal hNormal hConcreteSource

end SourceSupportWindowSupportMembershipConcreteSourceDataRealizationData

structure SourceSupportWindowSupportMembershipSourceNormalFormRealizationData
    {A : SourceTestAlgebra} (S : SourceSupportWindowData A)
    (f : A.Test) (I : S.Window)
    (supportSet : Type) (supportMembership : supportSet → Prop)
    (supportWindowSet : Type)
    (supportWindowMembership : supportWindowSet → Prop)
    (supportToWindow : supportSet → supportWindowSet)
    (realizationWitness :
      ∀ point : supportSet,
        supportMembership point →
          supportWindowMembership (supportToWindow point) → Type)
    (supportWindowSourceObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            realizationWitness point hSupport hWindow → Type)
    (sourceMembershipWitness :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              supportWindowSourceObject
                point hSupport hWindow hRealization → Type)
    (supportMembershipProofObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                sourceMembershipWitness
                  point hSupport hWindow hRealization hSource → Type)
    (supportMembershipEvidenceObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  supportMembershipProofObject
                    point hSupport hWindow hRealization hSource hMembership →
                    Type)
    (supportMembershipConcreteObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    supportMembershipEvidenceObject
                      point hSupport hWindow hRealization hSource
                      hMembership hProof → Type)
    (supportMembershipFinalObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    ∀ hEvidence :
                      supportMembershipEvidenceObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof,
                      supportMembershipConcreteObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof hEvidence → Type)
    (supportMembershipSourceNormalForm :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    ∀ hEvidence :
                      supportMembershipEvidenceObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof,
                      ∀ hConcrete :
                        supportMembershipConcreteObject
                          point hSupport hWindow hRealization hSource
                          hMembership hProof hEvidence,
                        supportMembershipFinalObject
                          point hSupport hWindow hRealization hSource
                          hMembership hProof hEvidence hConcrete → Type) where
  supportMembershipConcreteSourceData :
    ∀ point : supportSet,
      ∀ hSupport : supportMembership point,
        ∀ hWindow :
          supportWindowMembership (supportToWindow point),
          ∀ hRealization :
            realizationWitness point hSupport hWindow,
            ∀ hSource :
              supportWindowSourceObject
                point hSupport hWindow hRealization,
              ∀ hMembership :
                sourceMembershipWitness
                  point hSupport hWindow hRealization hSource,
                ∀ hProof :
                  supportMembershipProofObject
                    point hSupport hWindow hRealization hSource hMembership,
                  ∀ hEvidence :
                    supportMembershipEvidenceObject
                      point hSupport hWindow hRealization hSource
                      hMembership hProof,
                    ∀ hConcrete :
                      supportMembershipConcreteObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof hEvidence,
                      ∀ hFinal :
                        supportMembershipFinalObject
                          point hSupport hWindow hRealization hSource
                          hMembership hProof hEvidence hConcrete,
                        supportMembershipSourceNormalForm
                          point hSupport hWindow hRealization hSource
                          hMembership hProof hEvidence hConcrete hFinal →
                          Type
  supportMembershipConcreteSourceDataFor :
    ∀ point : supportSet,
      ∀ hSupport : supportMembership point,
        ∀ hWindow :
          supportWindowMembership (supportToWindow point),
          ∀ hRealization :
            realizationWitness point hSupport hWindow,
            ∀ hSource :
              supportWindowSourceObject
                point hSupport hWindow hRealization,
              ∀ hMembership :
                sourceMembershipWitness
                  point hSupport hWindow hRealization hSource,
                ∀ hProof :
                  supportMembershipProofObject
                    point hSupport hWindow hRealization hSource hMembership,
                  ∀ hEvidence :
                    supportMembershipEvidenceObject
                      point hSupport hWindow hRealization hSource
                      hMembership hProof,
                    ∀ hConcrete :
                      supportMembershipConcreteObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof hEvidence,
                      ∀ hFinal :
                        supportMembershipFinalObject
                          point hSupport hWindow hRealization hSource
                          hMembership hProof hEvidence hConcrete,
                        ∀ hNormal :
                          supportMembershipSourceNormalForm
                            point hSupport hWindow hRealization hSource
                            hMembership hProof hEvidence hConcrete hFinal,
                          supportMembershipConcreteSourceData
                            point hSupport hWindow hRealization hSource
                            hMembership hProof hEvidence hConcrete hFinal
                            hNormal
  supportMembershipConcreteSourceDataRealizationData :
    SourceSupportWindowSupportMembershipConcreteSourceDataRealizationData
      S f I supportSet supportMembership supportWindowSet
      supportWindowMembership supportToWindow realizationWitness
      supportWindowSourceObject sourceMembershipWitness
      supportMembershipProofObject supportMembershipEvidenceObject
      supportMembershipConcreteObject supportMembershipFinalObject
      supportMembershipSourceNormalForm supportMembershipConcreteSourceData

namespace SourceSupportWindowSupportMembershipSourceNormalFormRealizationData

theorem supportMembershipSourceNormalFormRealizesSupportInWindow
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} {I : S.Window}
    {supportSet : Type} {supportMembership : supportSet → Prop}
    {supportWindowSet : Type}
    {supportWindowMembership : supportWindowSet → Prop}
    {supportToWindow : supportSet → supportWindowSet}
    {realizationWitness :
      ∀ point : supportSet,
        supportMembership point →
          supportWindowMembership (supportToWindow point) → Type}
    {supportWindowSourceObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            realizationWitness point hSupport hWindow → Type}
    {sourceMembershipWitness :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              supportWindowSourceObject
                point hSupport hWindow hRealization → Type}
    {supportMembershipProofObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                sourceMembershipWitness
                  point hSupport hWindow hRealization hSource → Type}
    {supportMembershipEvidenceObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  supportMembershipProofObject
                    point hSupport hWindow hRealization hSource hMembership →
                    Type}
    {supportMembershipConcreteObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    supportMembershipEvidenceObject
                      point hSupport hWindow hRealization hSource
                      hMembership hProof → Type}
    {supportMembershipFinalObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    ∀ hEvidence :
                      supportMembershipEvidenceObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof,
                      supportMembershipConcreteObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof hEvidence → Type}
    {supportMembershipSourceNormalForm :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    ∀ hEvidence :
                      supportMembershipEvidenceObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof,
                      ∀ hConcrete :
                        supportMembershipConcreteObject
                          point hSupport hWindow hRealization hSource
                          hMembership hProof hEvidence,
                        supportMembershipFinalObject
                          point hSupport hWindow hRealization hSource
                          hMembership hProof hEvidence hConcrete → Type}
    (D :
      SourceSupportWindowSupportMembershipSourceNormalFormRealizationData
        S f I supportSet supportMembership supportWindowSet
        supportWindowMembership supportToWindow realizationWitness
        supportWindowSourceObject sourceMembershipWitness
        supportMembershipProofObject supportMembershipEvidenceObject
        supportMembershipConcreteObject supportMembershipFinalObject
        supportMembershipSourceNormalForm) :
    ∀ point : supportSet,
      ∀ hSupport : supportMembership point,
        ∀ hWindow :
          supportWindowMembership (supportToWindow point),
          ∀ hRealization :
            realizationWitness point hSupport hWindow,
            ∀ hSource :
              supportWindowSourceObject
                point hSupport hWindow hRealization,
              ∀ hMembership :
                sourceMembershipWitness
                  point hSupport hWindow hRealization hSource,
                ∀ hProof :
                  supportMembershipProofObject
                    point hSupport hWindow hRealization hSource hMembership,
                  ∀ hEvidence :
                    supportMembershipEvidenceObject
                      point hSupport hWindow hRealization hSource
                      hMembership hProof,
                    ∀ hConcrete :
                      supportMembershipConcreteObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof hEvidence,
                      ∀ hFinal :
                        supportMembershipFinalObject
                          point hSupport hWindow hRealization hSource
                          hMembership hProof hEvidence hConcrete,
                        supportMembershipSourceNormalForm
                          point hSupport hWindow hRealization hSource
                          hMembership hProof hEvidence hConcrete hFinal →
                          S.supportInWindow f I := by
  intro point hSupport hWindow hRealization hSource hMembership hProof
    hEvidence hConcrete hFinal hNormal
  exact
    D.supportMembershipConcreteSourceDataRealizationData
      |>.supportMembershipConcreteSourceDataRealizesSupportInWindow
      point hSupport hWindow hRealization hSource hMembership hProof
      hEvidence hConcrete hFinal hNormal
      (D.supportMembershipConcreteSourceDataFor
        point hSupport hWindow hRealization hSource hMembership hProof
        hEvidence hConcrete hFinal hNormal)

end SourceSupportWindowSupportMembershipSourceNormalFormRealizationData

structure SourceSupportWindowSupportMembershipFinalRealizationData
    {A : SourceTestAlgebra} (S : SourceSupportWindowData A)
    (f : A.Test) (I : S.Window)
    (supportSet : Type) (supportMembership : supportSet → Prop)
    (supportWindowSet : Type)
    (supportWindowMembership : supportWindowSet → Prop)
    (supportToWindow : supportSet → supportWindowSet)
    (realizationWitness :
      ∀ point : supportSet,
        supportMembership point →
          supportWindowMembership (supportToWindow point) → Type)
    (supportWindowSourceObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            realizationWitness point hSupport hWindow → Type)
    (sourceMembershipWitness :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              supportWindowSourceObject
                point hSupport hWindow hRealization → Type)
    (supportMembershipProofObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                sourceMembershipWitness
                  point hSupport hWindow hRealization hSource → Type)
    (supportMembershipEvidenceObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  supportMembershipProofObject
                    point hSupport hWindow hRealization hSource hMembership →
                    Type)
    (supportMembershipConcreteObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    supportMembershipEvidenceObject
                      point hSupport hWindow hRealization hSource
                      hMembership hProof → Type)
    (supportMembershipFinalObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    ∀ hEvidence :
                      supportMembershipEvidenceObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof,
                      supportMembershipConcreteObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof hEvidence → Type) where
  supportMembershipSourceNormalForm :
    ∀ point : supportSet,
      ∀ hSupport : supportMembership point,
        ∀ hWindow :
          supportWindowMembership (supportToWindow point),
          ∀ hRealization :
            realizationWitness point hSupport hWindow,
            ∀ hSource :
              supportWindowSourceObject
                point hSupport hWindow hRealization,
              ∀ hMembership :
                sourceMembershipWitness
                  point hSupport hWindow hRealization hSource,
                ∀ hProof :
                  supportMembershipProofObject
                    point hSupport hWindow hRealization hSource hMembership,
                  ∀ hEvidence :
                    supportMembershipEvidenceObject
                      point hSupport hWindow hRealization hSource
                      hMembership hProof,
                    ∀ hConcrete :
                      supportMembershipConcreteObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof hEvidence,
                      supportMembershipFinalObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof hEvidence hConcrete → Type
  supportMembershipSourceNormalFormFor :
    ∀ point : supportSet,
      ∀ hSupport : supportMembership point,
        ∀ hWindow :
          supportWindowMembership (supportToWindow point),
          ∀ hRealization :
            realizationWitness point hSupport hWindow,
            ∀ hSource :
              supportWindowSourceObject
                point hSupport hWindow hRealization,
              ∀ hMembership :
                sourceMembershipWitness
                  point hSupport hWindow hRealization hSource,
                ∀ hProof :
                  supportMembershipProofObject
                    point hSupport hWindow hRealization hSource hMembership,
                  ∀ hEvidence :
                    supportMembershipEvidenceObject
                      point hSupport hWindow hRealization hSource
                      hMembership hProof,
                    ∀ hConcrete :
                      supportMembershipConcreteObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof hEvidence,
                      ∀ hFinal :
                        supportMembershipFinalObject
                          point hSupport hWindow hRealization hSource
                          hMembership hProof hEvidence hConcrete,
                        supportMembershipSourceNormalForm
                          point hSupport hWindow hRealization hSource
                          hMembership hProof hEvidence hConcrete hFinal
  supportMembershipSourceNormalFormRealizationData :
    SourceSupportWindowSupportMembershipSourceNormalFormRealizationData
      S f I supportSet supportMembership supportWindowSet
      supportWindowMembership supportToWindow realizationWitness
      supportWindowSourceObject sourceMembershipWitness
      supportMembershipProofObject supportMembershipEvidenceObject
      supportMembershipConcreteObject supportMembershipFinalObject
      supportMembershipSourceNormalForm

namespace SourceSupportWindowSupportMembershipFinalRealizationData

theorem supportMembershipFinalRealizesSupportInWindow
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} {I : S.Window}
    {supportSet : Type} {supportMembership : supportSet → Prop}
    {supportWindowSet : Type}
    {supportWindowMembership : supportWindowSet → Prop}
    {supportToWindow : supportSet → supportWindowSet}
    {realizationWitness :
      ∀ point : supportSet,
        supportMembership point →
          supportWindowMembership (supportToWindow point) → Type}
    {supportWindowSourceObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            realizationWitness point hSupport hWindow → Type}
    {sourceMembershipWitness :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              supportWindowSourceObject
                point hSupport hWindow hRealization → Type}
    {supportMembershipProofObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                sourceMembershipWitness
                  point hSupport hWindow hRealization hSource → Type}
    {supportMembershipEvidenceObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  supportMembershipProofObject
                    point hSupport hWindow hRealization hSource hMembership →
                    Type}
    {supportMembershipConcreteObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    supportMembershipEvidenceObject
                      point hSupport hWindow hRealization hSource
                      hMembership hProof → Type}
    {supportMembershipFinalObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    ∀ hEvidence :
                      supportMembershipEvidenceObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof,
                      supportMembershipConcreteObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof hEvidence → Type}
    (D :
      SourceSupportWindowSupportMembershipFinalRealizationData
        S f I supportSet supportMembership supportWindowSet
        supportWindowMembership supportToWindow realizationWitness
        supportWindowSourceObject sourceMembershipWitness
        supportMembershipProofObject supportMembershipEvidenceObject
        supportMembershipConcreteObject supportMembershipFinalObject) :
    ∀ point : supportSet,
      ∀ hSupport : supportMembership point,
        ∀ hWindow :
          supportWindowMembership (supportToWindow point),
          ∀ hRealization :
            realizationWitness point hSupport hWindow,
            ∀ hSource :
              supportWindowSourceObject
                point hSupport hWindow hRealization,
              ∀ hMembership :
                sourceMembershipWitness
                  point hSupport hWindow hRealization hSource,
                ∀ hProof :
                  supportMembershipProofObject
                    point hSupport hWindow hRealization hSource hMembership,
                  ∀ hEvidence :
                    supportMembershipEvidenceObject
                      point hSupport hWindow hRealization hSource
                      hMembership hProof,
                    ∀ hConcrete :
                      supportMembershipConcreteObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof hEvidence,
                      supportMembershipFinalObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof hEvidence hConcrete →
                        S.supportInWindow f I := by
  intro point hSupport hWindow hRealization hSource hMembership hProof
    hEvidence hConcrete hFinal
  exact
    D.supportMembershipSourceNormalFormRealizationData
      |>.supportMembershipSourceNormalFormRealizesSupportInWindow
      point hSupport hWindow hRealization hSource hMembership hProof
      hEvidence hConcrete hFinal
      (D.supportMembershipSourceNormalFormFor
        point hSupport hWindow hRealization hSource hMembership hProof
        hEvidence hConcrete hFinal)

end SourceSupportWindowSupportMembershipFinalRealizationData

structure SourceSupportWindowSupportMembershipConcreteRealizationData
    {A : SourceTestAlgebra} (S : SourceSupportWindowData A)
    (f : A.Test) (I : S.Window)
    (supportSet : Type) (supportMembership : supportSet → Prop)
    (supportWindowSet : Type)
    (supportWindowMembership : supportWindowSet → Prop)
    (supportToWindow : supportSet → supportWindowSet)
    (realizationWitness :
      ∀ point : supportSet,
        supportMembership point →
          supportWindowMembership (supportToWindow point) → Type)
    (supportWindowSourceObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            realizationWitness point hSupport hWindow → Type)
    (sourceMembershipWitness :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              supportWindowSourceObject
                point hSupport hWindow hRealization → Type)
    (supportMembershipProofObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                sourceMembershipWitness
                  point hSupport hWindow hRealization hSource → Type)
    (supportMembershipEvidenceObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  supportMembershipProofObject
                    point hSupport hWindow hRealization hSource hMembership →
                    Type)
    (supportMembershipConcreteObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    supportMembershipEvidenceObject
                      point hSupport hWindow hRealization hSource
                      hMembership hProof → Type) where
  supportMembershipFinalObject :
    ∀ point : supportSet,
      ∀ hSupport : supportMembership point,
        ∀ hWindow :
          supportWindowMembership (supportToWindow point),
          ∀ hRealization :
            realizationWitness point hSupport hWindow,
            ∀ hSource :
              supportWindowSourceObject
                point hSupport hWindow hRealization,
              ∀ hMembership :
                sourceMembershipWitness
                  point hSupport hWindow hRealization hSource,
                ∀ hProof :
                  supportMembershipProofObject
                    point hSupport hWindow hRealization hSource hMembership,
                  ∀ hEvidence :
                    supportMembershipEvidenceObject
                      point hSupport hWindow hRealization hSource
                      hMembership hProof,
                    supportMembershipConcreteObject
                      point hSupport hWindow hRealization hSource
                      hMembership hProof hEvidence → Type
  supportMembershipFinalFor :
    ∀ point : supportSet,
      ∀ hSupport : supportMembership point,
        ∀ hWindow :
          supportWindowMembership (supportToWindow point),
          ∀ hRealization :
            realizationWitness point hSupport hWindow,
            ∀ hSource :
              supportWindowSourceObject
                point hSupport hWindow hRealization,
              ∀ hMembership :
                sourceMembershipWitness
                  point hSupport hWindow hRealization hSource,
                ∀ hProof :
                  supportMembershipProofObject
                    point hSupport hWindow hRealization hSource hMembership,
                  ∀ hEvidence :
                    supportMembershipEvidenceObject
                      point hSupport hWindow hRealization hSource
                      hMembership hProof,
                    ∀ hConcrete :
                      supportMembershipConcreteObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof hEvidence,
                      supportMembershipFinalObject
                        point hSupport hWindow hRealization hSource
                        hMembership hProof hEvidence hConcrete
  supportMembershipFinalRealizationData :
    SourceSupportWindowSupportMembershipFinalRealizationData
      S f I supportSet supportMembership supportWindowSet
      supportWindowMembership supportToWindow realizationWitness
      supportWindowSourceObject sourceMembershipWitness
      supportMembershipProofObject supportMembershipEvidenceObject
      supportMembershipConcreteObject supportMembershipFinalObject

namespace SourceSupportWindowSupportMembershipConcreteRealizationData

theorem supportMembershipConcreteRealizesSupportInWindow
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} {I : S.Window}
    {supportSet : Type} {supportMembership : supportSet → Prop}
    {supportWindowSet : Type}
    {supportWindowMembership : supportWindowSet → Prop}
    {supportToWindow : supportSet → supportWindowSet}
    {realizationWitness :
      ∀ point : supportSet,
        supportMembership point →
          supportWindowMembership (supportToWindow point) → Type}
    {supportWindowSourceObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            realizationWitness point hSupport hWindow → Type}
    {sourceMembershipWitness :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              supportWindowSourceObject
                point hSupport hWindow hRealization → Type}
    {supportMembershipProofObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                sourceMembershipWitness
                  point hSupport hWindow hRealization hSource → Type}
    {supportMembershipEvidenceObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  supportMembershipProofObject
                    point hSupport hWindow hRealization hSource hMembership →
                    Type}
    {supportMembershipConcreteObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  ∀ hProof :
                    supportMembershipProofObject
                      point hSupport hWindow hRealization hSource hMembership,
                    supportMembershipEvidenceObject
                      point hSupport hWindow hRealization hSource
                      hMembership hProof → Type}
    (D :
      SourceSupportWindowSupportMembershipConcreteRealizationData
        S f I supportSet supportMembership supportWindowSet
        supportWindowMembership supportToWindow realizationWitness
        supportWindowSourceObject sourceMembershipWitness
        supportMembershipProofObject supportMembershipEvidenceObject
        supportMembershipConcreteObject) :
    ∀ point : supportSet,
      ∀ hSupport : supportMembership point,
        ∀ hWindow :
          supportWindowMembership (supportToWindow point),
          ∀ hRealization :
            realizationWitness point hSupport hWindow,
            ∀ hSource :
              supportWindowSourceObject
                point hSupport hWindow hRealization,
              ∀ hMembership :
                sourceMembershipWitness
                  point hSupport hWindow hRealization hSource,
                ∀ hProof :
                  supportMembershipProofObject
                    point hSupport hWindow hRealization hSource hMembership,
                  ∀ hEvidence :
                    supportMembershipEvidenceObject
                      point hSupport hWindow hRealization hSource
                      hMembership hProof,
                    supportMembershipConcreteObject
                      point hSupport hWindow hRealization hSource
                      hMembership hProof hEvidence →
                      S.supportInWindow f I := by
  intro point hSupport hWindow hRealization hSource hMembership hProof
    hEvidence hConcrete
  exact
    D.supportMembershipFinalRealizationData.supportMembershipFinalRealizesSupportInWindow
      point hSupport hWindow hRealization hSource hMembership hProof
      hEvidence hConcrete
      (D.supportMembershipFinalFor
        point hSupport hWindow hRealization hSource hMembership hProof
        hEvidence hConcrete)

end SourceSupportWindowSupportMembershipConcreteRealizationData

structure SourceSupportWindowSupportMembershipEvidenceRealizationData
    {A : SourceTestAlgebra} (S : SourceSupportWindowData A)
    (f : A.Test) (I : S.Window)
    (supportSet : Type) (supportMembership : supportSet → Prop)
    (supportWindowSet : Type)
    (supportWindowMembership : supportWindowSet → Prop)
    (supportToWindow : supportSet → supportWindowSet)
    (realizationWitness :
      ∀ point : supportSet,
        supportMembership point →
          supportWindowMembership (supportToWindow point) → Type)
    (supportWindowSourceObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            realizationWitness point hSupport hWindow → Type)
    (sourceMembershipWitness :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              supportWindowSourceObject
                point hSupport hWindow hRealization → Type)
    (supportMembershipProofObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                sourceMembershipWitness
                  point hSupport hWindow hRealization hSource → Type)
    (supportMembershipEvidenceObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  supportMembershipProofObject
                    point hSupport hWindow hRealization hSource hMembership →
                    Type) where
  supportMembershipConcreteObject :
    ∀ point : supportSet,
      ∀ hSupport : supportMembership point,
        ∀ hWindow :
          supportWindowMembership (supportToWindow point),
          ∀ hRealization :
            realizationWitness point hSupport hWindow,
            ∀ hSource :
              supportWindowSourceObject
                point hSupport hWindow hRealization,
              ∀ hMembership :
                sourceMembershipWitness
                  point hSupport hWindow hRealization hSource,
                ∀ hProof :
                  supportMembershipProofObject
                    point hSupport hWindow hRealization hSource hMembership,
                  supportMembershipEvidenceObject
                    point hSupport hWindow hRealization hSource
                    hMembership hProof → Type
  supportMembershipConcreteFor :
    ∀ point : supportSet,
      ∀ hSupport : supportMembership point,
        ∀ hWindow :
          supportWindowMembership (supportToWindow point),
          ∀ hRealization :
            realizationWitness point hSupport hWindow,
            ∀ hSource :
              supportWindowSourceObject
                point hSupport hWindow hRealization,
              ∀ hMembership :
                sourceMembershipWitness
                  point hSupport hWindow hRealization hSource,
                ∀ hProof :
                  supportMembershipProofObject
                    point hSupport hWindow hRealization hSource hMembership,
                  ∀ hEvidence :
                    supportMembershipEvidenceObject
                      point hSupport hWindow hRealization hSource
                      hMembership hProof,
                    supportMembershipConcreteObject
                      point hSupport hWindow hRealization hSource
                      hMembership hProof hEvidence
  supportMembershipConcreteRealizationData :
    SourceSupportWindowSupportMembershipConcreteRealizationData
      S f I supportSet supportMembership supportWindowSet
      supportWindowMembership supportToWindow realizationWitness
      supportWindowSourceObject sourceMembershipWitness
      supportMembershipProofObject supportMembershipEvidenceObject
      supportMembershipConcreteObject

namespace SourceSupportWindowSupportMembershipEvidenceRealizationData

theorem supportMembershipEvidenceRealizesSupportInWindow
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} {I : S.Window}
    {supportSet : Type} {supportMembership : supportSet → Prop}
    {supportWindowSet : Type}
    {supportWindowMembership : supportWindowSet → Prop}
    {supportToWindow : supportSet → supportWindowSet}
    {realizationWitness :
      ∀ point : supportSet,
        supportMembership point →
          supportWindowMembership (supportToWindow point) → Type}
    {supportWindowSourceObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            realizationWitness point hSupport hWindow → Type}
    {sourceMembershipWitness :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              supportWindowSourceObject
                point hSupport hWindow hRealization → Type}
    {supportMembershipProofObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                sourceMembershipWitness
                  point hSupport hWindow hRealization hSource → Type}
    {supportMembershipEvidenceObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                ∀ hMembership :
                  sourceMembershipWitness
                    point hSupport hWindow hRealization hSource,
                  supportMembershipProofObject
                    point hSupport hWindow hRealization hSource hMembership →
                    Type}
    (D :
      SourceSupportWindowSupportMembershipEvidenceRealizationData
        S f I supportSet supportMembership supportWindowSet
        supportWindowMembership supportToWindow realizationWitness
        supportWindowSourceObject sourceMembershipWitness
        supportMembershipProofObject supportMembershipEvidenceObject) :
    ∀ point : supportSet,
      ∀ hSupport : supportMembership point,
        ∀ hWindow :
          supportWindowMembership (supportToWindow point),
          ∀ hRealization :
            realizationWitness point hSupport hWindow,
            ∀ hSource :
              supportWindowSourceObject
                point hSupport hWindow hRealization,
              ∀ hMembership :
                sourceMembershipWitness
                  point hSupport hWindow hRealization hSource,
                ∀ hProof :
                  supportMembershipProofObject
                    point hSupport hWindow hRealization hSource hMembership,
                  supportMembershipEvidenceObject
                    point hSupport hWindow hRealization hSource
                    hMembership hProof →
                    S.supportInWindow f I := by
  intro point hSupport hWindow hRealization hSource hMembership hProof hEvidence
  exact
    D.supportMembershipConcreteRealizationData.supportMembershipConcreteRealizesSupportInWindow
      point hSupport hWindow hRealization hSource hMembership hProof
      hEvidence
      (D.supportMembershipConcreteFor
        point hSupport hWindow hRealization hSource hMembership hProof
        hEvidence)

end SourceSupportWindowSupportMembershipEvidenceRealizationData

structure SourceSupportWindowSupportMembershipProofRealizationData
    {A : SourceTestAlgebra} (S : SourceSupportWindowData A)
    (f : A.Test) (I : S.Window)
    (supportSet : Type) (supportMembership : supportSet → Prop)
    (supportWindowSet : Type)
    (supportWindowMembership : supportWindowSet → Prop)
    (supportToWindow : supportSet → supportWindowSet)
    (realizationWitness :
      ∀ point : supportSet,
        supportMembership point →
          supportWindowMembership (supportToWindow point) → Type)
    (supportWindowSourceObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            realizationWitness point hSupport hWindow → Type)
    (sourceMembershipWitness :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              supportWindowSourceObject
                point hSupport hWindow hRealization → Type)
    (supportMembershipProofObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                sourceMembershipWitness
                  point hSupport hWindow hRealization hSource → Type) where
  supportMembershipEvidenceObject :
    ∀ point : supportSet,
      ∀ hSupport : supportMembership point,
        ∀ hWindow :
          supportWindowMembership (supportToWindow point),
          ∀ hRealization :
            realizationWitness point hSupport hWindow,
            ∀ hSource :
              supportWindowSourceObject
                point hSupport hWindow hRealization,
              ∀ hMembership :
                sourceMembershipWitness
                  point hSupport hWindow hRealization hSource,
                supportMembershipProofObject
                  point hSupport hWindow hRealization hSource hMembership →
                  Type
  supportMembershipEvidenceFor :
    ∀ point : supportSet,
      ∀ hSupport : supportMembership point,
        ∀ hWindow :
          supportWindowMembership (supportToWindow point),
          ∀ hRealization :
            realizationWitness point hSupport hWindow,
            ∀ hSource :
              supportWindowSourceObject
                point hSupport hWindow hRealization,
              ∀ hMembership :
                sourceMembershipWitness
                  point hSupport hWindow hRealization hSource,
                ∀ hProof :
                  supportMembershipProofObject
                    point hSupport hWindow hRealization hSource hMembership,
                  supportMembershipEvidenceObject
                    point hSupport hWindow hRealization hSource
                    hMembership hProof
  supportMembershipEvidenceRealizationData :
    SourceSupportWindowSupportMembershipEvidenceRealizationData
      S f I supportSet supportMembership supportWindowSet
      supportWindowMembership supportToWindow realizationWitness
      supportWindowSourceObject sourceMembershipWitness
      supportMembershipProofObject supportMembershipEvidenceObject

namespace SourceSupportWindowSupportMembershipProofRealizationData

theorem supportMembershipProofRealizesSupportInWindow
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} {I : S.Window}
    {supportSet : Type} {supportMembership : supportSet → Prop}
    {supportWindowSet : Type}
    {supportWindowMembership : supportWindowSet → Prop}
    {supportToWindow : supportSet → supportWindowSet}
    {realizationWitness :
      ∀ point : supportSet,
        supportMembership point →
          supportWindowMembership (supportToWindow point) → Type}
    {supportWindowSourceObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            realizationWitness point hSupport hWindow → Type}
    {sourceMembershipWitness :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              supportWindowSourceObject
                point hSupport hWindow hRealization → Type}
    {supportMembershipProofObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              ∀ hSource :
                supportWindowSourceObject
                  point hSupport hWindow hRealization,
                sourceMembershipWitness
                  point hSupport hWindow hRealization hSource → Type}
    (D :
      SourceSupportWindowSupportMembershipProofRealizationData
        S f I supportSet supportMembership supportWindowSet
        supportWindowMembership supportToWindow realizationWitness
        supportWindowSourceObject sourceMembershipWitness
        supportMembershipProofObject) :
    ∀ point : supportSet,
      ∀ hSupport : supportMembership point,
        ∀ hWindow :
          supportWindowMembership (supportToWindow point),
          ∀ hRealization :
            realizationWitness point hSupport hWindow,
            ∀ hSource :
              supportWindowSourceObject
                point hSupport hWindow hRealization,
              ∀ hMembership :
                sourceMembershipWitness
                  point hSupport hWindow hRealization hSource,
                supportMembershipProofObject
                  point hSupport hWindow hRealization hSource hMembership →
                  S.supportInWindow f I := by
  intro point hSupport hWindow hRealization hSource hMembership hProof
  exact
    D.supportMembershipEvidenceRealizationData.supportMembershipEvidenceRealizesSupportInWindow
      point hSupport hWindow hRealization hSource hMembership hProof
      (D.supportMembershipEvidenceFor
        point hSupport hWindow hRealization hSource hMembership hProof)

end SourceSupportWindowSupportMembershipProofRealizationData

structure SourceSupportWindowSourceMembershipRealizationData
    {A : SourceTestAlgebra} (S : SourceSupportWindowData A)
    (f : A.Test) (I : S.Window)
    (supportSet : Type) (supportMembership : supportSet → Prop)
    (supportWindowSet : Type)
    (supportWindowMembership : supportWindowSet → Prop)
    (supportToWindow : supportSet → supportWindowSet)
    (realizationWitness :
      ∀ point : supportSet,
        supportMembership point →
          supportWindowMembership (supportToWindow point) → Type)
    (supportWindowSourceObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            realizationWitness point hSupport hWindow → Type)
    (sourceMembershipWitness :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              supportWindowSourceObject
                point hSupport hWindow hRealization → Type) where
  supportMembershipProofObject :
    ∀ point : supportSet,
      ∀ hSupport : supportMembership point,
        ∀ hWindow :
          supportWindowMembership (supportToWindow point),
          ∀ hRealization :
            realizationWitness point hSupport hWindow,
            ∀ hSource :
              supportWindowSourceObject
                point hSupport hWindow hRealization,
              sourceMembershipWitness
                point hSupport hWindow hRealization hSource → Type
  supportMembershipProofFor :
    ∀ point : supportSet,
      ∀ hSupport : supportMembership point,
        ∀ hWindow :
          supportWindowMembership (supportToWindow point),
          ∀ hRealization :
            realizationWitness point hSupport hWindow,
            ∀ hSource :
              supportWindowSourceObject
                point hSupport hWindow hRealization,
              ∀ hMembership :
                sourceMembershipWitness
                  point hSupport hWindow hRealization hSource,
                supportMembershipProofObject
                  point hSupport hWindow hRealization hSource hMembership
  supportMembershipProofRealizationData :
    SourceSupportWindowSupportMembershipProofRealizationData
      S f I supportSet supportMembership supportWindowSet
      supportWindowMembership supportToWindow realizationWitness
      supportWindowSourceObject sourceMembershipWitness
      supportMembershipProofObject

namespace SourceSupportWindowSourceMembershipRealizationData

theorem sourceMembershipRealizesSupportInWindow
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} {I : S.Window}
    {supportSet : Type} {supportMembership : supportSet → Prop}
    {supportWindowSet : Type}
    {supportWindowMembership : supportWindowSet → Prop}
    {supportToWindow : supportSet → supportWindowSet}
    {realizationWitness :
      ∀ point : supportSet,
        supportMembership point →
          supportWindowMembership (supportToWindow point) → Type}
    {supportWindowSourceObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            realizationWitness point hSupport hWindow → Type}
    {sourceMembershipWitness :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            ∀ hRealization :
              realizationWitness point hSupport hWindow,
              supportWindowSourceObject
                point hSupport hWindow hRealization → Type}
    (D :
      SourceSupportWindowSourceMembershipRealizationData
        S f I supportSet supportMembership supportWindowSet
        supportWindowMembership supportToWindow realizationWitness
        supportWindowSourceObject sourceMembershipWitness) :
    ∀ point : supportSet,
      ∀ hSupport : supportMembership point,
        ∀ hWindow :
          supportWindowMembership (supportToWindow point),
          ∀ hRealization :
            realizationWitness point hSupport hWindow,
            ∀ hSource :
              supportWindowSourceObject
                point hSupport hWindow hRealization,
              sourceMembershipWitness
                point hSupport hWindow hRealization hSource →
                S.supportInWindow f I := by
  intro point hSupport hWindow hRealization hSource hMembership
  exact
    D.supportMembershipProofRealizationData.supportMembershipProofRealizesSupportInWindow
      point hSupport hWindow hRealization hSource hMembership
      (D.supportMembershipProofFor
        point hSupport hWindow hRealization hSource hMembership)

end SourceSupportWindowSourceMembershipRealizationData

structure SourceSupportWindowSourceObjectRealizationData
    {A : SourceTestAlgebra} (S : SourceSupportWindowData A)
    (f : A.Test) (I : S.Window)
    (supportSet : Type) (supportMembership : supportSet → Prop)
    (supportWindowSet : Type)
    (supportWindowMembership : supportWindowSet → Prop)
    (supportToWindow : supportSet → supportWindowSet)
    (realizationWitness :
      ∀ point : supportSet,
        supportMembership point →
          supportWindowMembership (supportToWindow point) → Type)
    (supportWindowSourceObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            realizationWitness point hSupport hWindow → Type) where
  sourceMembershipWitness :
    ∀ point : supportSet,
      ∀ hSupport : supportMembership point,
        ∀ hWindow :
          supportWindowMembership (supportToWindow point),
          ∀ hRealization :
            realizationWitness point hSupport hWindow,
            supportWindowSourceObject
              point hSupport hWindow hRealization → Type
  sourceMembershipWitnessFor :
    ∀ point : supportSet,
      ∀ hSupport : supportMembership point,
        ∀ hWindow :
          supportWindowMembership (supportToWindow point),
          ∀ hRealization :
            realizationWitness point hSupport hWindow,
            ∀ hSource :
              supportWindowSourceObject
                point hSupport hWindow hRealization,
              sourceMembershipWitness
                point hSupport hWindow hRealization hSource
  sourceMembershipRealizationData :
    SourceSupportWindowSourceMembershipRealizationData
      S f I supportSet supportMembership supportWindowSet
      supportWindowMembership supportToWindow realizationWitness
      supportWindowSourceObject sourceMembershipWitness

namespace SourceSupportWindowSourceObjectRealizationData

theorem sourceObjectRealizesSupportInWindow
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} {I : S.Window}
    {supportSet : Type} {supportMembership : supportSet → Prop}
    {supportWindowSet : Type}
    {supportWindowMembership : supportWindowSet → Prop}
    {supportToWindow : supportSet → supportWindowSet}
    {realizationWitness :
      ∀ point : supportSet,
        supportMembership point →
          supportWindowMembership (supportToWindow point) → Type}
    {supportWindowSourceObject :
      ∀ point : supportSet,
        ∀ hSupport : supportMembership point,
          ∀ hWindow :
            supportWindowMembership (supportToWindow point),
            realizationWitness point hSupport hWindow → Type}
    (D :
      SourceSupportWindowSourceObjectRealizationData
        S f I supportSet supportMembership supportWindowSet
        supportWindowMembership supportToWindow realizationWitness
        supportWindowSourceObject) :
    ∀ point : supportSet,
      ∀ hSupport : supportMembership point,
        ∀ hWindow :
          supportWindowMembership (supportToWindow point),
          ∀ hRealization :
            realizationWitness point hSupport hWindow,
            supportWindowSourceObject
              point hSupport hWindow hRealization →
              S.supportInWindow f I := by
  intro point hSupport hWindow hRealization hSource
  exact
    D.sourceMembershipRealizationData.sourceMembershipRealizesSupportInWindow
      point hSupport hWindow hRealization hSource
      (D.sourceMembershipWitnessFor
        point hSupport hWindow hRealization hSource)

end SourceSupportWindowSourceObjectRealizationData

structure SourceSupportWindowRealizationCertificate
    {A : SourceTestAlgebra} (S : SourceSupportWindowData A)
    (f : A.Test) (I : S.Window)
    (supportSet : Type) (supportMembership : supportSet → Prop)
    (supportWindowSet : Type)
    (supportWindowMembership : supportWindowSet → Prop)
    (supportToWindow : supportSet → supportWindowSet)
    (realizationWitness :
      ∀ point : supportSet,
        supportMembership point →
          supportWindowMembership (supportToWindow point) → Type) where
  supportWindowSourceObject :
    ∀ point : supportSet,
      ∀ hSupport : supportMembership point,
        ∀ hWindow :
          supportWindowMembership (supportToWindow point),
          realizationWitness point hSupport hWindow → Type
  sourceObjectFor :
    ∀ point : supportSet,
      ∀ hSupport : supportMembership point,
        ∀ hWindow :
          supportWindowMembership (supportToWindow point),
          ∀ hRealization :
            realizationWitness point hSupport hWindow,
            supportWindowSourceObject
              point hSupport hWindow hRealization
  sourceObjectRealizationData :
    SourceSupportWindowSourceObjectRealizationData
      S f I supportSet supportMembership supportWindowSet
      supportWindowMembership supportToWindow realizationWitness
      supportWindowSourceObject

namespace SourceSupportWindowRealizationCertificate

theorem realizationImpliesSupportInWindow
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} {I : S.Window}
    {supportSet : Type} {supportMembership : supportSet → Prop}
    {supportWindowSet : Type}
    {supportWindowMembership : supportWindowSet → Prop}
    {supportToWindow : supportSet → supportWindowSet}
    {realizationWitness :
      ∀ point : supportSet,
        supportMembership point →
          supportWindowMembership (supportToWindow point) → Type}
    (C :
      SourceSupportWindowRealizationCertificate
        S f I supportSet supportMembership supportWindowSet
        supportWindowMembership supportToWindow realizationWitness) :
    ∀ point : supportSet,
      ∀ hSupport : supportMembership point,
        ∀ hWindow :
          supportWindowMembership (supportToWindow point),
            realizationWitness point hSupport hWindow →
              S.supportInWindow f I := by
  intro point hSupport hWindow hRealization
  exact
    C.sourceObjectRealizationData.sourceObjectRealizesSupportInWindow
      point hSupport hWindow hRealization
      (C.sourceObjectFor point hSupport hWindow hRealization)

end SourceSupportWindowRealizationCertificate

structure SourceSupportWindowRealizationData
    {A : SourceTestAlgebra} (S : SourceSupportWindowData A)
    (f : A.Test) (I : S.Window)
    (supportSet : Type) (supportMembership : supportSet → Prop)
    (supportWindowSet : Type)
    (supportWindowMembership : supportWindowSet → Prop)
    (supportToWindow : supportSet → supportWindowSet) where
  realizationWitness :
    ∀ point : supportSet,
      supportMembership point →
        supportWindowMembership (supportToWindow point) → Type
  realizationWitnessFor :
    ∀ point : supportSet,
      ∀ hSupport : supportMembership point,
        ∀ hWindow :
          supportWindowMembership (supportToWindow point),
          realizationWitness point hSupport hWindow
  realizationCertificate :
    SourceSupportWindowRealizationCertificate
      S f I supportSet supportMembership supportWindowSet
      supportWindowMembership supportToWindow realizationWitness

namespace SourceSupportWindowRealizationData

theorem windowMembershipRealizesSupportInWindow
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} {I : S.Window}
    {supportSet : Type} {supportMembership : supportSet → Prop}
    {supportWindowSet : Type}
    {supportWindowMembership : supportWindowSet → Prop}
    {supportToWindow : supportSet → supportWindowSet}
    (D :
      SourceSupportWindowRealizationData
        S f I supportSet supportMembership supportWindowSet
        supportWindowMembership supportToWindow) :
    ∀ point : supportSet,
      supportMembership point →
        supportWindowMembership (supportToWindow point) →
          S.supportInWindow f I := by
  intro point hSupport hWindow
  exact
    D.realizationCertificate.realizationImpliesSupportInWindow
      point hSupport hWindow
      (D.realizationWitnessFor point hSupport hWindow)

end SourceSupportWindowRealizationData

structure SourceFourierSupportWindowRealizationCertificate
    {A : SourceTestAlgebra} (S : SourceSupportWindowData A)
    (f : A.Test) (I : S.Window)
    (fourierSupportSet : Type)
    (fourierSupportMembership : fourierSupportSet → Prop)
    (fourierSupportWindowSet : Type)
    (fourierSupportWindowMembership :
      fourierSupportWindowSet → Prop)
    (fourierSupportToWindow :
      fourierSupportSet → fourierSupportWindowSet)
    (realizationWitness :
      ∀ point : fourierSupportSet,
        fourierSupportMembership point →
          fourierSupportWindowMembership
            (fourierSupportToWindow point) → Type) where
  fourierSupportWindowSourceObject :
    ∀ point : fourierSupportSet,
      ∀ hSupport : fourierSupportMembership point,
        ∀ hWindow :
          fourierSupportWindowMembership
            (fourierSupportToWindow point),
          realizationWitness point hSupport hWindow → Type
  sourceObjectFor :
    ∀ point : fourierSupportSet,
      ∀ hSupport : fourierSupportMembership point,
        ∀ hWindow :
          fourierSupportWindowMembership
            (fourierSupportToWindow point),
          ∀ hRealization :
            realizationWitness point hSupport hWindow,
            fourierSupportWindowSourceObject
              point hSupport hWindow hRealization
  sourceObjectRealizesFourierSupportInWindow :
    ∀ point : fourierSupportSet,
      ∀ hSupport : fourierSupportMembership point,
        ∀ hWindow :
          fourierSupportWindowMembership
            (fourierSupportToWindow point),
          ∀ hRealization :
            realizationWitness point hSupport hWindow,
            fourierSupportWindowSourceObject
              point hSupport hWindow hRealization →
              S.fourierSupportInWindow f I

namespace SourceFourierSupportWindowRealizationCertificate

theorem realizationImpliesFourierSupportInWindow
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} {I : S.Window}
    {fourierSupportSet : Type}
    {fourierSupportMembership : fourierSupportSet → Prop}
    {fourierSupportWindowSet : Type}
    {fourierSupportWindowMembership :
      fourierSupportWindowSet → Prop}
    {fourierSupportToWindow :
      fourierSupportSet → fourierSupportWindowSet}
    {realizationWitness :
      ∀ point : fourierSupportSet,
        fourierSupportMembership point →
          fourierSupportWindowMembership
            (fourierSupportToWindow point) → Type}
    (C :
      SourceFourierSupportWindowRealizationCertificate
        S f I fourierSupportSet fourierSupportMembership
        fourierSupportWindowSet fourierSupportWindowMembership
        fourierSupportToWindow realizationWitness) :
    ∀ point : fourierSupportSet,
      ∀ hSupport : fourierSupportMembership point,
        ∀ hWindow :
          fourierSupportWindowMembership
            (fourierSupportToWindow point),
            realizationWitness point hSupport hWindow →
              S.fourierSupportInWindow f I := by
  intro point hSupport hWindow hRealization
  exact
    C.sourceObjectRealizesFourierSupportInWindow
      point hSupport hWindow hRealization
      (C.sourceObjectFor point hSupport hWindow hRealization)

end SourceFourierSupportWindowRealizationCertificate

structure SourceFourierSupportWindowRealizationData
    {A : SourceTestAlgebra} (S : SourceSupportWindowData A)
    (f : A.Test) (I : S.Window)
    (fourierSupportSet : Type)
    (fourierSupportMembership : fourierSupportSet → Prop)
    (fourierSupportWindowSet : Type)
    (fourierSupportWindowMembership :
      fourierSupportWindowSet → Prop)
    (fourierSupportToWindow :
      fourierSupportSet → fourierSupportWindowSet) where
  realizationWitness :
    ∀ point : fourierSupportSet,
      fourierSupportMembership point →
        fourierSupportWindowMembership
          (fourierSupportToWindow point) → Type
  realizationWitnessFor :
    ∀ point : fourierSupportSet,
      ∀ hSupport : fourierSupportMembership point,
        ∀ hWindow :
          fourierSupportWindowMembership
            (fourierSupportToWindow point),
          realizationWitness point hSupport hWindow
  realizationCertificate :
    SourceFourierSupportWindowRealizationCertificate
      S f I fourierSupportSet fourierSupportMembership
      fourierSupportWindowSet fourierSupportWindowMembership
      fourierSupportToWindow realizationWitness

namespace SourceFourierSupportWindowRealizationData

theorem windowMembershipRealizesFourierSupportInWindow
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} {I : S.Window}
    {fourierSupportSet : Type}
    {fourierSupportMembership : fourierSupportSet → Prop}
    {fourierSupportWindowSet : Type}
    {fourierSupportWindowMembership :
      fourierSupportWindowSet → Prop}
    {fourierSupportToWindow :
      fourierSupportSet → fourierSupportWindowSet}
    (D :
      SourceFourierSupportWindowRealizationData
        S f I fourierSupportSet fourierSupportMembership
        fourierSupportWindowSet fourierSupportWindowMembership
        fourierSupportToWindow) :
    ∀ point : fourierSupportSet,
      fourierSupportMembership point →
        fourierSupportWindowMembership
          (fourierSupportToWindow point) →
          S.fourierSupportInWindow f I := by
  intro point hSupport hWindow
  exact
    D.realizationCertificate.realizationImpliesFourierSupportInWindow
      point hSupport hWindow
      (D.realizationWitnessFor point hSupport hWindow)

end SourceFourierSupportWindowRealizationData

structure SourceFourierSupportWindowContainmentData
    {A : SourceTestAlgebra} (S : SourceSupportWindowData A)
    (f : A.Test) (I : S.Window)
    (fourierSupportSet : Type)
    (fourierSupportMembership : fourierSupportSet → Prop) where
  fourierSupportWindowSet : Type
  fourierSupportWindowMembership : fourierSupportWindowSet → Prop
  fourierSupportToWindow :
    fourierSupportSet → fourierSupportWindowSet
  fourierSupportImage_mem_window :
    ∀ point : fourierSupportSet,
      fourierSupportMembership point →
        fourierSupportWindowMembership
          (fourierSupportToWindow point)
  fourierSupportWindowRealization :
    SourceFourierSupportWindowRealizationData
      S f I fourierSupportSet fourierSupportMembership
      fourierSupportWindowSet fourierSupportWindowMembership
      fourierSupportToWindow

namespace SourceFourierSupportWindowContainmentData

theorem fourierSupportSetContainedInWindow
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} {I : S.Window}
    {fourierSupportSet : Type}
    {fourierSupportMembership : fourierSupportSet → Prop}
    (D :
      SourceFourierSupportWindowContainmentData
        S f I fourierSupportSet fourierSupportMembership) :
    ∀ point : fourierSupportSet,
      fourierSupportMembership point →
        S.fourierSupportInWindow f I := by
  intro point hpoint
  exact
    D.fourierSupportWindowRealization.windowMembershipRealizesFourierSupportInWindow
      point hpoint
      (D.fourierSupportImage_mem_window point hpoint)

end SourceFourierSupportWindowContainmentData

structure SourceSupportSetMembershipData
    {A : SourceTestAlgebra} (S : SourceSupportWindowData A)
    (f : A.Test) (I : S.Window) where
  supportSet : Type
  supportPoint : supportSet
  supportMembership : supportSet → Prop
  supportPoint_mem :
    supportMembership supportPoint
  supportWindowContainment :
    SourceSupportWindowContainmentData
      S f I supportSet supportMembership

namespace SourceSupportSetMembershipData

theorem supportInWindow
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} {I : S.Window}
    (D : SourceSupportSetMembershipData S f I) :
    S.supportInWindow f I :=
  D.supportWindowContainment.supportSetContainedInWindow
    D.supportPoint D.supportPoint_mem

end SourceSupportSetMembershipData

structure SourceFourierSupportSetMembershipData
    {A : SourceTestAlgebra} (S : SourceSupportWindowData A)
    (f : A.Test) (I : S.Window) where
  fourierSupportSet : Type
  fourierSupportPoint : fourierSupportSet
  fourierSupportMembership : fourierSupportSet → Prop
  fourierSupportPoint_mem :
    fourierSupportMembership fourierSupportPoint
  fourierSupportWindowContainment :
    SourceFourierSupportWindowContainmentData
      S f I fourierSupportSet fourierSupportMembership

namespace SourceFourierSupportSetMembershipData

theorem fourierSupportInWindow
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} {I : S.Window}
    (D : SourceFourierSupportSetMembershipData S f I) :
    S.fourierSupportInWindow f I :=
  D.fourierSupportWindowContainment.fourierSupportSetContainedInWindow
    D.fourierSupportPoint D.fourierSupportPoint_mem

end SourceFourierSupportSetMembershipData

structure SourceSupportMembershipModel
    {A : SourceTestAlgebra} (S : SourceSupportWindowData A)
    (I : S.Window) where
  supportAtom : Type
  atomTest : supportAtom → A.Test
  atomWindow : supportAtom → S.Window
  sourceAtom : supportAtom
  sourceAtomTest_eq :
    atomTest sourceAtom = S.sourceTest
  sourceAtomWindow_eq :
    atomWindow sourceAtom = I
  atomSupportMembership :
    ∀ atom : supportAtom,
      SourceSupportSetMembershipData S (atomTest atom) (atomWindow atom)

namespace SourceSupportMembershipModel

theorem sourceSupportInWindow
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} (M : SourceSupportMembershipModel S I) :
    S.supportInWindow S.sourceTest I := by
  simpa [M.sourceAtomTest_eq, M.sourceAtomWindow_eq]
    using (M.atomSupportMembership M.sourceAtom).supportInWindow

end SourceSupportMembershipModel

structure SourceFourierSupportMembershipModel
    {A : SourceTestAlgebra} (S : SourceSupportWindowData A)
    (I : S.Window) where
  fourierSupportAtom : Type
  atomTest : fourierSupportAtom → A.Test
  atomWindow : fourierSupportAtom → S.Window
  sourceAtom : fourierSupportAtom
  sourceAtomTest_eq :
    atomTest sourceAtom = S.sourceTest
  sourceAtomWindow_eq :
    atomWindow sourceAtom = I
  atomFourierSupportMembership :
    ∀ atom : fourierSupportAtom,
      SourceFourierSupportSetMembershipData
        S (atomTest atom) (atomWindow atom)

namespace SourceFourierSupportMembershipModel

theorem sourceFourierSupportInWindow
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} (M : SourceFourierSupportMembershipModel S I) :
    S.fourierSupportInWindow S.sourceTest I := by
  simpa [M.sourceAtomTest_eq, M.sourceAtomWindow_eq]
    using
      (M.atomFourierSupportMembership
        M.sourceAtom).fourierSupportInWindow

end SourceFourierSupportMembershipModel

structure SourceWindowSupportGeometry
    {A : SourceTestAlgebra} (S : SourceSupportWindowData A)
    (I : S.Window) where
  sourceSupportMembership :
    SourceSupportMembershipModel S I
  sourceFourierSupportMembership :
    SourceFourierSupportMembershipModel S I

namespace SourceWindowSupportGeometry

theorem sourceSupportInWindow
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} (G : SourceWindowSupportGeometry S I) :
    S.supportInWindow S.sourceTest I :=
  G.sourceSupportMembership.sourceSupportInWindow

theorem sourceFourierSupportInWindow
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} (G : SourceWindowSupportGeometry S I) :
    S.fourierSupportInWindow S.sourceTest I :=
  G.sourceFourierSupportMembership.sourceFourierSupportInWindow

end SourceWindowSupportGeometry

structure SourceWindowSupportNormalForm
    {A : SourceTestAlgebra} (S : SourceSupportWindowData A)
    (I : S.Window) where
  sourceSupportGeometry :
    SourceWindowSupportGeometry S I

namespace SourceWindowSupportNormalForm

theorem sourceSupportInWindow
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} (N : SourceWindowSupportNormalForm S I) :
    S.supportInWindow S.sourceTest I :=
  N.sourceSupportGeometry.sourceSupportInWindow

theorem sourceFourierSupportInWindow
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} (N : SourceWindowSupportNormalForm S I) :
    S.fourierSupportInWindow S.sourceTest I :=
  N.sourceSupportGeometry.sourceFourierSupportInWindow

end SourceWindowSupportNormalForm

structure SourceSoninComparisonCore
    {A : SourceTestAlgebra} (S : SourceSupportWindowData A)
    (I : S.Window) where
  sourceWindowSupport :
    SourceWindowSupportNormalForm S I

namespace SourceSoninComparisonCore

theorem sourceSupportTransported
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} (C : SourceSoninComparisonCore S I) :
    S.supportTransported S.sourceTest I :=
  S.supportTransported_of_supportInWindow C.sourceWindowSupport.sourceSupportInWindow

theorem sourceConvolutionSupportTransported
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} (C : SourceSoninComparisonCore S I) :
    S.convolutionSupportTransported S.sourceTest I :=
  S.convolutionSupportTransported_of_fourierSupportInWindow
    C.sourceWindowSupport.sourceFourierSupportInWindow

end SourceSoninComparisonCore

structure SourceFixedWindowExhaustionCore
    {A : SourceTestAlgebra} (S : SourceSupportWindowData A)
    (I : S.Window) (hSonin : SourceSoninComparisonCore S I) where
  sourceCanonicalModel :
    S.canonicalHilbertModel S.sourcePlaceSet
  sourceBoundedComparisonMap :
    S.boundedComparisonMap S.sourcePlaceSet
  sourceBoundedComparisonInverse :
    S.boundedComparisonInverse S.sourcePlaceSet

def soninSpaceComparison
    {A : SourceTestAlgebra} (S : SourceSupportWindowData A)
    (I : S.Window) : Prop :=
  Nonempty (SourceSoninComparisonCore S I)

def fixedWindowExhaustionCompatible
    {A : SourceTestAlgebra} (S : SourceSupportWindowData A)
    (I : S.Window) : Prop :=
  ∃ hSonin : SourceSoninComparisonCore S I,
    Nonempty (SourceFixedWindowExhaustionCore S I hSonin)

def toSemilocalModelSymbols
    {A : SourceTestAlgebra} (S : SourceSupportWindowData A) :
    SemilocalModelSymbols where
  PlaceSet := S.PlaceSet
  Window := S.Window
  Test := A.Test
  canonicalHilbertModel := S.canonicalHilbertModel
  scalingActionImplemented := S.scalingActionImplemented
  fourierGradingCompatible := S.fourierGradingCompatible
  supportInWindow := S.supportInWindow
  fourierSupportInWindow := S.fourierSupportInWindow
  supportTransported := S.supportTransported
  convolutionSupportTransported := S.convolutionSupportTransported
  windowContainedInLambda := S.windowContainedInLambda
  lambdaCompatible := S.lambdaCompatible
  boundedComparisonMap := S.boundedComparisonMap
  boundedComparisonInverse := S.boundedComparisonInverse
  soninSpaceComparison := S.soninSpaceComparison
  fixedWindowExhaustionCompatible := S.fixedWindowExhaustionCompatible

end SourceSupportWindowData

def SourceConvolutionSupportTransportStatement
    {A : SourceTestAlgebra} (S : SourceSupportWindowData A) : Prop :=
  S.convolutionSupportTransported S.sourceTest S.sourceSupportWindow

def SourceWindowLambdaCompatibilityStatement
    {A : SourceTestAlgebra} (S : SourceSupportWindowData A) : Prop :=
  ∀ lambda : ℝ,
    1 < lambda → S.lambdaCompatible S.sourceSupportWindow lambda

def SourceSoninWindow
    {A : SourceTestAlgebra} (S : SourceSupportWindowData A) : Type :=
  { I : S.Window // S.soninSpaceComparison I }

structure SourceFixedWindowSoninExhaustionNormalForm
    {A : SourceTestAlgebra} (S : SourceSupportWindowData A)
    (I : S.Window) where
  soninComparisonCore :
    SourceSupportWindowData.SourceSoninComparisonCore S I
  fixedWindowExhaustionCore :
    SourceSupportWindowData.SourceFixedWindowExhaustionCore
      S I soninComparisonCore

/-- CCM24 semilocal rows over the shared source support/window object. -/
structure SourceSemilocalRows
    {A : SourceTestAlgebra} (S : SourceSupportWindowData A) where
  sourceCCM24TestCompatibility : Prop
  sourceCanonicalModelData :
    S.canonicalHilbertModel S.sourcePlaceSet
  sourceScalingActionData :
    ∀ V : S.PlaceSet,
      S.canonicalHilbertModel V → S.scalingActionImplemented V
  sourceFourierGradingData :
    ∀ V : S.PlaceSet,
      S.canonicalHilbertModel V → S.fourierGradingCompatible V
  sourceLambdaWindowContainmentData :
    SourceSupportWindowData.SourceLambdaWindowContainmentData
      S S.sourceSupportWindow
  sourceBoundedComparisonMapData :
    ∀ V : S.PlaceSet,
      S.canonicalHilbertModel V → S.boundedComparisonMap V
  sourceBoundedComparisonInverseData :
    ∀ V : S.PlaceSet,
      S.canonicalHilbertModel V → S.boundedComparisonInverse V
  sourceFixedWindowSoninExhaustionNormalForm :
    ∀ I : S.Window,
      SourceFixedWindowSoninExhaustionNormalForm S I

namespace SourceSemilocalRows

theorem sourceCanonicalSemilocalModel
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    (rows : SourceSemilocalRows S) :
    SemilocalModelSymbols.CanonicalSemilocalModelStatement
      S.toSemilocalModelSymbols := by
  intro V hCanonical
  exact
    ⟨rows.sourceScalingActionData V hCanonical,
      rows.sourceFourierGradingData V hCanonical⟩

theorem sourceSupportInWindow
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    (rows : SourceSemilocalRows S) :
    S.supportInWindow S.sourceTest S.sourceSupportWindow := by
  exact
    (rows.sourceFixedWindowSoninExhaustionNormalForm
      S.sourceSupportWindow).soninComparisonCore
        |>.sourceWindowSupport
        |>.sourceSupportInWindow

theorem sourceFourierSupportInWindow
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    (rows : SourceSemilocalRows S) :
    S.fourierSupportInWindow S.sourceTest S.sourceSupportWindow := by
  exact
    (rows.sourceFixedWindowSoninExhaustionNormalForm
      S.sourceSupportWindow).soninComparisonCore
        |>.sourceWindowSupport
        |>.sourceFourierSupportInWindow

theorem sourceSupportAndFourierSupportTransport
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    (_rows : SourceSemilocalRows S) :
    SemilocalModelSymbols.SupportTransportStatement
      S.toSemilocalModelSymbols := by
  intro f I hSupport hFourier
  exact
    ⟨S.supportTransported_of_supportInWindow hSupport,
      S.convolutionSupportTransported_of_fourierSupportInWindow hFourier⟩

theorem sourceConvolutionSupportTransport
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    (rows : SourceSemilocalRows S) :
    SourceConvolutionSupportTransportStatement S := by
  exact
    (rows.sourceSupportAndFourierSupportTransport
      S.sourceTest S.sourceSupportWindow
      rows.sourceSupportInWindow
      rows.sourceFourierSupportInWindow).2

theorem sourceSoninSpaceComparison
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    (rows : SourceSemilocalRows S) :
    S.soninSpaceComparison S.sourceSupportWindow := by
  let normalForm :=
    rows.sourceFixedWindowSoninExhaustionNormalForm
      S.sourceSupportWindow
  exact ⟨normalForm.soninComparisonCore⟩

theorem sourceWindowContainedInLambdaData
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    (rows : SourceSemilocalRows S) :
    ∀ lambda : ℝ,
      1 < lambda → S.windowContainedInLambda S.sourceSupportWindow lambda := by
  exact rows.sourceLambdaWindowContainmentData.windowContainedInLambda

theorem sourceWindowLambdaCompatibility
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    (rows : SourceSemilocalRows S) :
    SourceWindowLambdaCompatibilityStatement S := by
  intro lambda hlambda
  exact
    S.lambdaCompatible_of_windowContainedInLambda
      (rows.sourceWindowContainedInLambdaData lambda hlambda)

theorem sourceBoundedComparisonTraceClassTransport
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    (rows : SourceSemilocalRows S) :
    SemilocalModelSymbols.BoundedComparisonStatement
      S.toSemilocalModelSymbols := by
  intro V hCanonical
  exact
    ⟨rows.sourceBoundedComparisonMapData V hCanonical,
      rows.sourceBoundedComparisonInverseData V hCanonical⟩

theorem sourceFixedWindowSoninExhaustion
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    (rows : SourceSemilocalRows S) :
    SemilocalModelSymbols.SoninComparisonStatement
      S.toSemilocalModelSymbols := by
  intro I hSonin
  let normalForm :=
    rows.sourceFixedWindowSoninExhaustionNormalForm I
  exact
    ⟨normalForm.soninComparisonCore,
      ⟨normalForm.fixedWindowExhaustionCore⟩⟩

end SourceSemilocalRows

/--
CCM25 finite-prime source arithmetic over the shared test algebra.

The global/restricted index sets are still finite `Finset ℕ` objects to match
the existing scaffold, but the data records the intended source predicates and
the two-sided exact-support laws before any route layer consumes the sums.
-/
structure SourceFinitePrimeData (A : SourceTestAlgebra) where
  globalPrimeIndexSet : Finset ℕ
  restrictedPrimeIndexSet : ℝ → Finset ℕ
  sourcePrimePowerIndex : ℕ → Prop
  sourceAtomVisible : ℕ → A.Test → Prop
  finitePrimeTerm : ℕ → A.Test → ℝ
  primePowerPairing : ℕ → A.Test → A.Test → ℝ
  vonMangoldtWeight : ℕ → ℝ
  vonMangoldtWeight_eq_source :
    ∀ n : ℕ, vonMangoldtWeight n = ArithmeticFunction.vonMangoldt n
  globalExact :
    ∀ F : A.Test, ∀ n : ℕ,
      n ∈ globalPrimeIndexSet ↔
        sourcePrimePowerIndex n ∧ sourceAtomVisible n F
  restrictedExact :
    ∀ lambda : ℝ, ∀ F : A.Test, ∀ n : ℕ,
      n ∈ restrictedPrimeIndexSet lambda ↔
        sourcePrimePowerIndex n ∧ sourceAtomVisible n F ∧
          1 < n ∧ (n : ℝ) ≤ lambda ^ 2
  globalCoverage :
    ∀ F : A.Test, ∀ n : ℕ,
      sourceAtomVisible n F → n ∈ globalPrimeIndexSet
  restrictedCoverage :
    ∀ lambda : ℝ, 1 < lambda → ∀ F : A.Test, ∀ n : ℕ,
      sourceAtomVisible n F → n ∈ restrictedPrimeIndexSet lambda
  termNormalization :
    ∀ f g : A.Test, ∀ n : ℕ,
      finitePrimeTerm n (A.convolutionStar f g) =
        vonMangoldtWeight n * primePowerPairing n f g

namespace SourceFinitePrimeData

def legacyGlobalPrimeIndexSet
    {A : SourceTestAlgebra} (P : SourceFinitePrimeData A) :
    Finset ℕ :=
  P.globalPrimeIndexSet

def legacyRestrictedPrimeIndexSet
    {A : SourceTestAlgebra} (P : SourceFinitePrimeData A) :
    ℝ → Finset ℕ :=
  P.restrictedPrimeIndexSet

def legacyFinitePrimeAtomVisible
    {A : SourceTestAlgebra} (P : SourceFinitePrimeData A) :
    ℕ → TestFunction → Prop :=
  fun n F => P.sourceAtomVisible n (A.legacy.decode F)

def legacyFinitePrimeTerm
    {A : SourceTestAlgebra} (P : SourceFinitePrimeData A) :
    ℕ → TestFunction → ℝ :=
  fun n F => P.finitePrimeTerm n (A.legacy.decode F)

def legacyPrimePowerPairing
    {A : SourceTestAlgebra} (P : SourceFinitePrimeData A) :
    ℕ → TestFunction → TestFunction → ℝ :=
  fun n f g =>
    P.primePowerPairing n (A.legacy.decode f) (A.legacy.decode g)

end SourceFinitePrimeData

/-- CCM25 global/restricted Weil-form formulas over the shared source algebra. -/
structure SourceWeilFormData (A : SourceTestAlgebra) where
  evaluation : SourceEvaluationData A
  finitePrime : SourceFinitePrimeData A
  qw : A.Test → A.Test → ℝ
  qwLambda : ℝ → A.Test → A.Test → ℝ
  psi : A.Test → ℝ
  archimedeanTerm : A.Test → ℝ
  qwDefinition :
    ∀ f g : A.Test, qw f g = psi (A.convolutionStar f g)
  psiSign :
    ∀ F : A.Test,
      psi F =
        evaluation.poleFunctional F - archimedeanTerm F -
          ∑ n ∈ finitePrime.globalPrimeIndexSet,
            finitePrime.finitePrimeTerm n F
  qwLambdaFormula :
    ∀ lambda : ℝ, 1 < lambda →
      ∀ g : A.Test,
        qwLambda lambda g g =
          archimedeanTerm (A.convolutionStar g g) +
            evaluation.polePairing g -
              ∑ n ∈ finitePrime.restrictedPrimeIndexSet lambda,
                finitePrime.vonMangoldtWeight n *
                  finitePrime.primePowerPairing n g g

namespace SourceWeilFormData

def toWeilFormSymbols
    {A : SourceTestAlgebra} (W : SourceWeilFormData A) :
    WeilFormSymbols where
  qw := fun f g => W.qw (A.legacy.decode f) (A.legacy.decode g)
  qwLambda := fun lambda f g =>
    W.qwLambda lambda (A.legacy.decode f) (A.legacy.decode g)
  psi := fun F => W.psi (A.legacy.decode F)
  convolutionStar := A.legacyConvolutionStar
  globalPrimeIndexSet := W.finitePrime.globalPrimeIndexSet
  restrictedPrimeIndexSet := W.finitePrime.restrictedPrimeIndexSet
  finitePrimeAtomVisible :=
    W.finitePrime.legacyFinitePrimeAtomVisible
  finitePrimeTerm := W.finitePrime.legacyFinitePrimeTerm
  archimedeanTerm := fun F => W.archimedeanTerm (A.legacy.decode F)
  poleFunctional := fun F => W.evaluation.poleFunctional (A.legacy.decode F)
  polePairing := fun f => W.evaluation.polePairing (A.legacy.decode f)
  primePowerPairing := W.finitePrime.legacyPrimePowerPairing
  vonMangoldtWeight := W.finitePrime.vonMangoldtWeight

theorem qw_definition_statement
    {A : SourceTestAlgebra} (W : SourceWeilFormData A) :
    WeilFormSymbols.QWDefinitionStatement W.toWeilFormSymbols := by
  intro f g
  simp [toWeilFormSymbols, SourceTestAlgebra.legacyConvolutionStar,
    W.qwDefinition]

theorem psi_sign_statement
    {A : SourceTestAlgebra} (W : SourceWeilFormData A) :
    WeilFormSymbols.PsiSignStatement W.toWeilFormSymbols := by
  intro F
  simpa [toWeilFormSymbols, SourceFinitePrimeData.legacyFinitePrimeTerm]
    using W.psiSign (A.legacy.decode F)

theorem qw_lambda_formula_statement
    {A : SourceTestAlgebra} (W : SourceWeilFormData A) :
    WeilFormSymbols.QWLambdaFormulaStatement W.toWeilFormSymbols := by
  intro lambda hlambda f
  simpa [toWeilFormSymbols, SourceTestAlgebra.legacyConvolutionStar,
    SourceFinitePrimeData.legacyPrimePowerPairing]
    using W.qwLambdaFormula lambda hlambda (A.legacy.decode f)

theorem finite_prime_term_normalization_statement
    {A : SourceTestAlgebra} (W : SourceWeilFormData A) :
    WeilFormSymbols.FinitePrimeNormalizationStatement W.toWeilFormSymbols := by
  intro f g
  refine
    { globalPrimeIndexCoverage := ?_
      restrictedPrimeIndexCoverage := ?_
      finitePrimeTermNormalization := ?_ }
  · intro n hn
    exact W.finitePrime.globalCoverage
      (A.legacy.decode (W.toWeilFormSymbols.convolutionStar f g)) n hn
  · intro lambda hlambda n hn
    exact W.finitePrime.restrictedCoverage lambda hlambda
      (A.legacy.decode (W.toWeilFormSymbols.convolutionStar f g)) n hn
  · intro n
    simpa [toWeilFormSymbols, SourceTestAlgebra.legacyConvolutionStar,
      SourceFinitePrimeData.legacyFinitePrimeTerm,
      SourceFinitePrimeData.legacyPrimePowerPairing]
      using W.finitePrime.termNormalization
        (A.legacy.decode f) (A.legacy.decode g) n

theorem pole_normalization_statement
    {A : SourceTestAlgebra} (W : SourceWeilFormData A) :
    WeilFormSymbols.PoleNormalizationStatement W.toWeilFormSymbols := by
  intro f
  calc
    W.toWeilFormSymbols.polePairing f =
        W.evaluation.poleFunctional (A.convolutionSquare (A.legacy.decode f)) :=
      W.evaluation.polePairing_eq_functional_square (A.legacy.decode f)
    _ = W.toWeilFormSymbols.poleFunctional
        (W.toWeilFormSymbols.convolutionStar f f) := by
      simp [toWeilFormSymbols, SourceTestAlgebra.legacyConvolutionStar,
        A.convolutionSquare_eq (A.legacy.decode f)]

end SourceWeilFormData

/-- CC20 trace-scale source data over the shared test object. -/
structure SourceTraceScaleData (A : SourceTestAlgebra) where
  traceAmplitude : A.Test → ℝ
  traceClass : A.Test → Prop
  cyclicLegal : A.Test → Prop
  hilbertSchmidtGate : A.Test → Prop
  supportSquareTrace : A.Test → ℝ
  sourceNoDefectTrace : A.Test → ℝ
  positiveTrace : A.Test → ℝ
  supportSquareTrace_eq_amplitude_sq :
    ∀ g : A.Test, supportSquareTrace g = traceAmplitude g ^ 2
  positiveTrace_eq_supportSquare :
    ∀ g : A.Test, positiveTrace g = supportSquareTrace g
  traceClass_of_hilbertSchmidt :
    ∀ g : A.Test, hilbertSchmidtGate g → traceClass g
  cyclicLegal_of_hilbertSchmidt :
    ∀ g : A.Test, hilbertSchmidtGate g → cyclicLegal g

namespace SourceTraceScaleData

def toNormalizedLegalSquareTraceScaleSymbols
    {A : SourceTestAlgebra} (T : SourceTraceScaleData A) :
    CC20Concrete.TraceScale.NormalizedLegalSquareTraceScaleSymbols where
  Test := A.Test
  traceAmplitude := T.traceAmplitude
  traceClass := T.traceClass
  cyclicLegal := T.cyclicLegal

def toArchimedeanTraceSymbols
    {A : SourceTestAlgebra} (T : SourceTraceScaleData A) :
    ArchimedeanTraceSymbols where
  Test := A.Test
  supportSquareTrace := T.supportSquareTrace
  sourceNoDefectTrace := T.sourceNoDefectTrace
  positiveTrace := T.positiveTrace
  traceClass := T.traceClass
  cyclicLegal := T.cyclicLegal
  hilbertSchmidtGate := T.hilbertSchmidtGate
  mellinHalfDensityMatched := True
  uInfinityNormalized := True
  qduNormalized := True
  archimedeanSignNormalized := True

end SourceTraceScaleData

/-- The shared core object consumed by CCM24, CCM25, and CC20. -/
structure SourceAnalyticCore where
  testAlgebra : SourceTestAlgebra
  evaluation : SourceEvaluationData testAlgebra
  supportWindow : SourceSupportWindowData testAlgebra
  weilForm : SourceWeilFormData testAlgebra
  traceScale : SourceTraceScaleData testAlgebra
  weilForm_uses_evaluation : weilForm.evaluation = evaluation

namespace SourceAnalyticCore

def toWeilFormSymbols (core : SourceAnalyticCore) : WeilFormSymbols :=
  core.weilForm.toWeilFormSymbols

def toSemilocalModelSymbols (core : SourceAnalyticCore) :
    SemilocalModelSymbols :=
  core.supportWindow.toSemilocalModelSymbols

def toArchimedeanTraceSymbols (core : SourceAnalyticCore) :
    ArchimedeanTraceSymbols :=
  core.traceScale.toArchimedeanTraceSymbols

def toNormalizedLegalSquareTraceScaleSymbols
    (core : SourceAnalyticCore) :
    CC20Concrete.TraceScale.NormalizedLegalSquareTraceScaleSymbols :=
  core.traceScale.toNormalizedLegalSquareTraceScaleSymbols

end SourceAnalyticCore

end AnalyticCore
end Source
end ConnesWeilRH
