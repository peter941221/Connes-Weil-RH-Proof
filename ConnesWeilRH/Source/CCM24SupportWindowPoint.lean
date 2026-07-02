/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Source.AnalyticCoreBase

/-!
# CCM24 support-window point core

This module owns the lowest currently exposed point-membership normal form for
the CCM24 support-window lane.  Keeping it outside `AnalyticCore` lets later
containment data import the common support-window carrier without creating an
import cycle.
-/

namespace ConnesWeilRH
namespace Source
namespace AnalyticCore

namespace SourceSupportWindowData

structure SourceSupportWindowPointContainmentCoreData
    {A : SourceTestAlgebra} (S : SourceSupportWindowData A)
    (f : A.Test) (I : S.Window)
    (supportWindowSet : Type)
    (supportWindowMembership : supportWindowSet → Prop) where
  supportWindowPoint : supportWindowSet
  supportWindowPoint_mem :
    supportWindowMembership supportWindowPoint
  supportWindowContainment :
    SourceSupportWindowContainmentData
      S f I supportWindowSet supportWindowMembership

namespace SourceSupportWindowPointContainmentCoreData

theorem supportWindowPointMembershipWitnessesSupportInWindow
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} {I : S.Window}
    {supportWindowSet : Type}
    {supportWindowMembership : supportWindowSet → Prop}
    (D :
      SourceSupportWindowPointContainmentCoreData
        S f I supportWindowSet supportWindowMembership) :
    supportWindowMembership D.supportWindowPoint →
      S.supportInWindow f I := by
  intro hWindow
  exact
    D.supportWindowContainment.supportSetContainedInWindow
      D.supportWindowPoint hWindow

end SourceSupportWindowPointContainmentCoreData

structure SourceSupportWindowSupportWindowPointMembershipCoreData
    {A : SourceTestAlgebra} (S : SourceSupportWindowData A)
    (f : A.Test) (I : S.Window)
    (supportWindowSet : Type)
    (supportWindowMembership : supportWindowSet → Prop) where
  supportWindowPointContainmentCore :
    SourceSupportWindowPointContainmentCoreData
      S f I supportWindowSet supportWindowMembership

namespace SourceSupportWindowSupportWindowPointMembershipCoreData

theorem supportWindowPointRealizesSupportInWindow
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} {I : S.Window}
    {supportWindowSet : Type}
    {supportWindowMembership : supportWindowSet → Prop}
    (D :
      SourceSupportWindowSupportWindowPointMembershipCoreData
        S f I supportWindowSet supportWindowMembership) :
    S.supportInWindow f I :=
  D.supportWindowPointContainmentCore
    |>.supportWindowPointMembershipWitnessesSupportInWindow
      D.supportWindowPointContainmentCore.supportWindowPoint_mem

end SourceSupportWindowSupportWindowPointMembershipCoreData

end SourceSupportWindowData

end AnalyticCore
end Source
end ConnesWeilRH
