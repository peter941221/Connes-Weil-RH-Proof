import ConnesWeilRH.Dev.OffDiagE00_01.C1RouteAEntryAssembly2663
import ConnesWeilRH.Dev.OffDiagE00_02.C1RouteAEntryAssembly2663
import ConnesWeilRH.Dev.OffDiagE00_04.C1RouteAEntryAssembly2663
import ConnesWeilRH.Dev.OffDiagE01_00.C1RouteAEntryAssembly2663
import ConnesWeilRH.Dev.OffDiagE01_03.C1RouteAEntryAssembly2663
import ConnesWeilRH.Dev.OffDiagE01_04.C1RouteAEntryAssembly2663
import ConnesWeilRH.Dev.OffDiagE02_03.C1RouteAEntryAssembly2663
import ConnesWeilRH.Dev.OffDiagE02_04.C1RouteAEntryAssembly2663
import ConnesWeilRH.Dev.OffDiagE03_02.C1RouteAEntryAssembly2663
import ConnesWeilRH.Dev.OffDiagE03_04.C1RouteAEntryAssembly2663
import ConnesWeilRH.Dev.OffDiagE04_00.C1RouteAEntryAssembly2663
import ConnesWeilRH.Dev.OffDiagE04_01.C1RouteAEntryAssembly2663
import ConnesWeilRH.Dev.OffDiagE04_03.C1RouteAEntryAssembly2663
import ConnesWeilRH.Dev.OffDiagE05_06.C1RouteAEntryAssembly2663
import ConnesWeilRH.Dev.OffDiagE05_07.C1RouteAEntryAssembly2663
import ConnesWeilRH.Dev.OffDiagE06_05.C1RouteAEntryAssembly2663
import ConnesWeilRH.Dev.OffDiagE06_07.C1RouteAEntryAssembly2663
import ConnesWeilRH.Dev.OffDiagE07_05.C1RouteAEntryAssembly2663
import ConnesWeilRH.Dev.OffDiagE07_06.C1RouteAEntryAssembly2663
import ConnesWeilRH.Dev.OffDiagE11_09.C1RouteAEntryAssembly2663
import ConnesWeilRH.Dev.OffDiagE13_03.C1RouteAEntryAssembly2663
import ConnesWeilRH.Dev.OffDiagE14_03.C1RouteAEntryAssembly2663
import ConnesWeilRH.Dev.OffDiagE15_03.C1RouteAEntryAssembly2663
import ConnesWeilRH.Dev.OffDiagE16_03.C1RouteAEntryAssembly2663
import ConnesWeilRH.Dev.OffDiagE17_03.C1RouteAEntryAssembly2663
import ConnesWeilRH.Dev.OffDiagE18_03.C1RouteAEntryAssembly2663
import ConnesWeilRH.Dev.OffDiagE19_02.C1RouteAEntryAssembly2663
import ConnesWeilRH.Dev.OffDiagE19_03.C1RouteAEntryAssembly2663
import ConnesWeilRH.Dev.OffDiagE20_02.C1RouteAEntryAssembly2663
import ConnesWeilRH.Dev.OffDiagE20_03.C1RouteAEntryAssembly2663
import ConnesWeilRH.Dev.OffDiagE21_02.C1RouteAEntryAssembly2663
import ConnesWeilRH.Dev.OffDiagE21_03.C1RouteAEntryAssembly2663
import ConnesWeilRH.Dev.OffDiagE22_02.C1RouteAEntryAssembly2663
import ConnesWeilRH.Dev.OffDiagE22_03.C1RouteAEntryAssembly2663
import ConnesWeilRH.Dev.OffDiagE23_02.C1RouteAEntryAssembly2663
import ConnesWeilRH.Dev.OffDiagE23_03.C1RouteAEntryAssembly2663
import ConnesWeilRH.Dev.OffDiagE24_02.C1RouteAEntryAssembly2663
import ConnesWeilRH.Dev.OffDiagE24_03.C1RouteAEntryAssembly2663
import ConnesWeilRH.Dev.OffDiagE25_02.C1RouteAEntryAssembly2663
import ConnesWeilRH.Dev.OffDiagE25_03.C1RouteAEntryAssembly2663
import ConnesWeilRH.Dev.OffDiagE26_02.C1RouteAEntryAssembly2663
import ConnesWeilRH.Dev.OffDiagE26_03.C1RouteAEntryAssembly2663
import ConnesWeilRH.Dev.OffDiagE27_02.C1RouteAEntryAssembly2663
import ConnesWeilRH.Dev.OffDiagE27_03.C1RouteAEntryAssembly2663
import ConnesWeilRH.Dev.OffDiagE27_07.C1RouteAEntryAssembly2663
import ConnesWeilRH.Dev.OffDiagE28_02.C1RouteAEntryAssembly2663
import ConnesWeilRH.Dev.OffDiagE28_03.C1RouteAEntryAssembly2663
import ConnesWeilRH.Dev.OffDiagE28_07.C1RouteAEntryAssembly2663
import ConnesWeilRH.Dev.OffDiagE29_02.C1RouteAEntryAssembly2663
import ConnesWeilRH.Dev.OffDiagE29_03.C1RouteAEntryAssembly2663
import ConnesWeilRH.Dev.OffDiagE29_07.C1RouteAEntryAssembly2663

namespace ConnesWeilRH.Dev

/-! The 51 manifest entries from record 2664 are imported as proof-producing
assembly modules.  This facade gives the 2695 consumer one quantified
membership theorem without treating the manifest JSON as a proof. -/

def parameterizedOffdiagManifest2664Base (i j : Fin 30) : Prop :=
  (i = 0 ∧ j = 1) ∨
  (i = 0 ∧ j = 4) ∨
  (i = 1 ∧ j = 0) ∨
  (i = 1 ∧ j = 3) ∨
  (i = 1 ∧ j = 4) ∨
  (i = 2 ∧ j = 3) ∨
  (i = 2 ∧ j = 4) ∨
  (i = 3 ∧ j = 2) ∨
  (i = 3 ∧ j = 4) ∨
  (i = 4 ∧ j = 0) ∨
  (i = 4 ∧ j = 1) ∨
  (i = 4 ∧ j = 3) ∨
  (i = 5 ∧ j = 6) ∨
  (i = 5 ∧ j = 7) ∨
  (i = 6 ∧ j = 5) ∨
  (i = 6 ∧ j = 7) ∨
  (i = 7 ∧ j = 5) ∨
  (i = 7 ∧ j = 6) ∨
  (i = 13 ∧ j = 3) ∨
  (i = 14 ∧ j = 3) ∨
  (i = 15 ∧ j = 3) ∨
  (i = 16 ∧ j = 3) ∨
  (i = 17 ∧ j = 3) ∨
  (i = 18 ∧ j = 3) ∨
  (i = 19 ∧ j = 2) ∨
  (i = 19 ∧ j = 3) ∨
  (i = 20 ∧ j = 2) ∨
  (i = 20 ∧ j = 3) ∨
  (i = 21 ∧ j = 2) ∨
  (i = 21 ∧ j = 3) ∨
  (i = 22 ∧ j = 2) ∨
  (i = 22 ∧ j = 3) ∨
  (i = 23 ∧ j = 2) ∨
  (i = 23 ∧ j = 3) ∨
  (i = 24 ∧ j = 2) ∨
  (i = 24 ∧ j = 3) ∨
  (i = 25 ∧ j = 2) ∨
  (i = 25 ∧ j = 3) ∨
  (i = 26 ∧ j = 2) ∨
  (i = 26 ∧ j = 3) ∨
  (i = 27 ∧ j = 2) ∨
  (i = 27 ∧ j = 3) ∨
  (i = 27 ∧ j = 7) ∨
  (i = 28 ∧ j = 2) ∨
  (i = 28 ∧ j = 3) ∨
  (i = 28 ∧ j = 7) ∨
  (i = 29 ∧ j = 2) ∨
  (i = 29 ∧ j = 3) ∨
  (i = 29 ∧ j = 7)

def parameterizedOffdiagManifest2664 (i j : Fin 30) : Prop :=
  parameterizedOffdiagManifest2664Base i j ∨
    (i = 0 ∧ j = 2) ∨ (i = 11 ∧ j = 9)

theorem parameterizedOffdiagManifest2664Base_mem
    (i j : Fin 30) (h : parameterizedOffdiagManifest2664Base i j) :
    (analyticMomentInterval2597 i j).Mem
      (ownerMomentMatrix2351 capturedModulations2584 capturedNodes2584 i j) := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  exacts [
    ConnesWeilRH.Dev.OffDiagE00_01.entry0001Mem2663,
    ConnesWeilRH.Dev.OffDiagE00_04.entry0004Mem2663,
    ConnesWeilRH.Dev.OffDiagE01_00.entry0100Mem2663,
    ConnesWeilRH.Dev.OffDiagE01_03.entry0103Mem2663,
    ConnesWeilRH.Dev.OffDiagE01_04.entry0104Mem2663,
    ConnesWeilRH.Dev.OffDiagE02_03.entry0203Mem2663,
    ConnesWeilRH.Dev.OffDiagE02_04.entry0204Mem2663,
    ConnesWeilRH.Dev.OffDiagE03_02.entry0302Mem2663,
    ConnesWeilRH.Dev.OffDiagE03_04.entry0304Mem2663,
    ConnesWeilRH.Dev.OffDiagE04_00.entry0400Mem2663,
    ConnesWeilRH.Dev.OffDiagE04_01.entry0401Mem2663,
    ConnesWeilRH.Dev.OffDiagE04_03.entry0403Mem2663,
    ConnesWeilRH.Dev.OffDiagE05_06.entry0506Mem2663,
    ConnesWeilRH.Dev.OffDiagE05_07.entry0507Mem2663,
    ConnesWeilRH.Dev.OffDiagE06_05.entry0605Mem2663,
    ConnesWeilRH.Dev.OffDiagE06_07.entry0607Mem2663,
    ConnesWeilRH.Dev.OffDiagE07_05.entry0705Mem2663,
    ConnesWeilRH.Dev.OffDiagE07_06.entry0706Mem2663,
    ConnesWeilRH.Dev.OffDiagE13_03.entry1303Mem2663,
    ConnesWeilRH.Dev.OffDiagE14_03.entry1403Mem2663,
    ConnesWeilRH.Dev.OffDiagE15_03.entry1503Mem2663,
    ConnesWeilRH.Dev.OffDiagE16_03.entry1603Mem2663,
    ConnesWeilRH.Dev.OffDiagE17_03.entry1703Mem2663,
    ConnesWeilRH.Dev.OffDiagE18_03.entry1803Mem2663,
    ConnesWeilRH.Dev.OffDiagE19_02.entry1902Mem2663,
    ConnesWeilRH.Dev.OffDiagE19_03.entry1903Mem2663,
    ConnesWeilRH.Dev.OffDiagE20_02.entry2002Mem2663,
    ConnesWeilRH.Dev.OffDiagE20_03.entry2003Mem2663,
    ConnesWeilRH.Dev.OffDiagE21_02.entry2102Mem2663,
    ConnesWeilRH.Dev.OffDiagE21_03.entry2103Mem2663,
    ConnesWeilRH.Dev.OffDiagE22_02.entry2202Mem2663,
    ConnesWeilRH.Dev.OffDiagE22_03.entry2203Mem2663,
    ConnesWeilRH.Dev.OffDiagE23_02.entry2302Mem2663,
    ConnesWeilRH.Dev.OffDiagE23_03.entry2303Mem2663,
    ConnesWeilRH.Dev.OffDiagE24_02.entry2402Mem2663,
    ConnesWeilRH.Dev.OffDiagE24_03.entry2403Mem2663,
    ConnesWeilRH.Dev.OffDiagE25_02.entry2502Mem2663,
    ConnesWeilRH.Dev.OffDiagE25_03.entry2503Mem2663,
    ConnesWeilRH.Dev.OffDiagE26_02.entry2602Mem2663,
    ConnesWeilRH.Dev.OffDiagE26_03.entry2603Mem2663,
    ConnesWeilRH.Dev.OffDiagE27_02.entry2702Mem2663,
    ConnesWeilRH.Dev.OffDiagE27_03.entry2703Mem2663,
    ConnesWeilRH.Dev.OffDiagE27_07.entry2707Mem2663,
    ConnesWeilRH.Dev.OffDiagE28_02.entry2802Mem2663,
    ConnesWeilRH.Dev.OffDiagE28_03.entry2803Mem2663,
    ConnesWeilRH.Dev.OffDiagE28_07.entry2807Mem2663,
    ConnesWeilRH.Dev.OffDiagE29_02.entry2902Mem2663,
    ConnesWeilRH.Dev.OffDiagE29_03.entry2903Mem2663,
    ConnesWeilRH.Dev.OffDiagE29_07.entry2907Mem2663]

#print axioms parameterizedOffdiagManifest2664Base_mem

theorem parameterizedOffdiagManifest2664_mem
    (i j : Fin 30) (h : parameterizedOffdiagManifest2664 i j) :
    (analyticMomentInterval2597 i j).Mem
      (ownerMomentMatrix2351 capturedModulations2584 capturedNodes2584 i j) := by
  rcases h with hbase | h02 | h119
  · exact parameterizedOffdiagManifest2664Base_mem i j hbase
  · rcases h02 with ⟨rfl, rfl⟩
    exact ConnesWeilRH.Dev.OffDiagE00_02.entry0002Mem2663
  · rcases h119 with ⟨rfl, rfl⟩
    exact ConnesWeilRH.Dev.OffDiagE11_09.entry1109Mem2663

#print axioms parameterizedOffdiagManifest2664_mem

end ConnesWeilRH.Dev
