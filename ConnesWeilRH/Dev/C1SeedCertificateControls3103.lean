import ConnesWeilRH.Dev.C1SeedCertificatePilot3101

namespace ConnesWeilRH.Dev.C1SeedCertificate3101

open C1SeedCertificate3098

theorem reject_underpriced_four3103 :
    checkCell 1249 { cell1249 with price4 := 0 } = false := by decide +kernel

theorem reject_underpriced_seven3103 :
    checkCell 1249 { cell1249 with price7 := 0 } = false := by decide +kernel

theorem reject_false_initial_exp3103 :
    checkCell 1249 { cell1249 with powers := cell1249.powers.set 0 (Box.point 0) } = false := by
  decide +kernel

theorem reject_outside_partition3103 :
    checkCell 8192 cell8191 = false := by decide +kernel

end ConnesWeilRH.Dev.C1SeedCertificate3101
