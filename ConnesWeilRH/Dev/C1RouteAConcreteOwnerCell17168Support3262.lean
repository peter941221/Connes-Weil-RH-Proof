import ConnesWeilRH.Dev.C1RouteAConcreteOwnerCell17168Rect3245

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

theorem record2680_cell17168_center_inside_support3262
    (family : Fin 30) :
    |record2680Center3212 17168| < storedWidth family ^ 2 := by
  fin_cases family <;>
    norm_num [record2680Center3212, record2680Grid3212,
      diagnosticRadius3201, storedWidth, Matrix.cons_val_zero,
      Matrix.cons_val_four, Fin.ext_iff]

theorem record2680_cell17168_family8_bump_pos3262 :
    0 < widthBump (storedWidth 8 ^ 2) (record2680Center3212 17168) := by
  rw [widthBump]
  rw [if_pos (record2680_cell17168_center_inside_support3262 8)]
  exact Real.exp_pos _

end ConnesWeilRH.Dev
