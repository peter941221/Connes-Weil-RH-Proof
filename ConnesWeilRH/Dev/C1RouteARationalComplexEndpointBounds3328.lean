import ConnesWeilRH.Dev.C1RouteARationalComplexEndpointBounds3326

namespace ConnesWeilRH.Dev

set_option maxHeartbeats 10000000 in
theorem ratRect_add_endpointAbsBound_le_sum3328
    (a b : RatRect3276) :
    ratRectEndpointAbsBound3326 (RatRect3276.add a b) ≤
      ratRectEndpointAbsBound3326 a + ratRectEndpointAbsBound3326 b := by
  unfold ratRectEndpointAbsBound3326 RatRect3276.add
  apply max_le
  · apply max_le
    · exact abs_add_le _ _ |>.trans (add_le_add
        (le_trans (le_max_left _ _) (le_max_left _ _))
        (le_trans (le_max_left _ _) (le_max_left _ _)))
    · exact abs_add_le _ _ |>.trans (add_le_add
        (le_trans (le_max_right _ _) (le_max_left _ _))
        (le_trans (le_max_right _ _) (le_max_left _ _)))
  · apply max_le
    · exact abs_add_le _ _ |>.trans (add_le_add
        (le_trans (le_max_left _ _) (le_max_right _ _))
        (le_trans (le_max_left _ _) (le_max_right _ _)))
    · exact abs_add_le _ _ |>.trans (add_le_add
        (le_trans (le_max_right _ _) (le_max_right _ _))
        (le_trans (le_max_right _ _) (le_max_right _ _)))

end ConnesWeilRH.Dev
