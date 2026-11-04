import ConnesWeilRH.Dev.C1RouteARationalComplexEndpointBounds3328
import ConnesWeilRH.Dev.C1RouteARationalSignedCoordinateBound3342

namespace ConnesWeilRH.Dev

set_option maxHeartbeats 10000000 in

theorem ratRectImagEndpointAbsBound3342_le_endpointAbsBound3371
    (a : RatRect3276) :
    ratRectImagEndpointAbsBound3342 a ≤ ratRectEndpointAbsBound3326 a := by
  change max |a.imLo| |a.imHi| ≤ max (max |a.reLo| |a.reHi|) (max |a.imLo| |a.imHi|)
  exact le_max_right _ _

set_option maxHeartbeats 10000000 in
theorem ratRectRealEndpointAbsBound3342_le_endpointAbsBound3371
    (a : RatRect3276) :
    ratRectRealEndpointAbsBound3342 a ≤ ratRectEndpointAbsBound3326 a := by
  change max |a.reLo| |a.reHi| ≤ max (max |a.reLo| |a.reHi|) (max |a.imLo| |a.imHi|)
  exact le_max_left _ _

set_option maxHeartbeats 10000000 in
theorem ratRect_add_imagEndpointAbsBound3342_le_sum3371
    (a b : RatRect3276) :
    ratRectImagEndpointAbsBound3342 (RatRect3276.add a b) ≤
      ratRectEndpointAbsBound3326 a + ratRectEndpointAbsBound3326 b := by
  exact le_trans
    (ratRectImagEndpointAbsBound3342_le_endpointAbsBound3371
      (RatRect3276.add a b))
    (ratRect_add_endpointAbsBound_le_sum3328 a b)

end ConnesWeilRH.Dev
