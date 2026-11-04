import ConnesWeilRH.Dev.C1RouteARationalRealScalingEndpoint3358

namespace ConnesWeilRH.Dev

theorem ratRect_mul_real_comm3360
    (a : RatRect3276) (b : RatInterval3276) :
    RatRect3276.mul (ratRealRect3281 b) a =
      RatRect3276.mul a (ratRealRect3281 b) := by
  cases a with
  | mk reLo reHi imLo imHi =>
    cases b with
    | mk lo hi =>
      simp [RatRect3276.mul, RatInterval3276.mul,
        RatInterval3276.sub, RatInterval3276.add,
        ratRealRect3281, mul_comm, max_comm, max_left_comm,
        max_assoc, min_comm, min_left_comm, min_assoc]

end ConnesWeilRH.Dev
