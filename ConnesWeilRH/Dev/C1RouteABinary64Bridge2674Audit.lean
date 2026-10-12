import ConnesWeilRH.Dev.C1RouteABinary64Bridge2674
import Mathlib.Tactic.NormNum

namespace ConnesWeilRH.Dev

#print axioms Binary64UpperCertificate2674.sound
#print axioms Binary64LowerCertificate2674.sound
#print axioms mem_binary64Interval2674

example : binary64Value2674 0x3ff0000000000000 = 1 := by
  norm_num [binary64Value2674, binary64ExponentBits2674,
    binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

example : binary64Value2674 0xbfe0000000000000 = -(1 / 2 : ℚ) := by
  norm_num [binary64Value2674, binary64ExponentBits2674,
    binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

example : binary64Value2674 0x0000000000000001 = 1 / (2 : ℚ) ^ 1074 := by
  norm_num [binary64Value2674, binary64ExponentBits2674,
    binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

def upperSample2674 : Binary64UpperCertificate2674 :=
  { bits := 0x3ff0000000000001
    exactValue := 1 + 1 / (2 : ℚ) ^ 200
    bits_lt := by norm_num
    finite := by norm_num [binary64ExponentBits2674]
    encloses := by
      norm_num [binary64Value2674, binary64ExponentBits2674,
        binary64Significand2674, binary64FractionBits2674,
        binary64Sign2674] }

example : upperSample2674.exactValue ≤
    binary64Value2674 upperSample2674.bits := by
  exact upperSample2674.sound

def lowerSample2674 : Binary64LowerCertificate2674 :=
  { bits := 0x3ff0000000000000
    exactValue := 1 + 1 / (2 : ℚ) ^ 200
    bits_lt := by norm_num
    finite := by norm_num [binary64ExponentBits2674]
    encloses := by
      norm_num [binary64Value2674, binary64ExponentBits2674,
        binary64Significand2674, binary64FractionBits2674,
        binary64Sign2674] }

example : binary64Value2674 lowerSample2674.bits ≤
    lowerSample2674.exactValue := by
  exact lowerSample2674.sound

example :
    (binary64Interval2674 lowerSample2674.bits upperSample2674.bits).Mem
      ((1 + 1 / (2 : ℚ) ^ 200 : ℚ) : ℝ) := by
  apply mem_binary64Interval2674 lowerSample2674 upperSample2674 <;>
    norm_num [lowerSample2674, upperSample2674]

end ConnesWeilRH.Dev
