import ConnesWeilRH.Dev.C1RouteAIntervalAlgebra
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic

namespace ConnesWeilRH.Dev

def binary64FractionBits2674 (bits : Nat) : Nat := bits % 2 ^ 52

def binary64ExponentBits2674 (bits : Nat) : Nat :=
  (bits / 2 ^ 52) % 2 ^ 11

def binary64Significand2674 (bits : Nat) : Nat :=
  if binary64ExponentBits2674 bits = 0 then
    binary64FractionBits2674 bits
  else
    2 ^ 52 + binary64FractionBits2674 bits

def binary64Sign2674 (bits : Nat) : Int :=
  if bits / 2 ^ 63 = 1 then -1 else 1

def binary64Value2674 (bits : Nat) : ℚ :=
  let exponent := binary64ExponentBits2674 bits
  let significand := binary64Significand2674 bits
  let sign : ℚ := (binary64Sign2674 bits : ℚ)
  if exponent = 0 then
    sign * (significand : ℚ) / (2 : ℚ) ^ 1074
  else if exponent ≤ 1075 then
    sign * (significand : ℚ) / (2 : ℚ) ^ (1075 - exponent)
  else
    sign * (significand : ℚ) * (2 : ℚ) ^ (exponent - 1075)

structure Binary64UpperCertificate2674 where
  bits : Nat
  exactValue : ℚ
  bits_lt : bits < 2 ^ 64
  finite : binary64ExponentBits2674 bits < 2047
  encloses : exactValue ≤ binary64Value2674 bits

theorem Binary64UpperCertificate2674.sound
    (certificate : Binary64UpperCertificate2674) :
    certificate.exactValue ≤ binary64Value2674 certificate.bits :=
  certificate.encloses

structure Binary64LowerCertificate2674 where
  bits : Nat
  exactValue : ℚ
  bits_lt : bits < 2 ^ 64
  finite : binary64ExponentBits2674 bits < 2047
  encloses : binary64Value2674 bits ≤ exactValue

theorem Binary64LowerCertificate2674.sound
    (certificate : Binary64LowerCertificate2674) :
    binary64Value2674 certificate.bits ≤ certificate.exactValue :=
  certificate.encloses

def binary64Interval2674 (lowerBits upperBits : Nat) : RealInterval2429 :=
  { lo := binary64Value2674 lowerBits
    hi := binary64Value2674 upperBits }

theorem mem_binary64Interval2674
    (lower : Binary64LowerCertificate2674)
    (upper : Binary64UpperCertificate2674)
    {x : ℚ} (hlower : lower.exactValue ≤ x)
    (hupper : x ≤ upper.exactValue) :
    (binary64Interval2674 lower.bits upper.bits).Mem (x : ℝ) := by
  constructor
  · exact Rat.cast_le.mpr (le_trans lower.encloses hlower)
  · exact Rat.cast_le.mpr (le_trans hupper upper.encloses)

end ConnesWeilRH.Dev
