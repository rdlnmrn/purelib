module

public import Init.Data.Int.Basic
import Purelib.Data.Int.Arithmetic

namespace Purelib.Data.Int.Divisibility

/-- An integer divisibility witness gives divisibility of the absolute values.

The absolute value of its displayed integer multiplier is the retained
natural multiplier for the two magnitudes. -/
public theorem natAbs_dvd_natAbs_of_dvd {left right : Int}
    (dvd : left ∣ right) : left.natAbs ∣ right.natAbs := by
  rcases dvd with ⟨factor, rfl⟩
  refine ⟨factor.natAbs, ?_⟩
  exact Arithmetic.natAbs_mul left factor

/-- A common integer divisor divides the sum of the displayed multiples. -/
public theorem add {divisor first second : Int} (left : divisor ∣ first)
    (right : divisor ∣ second) : divisor ∣ first + second := by
  obtain ⟨leftFactor, leftEquation⟩ := left
  obtain ⟨rightFactor, rightEquation⟩ := right
  refine ⟨leftFactor + rightFactor, ?_⟩
  rw [leftEquation, rightEquation, Arithmetic.mul_add]

/-- A retained integer divisor divides a left scalar multiple. -/
public theorem mul_left {divisor value : Int} (retained : divisor ∣ value)
    (factor : Int) : divisor ∣ factor * value := by
  obtain ⟨retainedFactor, retainedEquation⟩ := retained
  refine ⟨factor * retainedFactor, ?_⟩
  rw [retainedEquation, ← Arithmetic.mul_assoc,
    Arithmetic.mul_comm factor divisor, Arithmetic.mul_assoc]

/-- Casting a displayed natural divisibility witness gives an integer witness. -/
public theorem of_nat {divisor value : Nat} (retained : divisor ∣ value) :
    (divisor : Int) ∣ (value : Int) := by
  obtain ⟨factor, equation⟩ := retained
  exact ⟨(factor : Int), congrArg Int.ofNat equation⟩

/-- Divisibility of an integer's magnitude gives divisibility of the integer.

The natural divisor is cast to an integer. The retained natural multiplier
keeps its magnitude and receives the sign of the divided integer. -/
public theorem of_natAbs {divisor : Nat} {value : Int}
    (retained : divisor ∣ value.natAbs) : (divisor : Int) ∣ value := by
  cases value with
  | ofNat value => exact of_nat retained
  | negSucc value =>
      obtain ⟨factor, equation⟩ := retained
      refine ⟨-(factor : Int), ?_⟩
      change Int.negOfNat (value + 1) = Int.ofNat divisor * Int.negOfNat factor
      rw [Int.ofNat_eq_natCast divisor, Int.ofNat_mul_negOfNat]
      exact congrArg Int.negOfNat equation

/-- Integer divisibility between natural casts gives natural divisibility.

The displayed integer factor is either natural or a negative successor.
A negative factor with a positive natural divisor cannot produce a natural
cast; the zero-divisor case has an explicit zero factor. -/
public theorem to_nat {divisor value : Nat}
    (retained : (divisor : Int) ∣ (value : Int)) : divisor ∣ value := by
  obtain ⟨factor, equation⟩ := retained
  cases factor with
  | ofNat factor => exact ⟨factor, Int.ofNat.inj equation⟩
  | negSucc factor =>
      cases divisor with
      | zero =>
          have vanishes : value = 0 :=
            Int.ofNat.inj (equation.trans (Arithmetic.zero_mul _))
          exact ⟨0, vanishes⟩
      | succ divisor =>
          change Int.ofNat value = Int.negOfNat ((divisor + 1) * (factor + 1)) at equation
          rw [Nat.mul_succ, Nat.add_succ] at equation
          cases equation

end Purelib.Data.Int.Divisibility
