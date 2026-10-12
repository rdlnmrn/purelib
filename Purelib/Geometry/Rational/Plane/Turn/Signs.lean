module

import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Data.Rat.Sign.Typed
import Purelib.Data.Rat.Sign.Typed.Compatibility
import Purelib.Data.Sign.Basic
public import Purelib.Data.Sign.Pair.Turn
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

/-!
# Rational coordinate certificates for formal small turns

Nonzero endpoint coordinates and a positive dot product determine the same
finite quadrant transition and its retained cross-product orientation.
-/

namespace Purelib.Geometry.Rational.Plane.Turn.Signs

open Purelib.Data.Rat
open Purelib.Data.Rat.Sign
open _root_.Purelib.Data renaming Sign -> FiniteSign
open Purelib.Data.Sign.Pair.Turn

/-- Positive endpoint dot product certifies the corresponding formal small turn.

All four rational endpoint coordinates are nonzero. The dot-product inequality
excludes two negative coordinate products, and the exact cross-product sign
identifies the orientation of whichever coordinate changes sign. -/
public theorem smallTurnCompatible_of_dot_pos
    {Aₗ Bₗ Aᵣ Bᵣ : Fraction.Rational}
    (AₗNonzero : Aₗ ≠ 0) (BₗNonzero : Bₗ ≠ 0)
    (AᵣNonzero : Aᵣ ≠ 0) (BᵣNonzero : Bᵣ ≠ 0)
    (dotPositive : 0 < Aₗ * Aᵣ + Bₗ * Bᵣ) :
    Data.Sign.Pair.Turn.SmallTurnCompatible
      (FiniteSign.ofCoordinate Aₗ) (FiniteSign.ofCoordinate Bₗ)
      (FiniteSign.ofCoordinate Aᵣ) (FiniteSign.ofCoordinate Bᵣ)
      (FiniteSign.ofCoordinate (Aₗ * Bᵣ - Bₗ * Aᵣ)) := by
  let cross := Aₗ * Bᵣ - Bₗ * Aᵣ
  have AProductNonzero : Aₗ * Aᵣ ≠ 0 :=
    Fraction.Field.mul_ne_zero_direct AₗNonzero AᵣNonzero
  have BProductNonzero : Bₗ * Bᵣ ≠ 0 :=
    Fraction.Field.mul_ne_zero_direct BₗNonzero BᵣNonzero
  have AₗSign : FiniteSign.ofCoordinate Aₗ ≠ .zero := by
    exact FiniteSign.ofCoordinate_ne_zero_iff.mpr AₗNonzero
  have BₗSign : FiniteSign.ofCoordinate Bₗ ≠ .zero := by
    exact FiniteSign.ofCoordinate_ne_zero_iff.mpr BₗNonzero
  have AᵣSign : FiniteSign.ofCoordinate Aᵣ ≠ .zero := by
    exact FiniteSign.ofCoordinate_ne_zero_iff.mpr AᵣNonzero
  have BᵣSign : FiniteSign.ofCoordinate Bᵣ ≠ .zero := by
    exact FiniteSign.ofCoordinate_ne_zero_iff.mpr BᵣNonzero
  refine ⟨AₗSign, BₗSign, AᵣSign, BᵣSign, ?_⟩
  rcases lt_trichotomy (Aₗ * Aᵣ) 0 with
      AProductNegative | AProductZero | AProductPositive
  · rcases lt_trichotomy (Bₗ * Bᵣ) 0 with
        BProductNegative | BProductZero | BProductPositive
    · exact ((not_lt_of_ge
        (add_nonpos AProductNegative.le BProductNegative.le))
          dotPositive).elim
    · exact (BProductNonzero BProductZero).elim
    · have ASignsDiffer := Typed.Compatibility.Turn.ofCoordinate_ne_of_mul_neg AProductNegative
      have BSignsEqual := Typed.Compatibility.Turn.ofCoordinate_eq_of_mul_pos BProductPositive
      have firstPositive :
          0 < Aₗ ^ 2 * (Bₗ * Bᵣ) :=
        Fraction.Order.Arithmetic.mul_pos_direct
          (Fraction.Order.Arithmetic.exact_rational_sq_pos AₗNonzero) BProductPositive
      have secondNegative :
          Bₗ ^ 2 * (Aₗ * Aᵣ) < 0 :=
        Fraction.Order.Arithmetic.mul_neg_of_pos_of_neg_direct
          (Fraction.Order.Arithmetic.exact_rational_sq_pos BₗNonzero) AProductNegative
      have crossProductPositive : 0 < cross * (Aₗ * Bₗ) := by
        calc
          0 < Aₗ ^ 2 * (Bₗ * Bᵣ) -
              Bₗ ^ 2 * (Aₗ * Aᵣ) :=
            Fraction.Order.Arithmetic.sub_pos_direct
              (secondNegative.trans firstPositive)
          _ = cross * (Aₗ * Bₗ) := by
            dsimp only [cross]
            ring1
      have turn : FiniteSign.ofCoordinate cross =
          FiniteSign.mul (FiniteSign.ofCoordinate Aₗ)
            (FiniteSign.ofCoordinate Bₗ) := by
        simpa only [FiniteSign.ofCoordinate_mul] using
          Typed.Compatibility.Turn.ofCoordinate_eq_of_mul_pos crossProductPositive
      rw [if_neg ASignsDiffer]
      exact ⟨BSignsEqual, by simpa only [cross] using turn⟩
  · exact (AProductNonzero AProductZero).elim
  · rcases lt_trichotomy (Bₗ * Bᵣ) 0 with
        BProductNegative | BProductZero | BProductPositive
    · have ASignsEqual := Typed.Compatibility.Turn.ofCoordinate_eq_of_mul_pos AProductPositive
      have BSignsDiffer := Typed.Compatibility.Turn.ofCoordinate_ne_of_mul_neg BProductNegative
      have firstNegative :
          Aₗ ^ 2 * (Bₗ * Bᵣ) < 0 :=
        Fraction.Order.Arithmetic.mul_neg_of_pos_of_neg_direct
          (Fraction.Order.Arithmetic.exact_rational_sq_pos AₗNonzero) BProductNegative
      have secondPositive :
          0 < Bₗ ^ 2 * (Aₗ * Aᵣ) :=
        Fraction.Order.Arithmetic.mul_pos_direct
          (Fraction.Order.Arithmetic.exact_rational_sq_pos BₗNonzero) AProductPositive
      have crossProductPositive : 0 < cross * (-(Aₗ * Bₗ)) := by
        calc
          0 < Bₗ ^ 2 * (Aₗ * Aᵣ) -
              Aₗ ^ 2 * (Bₗ * Bᵣ) :=
            Fraction.Order.Arithmetic.sub_pos_direct
              (firstNegative.trans secondPositive)
          _ = cross * (-(Aₗ * Bₗ)) := by
            dsimp only [cross]
            ring1
      have turn : FiniteSign.ofCoordinate cross =
          FiniteSign.neg (FiniteSign.mul
            (FiniteSign.ofCoordinate Aₗ)
            (FiniteSign.ofCoordinate Bₗ)) := by
        simpa only [FiniteSign.ofCoordinate_neg,
          FiniteSign.ofCoordinate_mul] using
          Typed.Compatibility.Turn.ofCoordinate_eq_of_mul_pos crossProductPositive
      rw [if_pos ASignsEqual, if_neg BSignsDiffer]
      simpa only [cross] using turn
    · exact (BProductNonzero BProductZero).elim
    · have ASignsEqual := Typed.Compatibility.Turn.ofCoordinate_eq_of_mul_pos AProductPositive
      have BSignsEqual := Typed.Compatibility.Turn.ofCoordinate_eq_of_mul_pos BProductPositive
      rw [if_pos ASignsEqual, if_pos BSignsEqual]
      trivial

end Purelib.Geometry.Rational.Plane.Turn.Signs
