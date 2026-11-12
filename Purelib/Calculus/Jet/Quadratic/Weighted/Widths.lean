module

public import Purelib.Calculus.Jet.Quadratic.Weighted
import Purelib.Data.Gaussian.Norm.Weighted
public import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Tactic.Ring

/-! # Taylor summation with retained nonnegative widths

The pointwise factors are paid by squared original widths. Weighted finite
Cauchy bounds the SAME ordered remainder sum by the square of their total
width, including zero widths. No finite entry count multiplies the factor.
-/

public section

namespace Purelib.Calculus.Jet.Quadratic.Basic.Certificate

open Purelib.Algebra
open Purelib.Data
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat

variable {count : Nat} {increment : Canonical}

/-- Summing the original entries preserves their exact first-order expansions at the identical increment. -/
theorem sum_expansion (entries : Fin count → Certificate increment) :
    FiniteSum.Fin.sumFin (fun index => (entries index).output) -
        FiniteSum.Fin.sumFin (fun index => (entries index).base) -
        increment * FiniteSum.Fin.sumFin (fun index => (entries index).slope) =
      FiniteSum.Fin.sumFin (fun index => (entries index).remainder) := by
  calc
    _ = FiniteSum.Fin.sumFin (fun index =>
        (entries index).output - (entries index).base - increment * (entries index).slope) := by
      rewrite [FiniteSum.Fin.sumFin_sub, FiniteSum.Fin.sumFin_sub, FiniteSum.Fin.sumFin_mul_left]
      rfl
    _ = _ := FiniteSum.Fin.sumFin_congr (fun index => (entries index).expansion)

/-- The same finite remainder sum is bounded by one density and the square of its retained total width.

Each nonnegative width pays the corresponding original certificate factor
by its square. The existing weighted quadrance estimate also handles zero
widths, without removing occurrences or dividing by a width.
-/
theorem width_remainder_le (entries : Fin count → Certificate increment)
    (widths : Fin count → Fraction.Rational) (density : Fraction.Rational)
    (nonnegative : ∀ index, 0 ≤ widths index)
    (factor_le : ∀ index, (entries index).factor ≤ density * (widths index) ^ 2) :
    Norm.Basic.normSq (FiniteSum.Fin.sumFin (fun index => (entries index).remainder)) ≤
      (density * (FiniteSum.Fin.sumFin widths) ^ 2) * Norm.Basic.normSq increment ^ 2 := by
  have bounded (index : Fin count) :
      Norm.Basic.normSq (entries index).remainder ≤
        (density * Norm.Basic.normSq increment ^ 2) * (widths index) ^ 2 := by
    have original := (entries index).remainder_le
    rewrite [← Norm.Basic.normSq_eq_canonical, ← Norm.Basic.normSq_eq_canonical] at original
    exact (original.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      (factor_le index) (Fraction.Order.Arithmetic.sq_nonneg_direct (Norm.Basic.normSq increment)))).trans_eq
      (by ring1)
  exact (Norm.Weighted.normSq_sumFin_weighted
    (fun index => (entries index).remainder) widths nonnegative bounded).trans_eq (by ring1)

/-- Construct the exact original finite Taylor sum using its squared-width density.

The base, output, slope and remainder retain their original ordered finite
sums. The internally proved factor is independent of the number of entries
when the original widths sum to one.
-/
@[expose] def sumWithWidths (entries : Fin count → Certificate increment)
    (widths : Fin count → Fraction.Rational) (density : Fraction.Rational)
    (density_nonnegative : 0 ≤ density) (nonnegative : ∀ index, 0 ≤ widths index)
    (factor_le : ∀ index, (entries index).factor ≤ density * (widths index) ^ 2) : Certificate increment where
  base := FiniteSum.Fin.sumFin (fun index => (entries index).base)
  output := FiniteSum.Fin.sumFin (fun index => (entries index).output)
  slope := FiniteSum.Fin.sumFin (fun index => (entries index).slope)
  remainder := FiniteSum.Fin.sumFin (fun index => (entries index).remainder)
  expansion := sum_expansion entries
  factor := density * (FiniteSum.Fin.sumFin widths) ^ 2
  factor_nonneg := Fraction.Order.Arithmetic.mul_nonneg_direct density_nonnegative
    (Fraction.Order.Arithmetic.sq_nonneg_direct _)
  remainder_le := by
    rewrite [← Norm.Basic.normSq_eq_canonical, ← Norm.Basic.normSq_eq_canonical]
    exact width_remainder_le entries widths density nonnegative factor_le

/-- The width-paid sum retains the same original finite base samples. -/
theorem sumWithWidths_base (entries : Fin count → Certificate increment)
    (widths : Fin count → Fraction.Rational) (density : Fraction.Rational)
    (density_nonnegative : 0 ≤ density) (nonnegative : ∀ index, 0 ≤ widths index)
    (factor_le : ∀ index, (entries index).factor ≤ density * (widths index) ^ 2) :
    (sumWithWidths entries widths density density_nonnegative nonnegative factor_le).base =
      FiniteSum.Fin.sumFin (fun index => (entries index).base) := rfl

/-- The width-paid output retains the same original finite output samples. -/
theorem sumWithWidths_output (entries : Fin count → Certificate increment)
    (widths : Fin count → Fraction.Rational) (density : Fraction.Rational)
    (density_nonnegative : 0 ≤ density) (nonnegative : ∀ index, 0 ≤ widths index)
    (factor_le : ∀ index, (entries index).factor ≤ density * (widths index) ^ 2) :
    (sumWithWidths entries widths density density_nonnegative nonnegative factor_le).output =
      FiniteSum.Fin.sumFin (fun index => (entries index).output) := rfl

/-- The width-paid slope retains the same original finite derivative samples. -/
theorem sumWithWidths_slope (entries : Fin count → Certificate increment)
    (widths : Fin count → Fraction.Rational) (density : Fraction.Rational)
    (density_nonnegative : 0 ≤ density) (nonnegative : ∀ index, 0 ≤ widths index)
    (factor_le : ∀ index, (entries index).factor ≤ density * (widths index) ^ 2) :
    (sumWithWidths entries widths density density_nonnegative nonnegative factor_le).slope =
      FiniteSum.Fin.sumFin (fun index => (entries index).slope) := rfl

/-- Its factor is exactly the density times the square of the original total width. -/
theorem sumWithWidths_factor (entries : Fin count → Certificate increment)
    (widths : Fin count → Fraction.Rational) (density : Fraction.Rational)
    (density_nonnegative : 0 ≤ density) (nonnegative : ∀ index, 0 ≤ widths index)
    (factor_le : ∀ index, (entries index).factor ≤ density * (widths index) ^ 2) :
    (sumWithWidths entries widths density density_nonnegative nonnegative factor_le).factor =
      density * (FiniteSum.Fin.sumFin widths) ^ 2 := rfl

end Purelib.Calculus.Jet.Quadratic.Basic.Certificate

end
