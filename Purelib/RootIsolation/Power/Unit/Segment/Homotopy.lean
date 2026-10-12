module
import Purelib.Data.Nat.Subtraction

import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
public import Purelib.Data.Gaussian.Norm.Nonzero
import Purelib.Data.Gaussian.Power
import Purelib.Data.Nat.Positive
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Interval.Basic

import Purelib.Geometry.Rational.Affine
import Purelib.Geometry.Rational.Affine.Segment
import Purelib.Polynomial.Clearance.Pair.Basic
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Monomial.Coordinate
import Purelib.Polynomial.Dense.Gaussian.Path.Components
import Purelib.Polynomial.Dense.Gaussian.Power.Coordinate
import Purelib.Polynomial.Dense.Rational.CauchyIndex.Comparison.Dominance
public import Purelib.Polynomial.Winding.Polygon.Comparison
import Purelib.RootIsolation.Power.Unit.Box
public import Purelib.RootIsolation.Power.Unit.Move.Budget
import Purelib.RootIsolation.Power.Unit.Segment.Bounds
import Purelib.RootIsolation.Power.Unit.Segment.Power
import Purelib.RootIsolation.Power.Unit.Segment.Residual
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Tactic.Ring

open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Nat.Positive (RootDegree)
open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.Polynomial.Winding.Polygon.Comparison (SegmentHomotopyFormula)

open Purelib.Data.Gaussian.Norm.Basic (normSq)

open Purelib.Data

open Purelib

open Purelib.Data.Rat

open Purelib.Polynomial

open Purelib.RootIsolation

section
public section

/-!
# Finite monodromy for `Z^d - w`

This file specializes finite owner monodromy to the displayed power family.
The first layer records the exact off-zero Bézout identity.  It is uniform in
the displayed positive degree and uses only finite dense-polynomial
calculations:

`-w⁻¹ (Z^d-w) + (w⁻¹ d⁻¹ Z) (Z^d-w)' = 1`.

The later layers use that identity to carry every owner around one explicit
rational circuit of the parameter and to calculate the resulting finite
permutation.
-/

namespace Purelib.RootIsolation.Power.Unit.Segment.Homotopy

open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (sub_im sub_re)

/-- Edgewise finite Rouché formula from a displayed residual estimate. -/
private theorem unitRobustSegmentHomotopy_of_residual
    {source parameterStart parameterFinish start finish : Canonical}
    (sourceUnit : normSq source = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (index : Fin degree.value)
    (startInside : (Power.Unit.Box.unitRobustBox (Gaussian.Norm.Nonzero.nonzero_of_normSq_eq_one sourceUnit)
      sourceUnit degree degreeAtLeastTwo index).Contains start)
    (finishInside : (Power.Unit.Box.unitRobustBox (Gaussian.Norm.Nonzero.nonzero_of_normSq_eq_one sourceUnit)
      sourceUnit degree degreeAtLeastTwo index).Contains finish)
    (residual : ∀ {time : Fraction.Rational},
      (0 : Fraction.Rational) ≤ time ∧ time ≤ 1 →
      normSq
          ((Purelib.Geometry.Rational.Affine.line start (finish - start) time) ^ degree.value -
            Purelib.Geometry.Rational.Affine.line parameterStart
              (parameterFinish - parameterStart) time) ≤
        (1 / 8 : Fraction.Rational)) :
    SegmentHomotopyFormula
      (Dense.Gaussian.Power.Coordinate.coordinatePositivePower (degree.value - 1))
      Dense.Gaussian.Monomial.Coordinate.coordinatePolynomial start finish parameterStart
        parameterFinish := open Purelib.Geometry.Rational in by
  let power := Dense.Gaussian.Power.Coordinate.coordinatePositivePower (degree.value - 1)
  let coordinate := Dense.Gaussian.Monomial.Coordinate.coordinatePolynomial
  let A := Dense.Gaussian.Path.Components.pathReal power start (finish - start)
  let B := Dense.Gaussian.Path.Components.pathImag power start (finish - start)
  let U := Dense.Gaussian.Path.Components.pathReal coordinate parameterStart
    (parameterFinish - parameterStart)
  let V := Dense.Gaussian.Path.Components.pathImag coordinate parameterStart
    (parameterFinish - parameterStart)
  let C := U - A
  let D := V - B
  let interval : Data.Rat.Interval.Bounds :=
    { lower := 0, upper := 1, valid := by decide }
  let clearance : Clearance.Pair.Basic.Certificate A B interval :=
    unitRobustSegmentPowerCertificate
      (Gaussian.Norm.Nonzero.nonzero_of_normSq_eq_one sourceUnit) sourceUnit degree degreeAtLeastTwo
      index startInside finishInside
  have exponent : degree.value - 1 + 1 = degree.value :=
    Nat.Subtraction.sub_add_cancel degree.positive
  have startNonzero : power.eval start ≠ 0 := by
    intro zero
    have pair := clearance.eval_ne_zero
      (x := (0 : Fraction.Rational)) (show interval.Contains 0 from ⟨le_rfl, by decide⟩)
    simp only [-eq_self, -iff_self, A, B, Dense.Gaussian.Path.Components.eval_pathReal,
      Dense.Gaussian.Path.Components.eval_pathImag, Affine.Segment.line_segment_zero,
      zero, Gaussian.Basic.zero_re, Gaussian.Basic.zero_im] at pair
    exact pair.elim (fun impossible => impossible rfl)
      (fun impossible => impossible rfl)
  have finishNonzero : power.eval finish ≠ 0 := by
    intro zero
    have pair := clearance.eval_ne_zero
      (x := (1 : Fraction.Rational)) (show interval.Contains 1 from ⟨by decide, le_rfl⟩)
    simp only [-eq_self, -iff_self, A, B, Dense.Gaussian.Path.Components.eval_pathReal,
      Dense.Gaussian.Path.Components.eval_pathImag, Affine.Segment.line_segment_one,
      zero, Gaussian.Basic.zero_re, Gaussian.Basic.zero_im] at pair
    exact pair.elim (fun impossible => impossible rfl)
      (fun impossible => impossible rfl)
  refine
    { sourceStartNonzero := startNonzero
      sourceFinishNonzero := finishNonzero
      data := ?_ }
  apply Dense.Rational.CauchyIndex.Comparison.Dominance.lineData_of_normDominance
    (A := A) (B := B) (C := C) (D := D) (U := U) (V := V)
    (root := interval) (by decide) clearance (1 / 8) (by decide)
  · intro time timeInside
    have powerLower := Power.Unit.Segment.Bounds.unitRobustSegment_power_lower
      (Gaussian.Norm.Nonzero.nonzero_of_normSq_eq_one sourceUnit) sourceUnit degree degreeAtLeastTwo
      index startInside finishInside timeInside
    have errorUpper := residual timeInside
    have powerCoordinates : (1 / 4 : Fraction.Rational) ≤
        A.eval time ^ 2 + B.eval time ^ 2 := by
      rw [← Gaussian.Power.normSq_pow] at powerLower
      rw [← exponent] at powerLower
      simpa only [-eq_self, -iff_self, A, B, power, Dense.Gaussian.Path.Components.eval_pathReal,
        Dense.Gaussian.Path.Components.eval_pathImag,
        Dense.Gaussian.Power.Coordinate.coordinatePositivePower_eval, normSq] using powerLower
    have errorCoordinates : C.eval time ^ 2 + D.eval time ^ 2 ≤
        (1 / 8 : Fraction.Rational) := by
      calc
        C.eval time ^ 2 + D.eval time ^ 2 =
            normSq
              (Affine.line parameterStart
                  (parameterFinish - parameterStart) time -
                (Affine.line start (finish - start) time) ^
                  degree.value) := by
          simp only [-eq_self, -iff_self, C, D, U, V, A, B, power, coordinate, DensePolynomial.eval_sub,
            Dense.Gaussian.Path.Components.eval_pathReal,
            Dense.Gaussian.Path.Components.eval_pathImag,
            Dense.Gaussian.Power.Coordinate.coordinatePositivePower_eval,
            Dense.Gaussian.Monomial.Coordinate.coordinatePolynomial_eval, exponent, normSq,
            sub_re, sub_im]
          rfl
        _ = normSq
              ((Affine.line start (finish - start) time) ^
                  degree.value -
                Affine.line parameterStart
                  (parameterFinish - parameterStart) time) := by
          simp only [-eq_self, -iff_self, normSq, sub_re, sub_im]
          ring1
        _ ≤ 1 / 8 := errorUpper
    calc
      (1 / 8 : Fraction.Rational) = 1 / 4 - 1 / 8 := by decide
      _ ≤ (A.eval time ^ 2 + B.eval time ^ 2) -
          (C.eval time ^ 2 + D.eval time ^ 2) :=
        Fraction.Order.Arithmetic.sub_le_sub_direct powerCoordinates
          errorCoordinates
  · intro time
    simp only [-eq_self, -iff_self, C, U, A, DensePolynomial.eval_sub]
    ring1
  · intro time
    simp only [-eq_self, -iff_self, D, V, B, DensePolynomial.eval_sub]
    ring1
end Purelib.RootIsolation.Power.Unit.Segment.Homotopy

end

section
public section

/-!
# Finite monodromy for `Z^d - w`

This file specializes finite owner monodromy to the displayed power family.
The first layer records the exact off-zero Bézout identity.  It is uniform in
the displayed positive degree and uses only finite dense-polynomial
calculations:

`-w⁻¹ (Z^d-w) + (w⁻¹ d⁻¹ Z) (Z^d-w)' = 1`.

The later layers use that identity to carry every owner around one explicit
rational circuit of the parameter and to calculate the resulting finite
permutation.
-/

namespace Purelib.RootIsolation.Power.Unit.Segment.Homotopy

open Purelib.Data.Gaussian

/-- The two connector edges after a parameter move are compared with the
constant target parameter. -/
theorem unitRobustSegmentConstantTargetHomotopy
    {source target start finish : Canonical}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : Power.Unit.Move.Budget.UnitMoveSmall sourceUnit targetUnit degree degreeAtLeastTwo)
    (index : Fin degree.value)
    (startInside : (Power.Unit.Box.unitRobustBox (Gaussian.Norm.Nonzero.nonzero_of_normSq_eq_one sourceUnit)
      sourceUnit degree degreeAtLeastTwo index).Contains start)
    (finishInside : (Power.Unit.Box.unitRobustBox (Gaussian.Norm.Nonzero.nonzero_of_normSq_eq_one sourceUnit)
      sourceUnit degree degreeAtLeastTwo index).Contains finish) :
    SegmentHomotopyFormula
      (Dense.Gaussian.Power.Coordinate.coordinatePositivePower (degree.value - 1))
      Dense.Gaussian.Monomial.Coordinate.coordinatePolynomial start finish target target := by
  apply unitRobustSegmentHomotopy_of_residual sourceUnit degree degreeAtLeastTwo
    index startInside finishInside
  intro time timeInside
  rw [Geometry.Rational.Affine.Segment.line_self]
  exact Power.Unit.Segment.Residual.unitRobustSegment_constantTarget_residual_le_eighth sourceUnit
    targetUnit degree degreeAtLeastTwo small index startInside finishInside
    timeInside
end Purelib.RootIsolation.Power.Unit.Segment.Homotopy

end

section
public section

/-!
# Finite monodromy for `Z^d - w`

This file specializes finite owner monodromy to the displayed power family.
The first layer records the exact off-zero Bézout identity.  It is uniform in
the displayed positive degree and uses only finite dense-polynomial
calculations:

`-w⁻¹ (Z^d-w) + (w⁻¹ d⁻¹ Z) (Z^d-w)' = 1`.

The later layers use that identity to carry every owner around one explicit
rational circuit of the parameter and to calculate the resulting finite
permutation.
-/

namespace Purelib.RootIsolation.Power.Unit.Segment.Homotopy

open Purelib.Data.Gaussian

/-- Edgewise finite Rouché formula comparing a robust lifted segment with
the synchronized parameter segment. -/
theorem unitRobustSegmentHomotopy
    {source target start finish : Canonical}
    (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (small : Power.Unit.Move.Budget.UnitMoveSmall sourceUnit targetUnit degree degreeAtLeastTwo)
    (index : Fin degree.value)
    (startInside : (Power.Unit.Box.unitRobustBox (Gaussian.Norm.Nonzero.nonzero_of_normSq_eq_one sourceUnit)
      sourceUnit degree degreeAtLeastTwo index).Contains start)
    (finishInside : (Power.Unit.Box.unitRobustBox (Gaussian.Norm.Nonzero.nonzero_of_normSq_eq_one sourceUnit)
      sourceUnit degree degreeAtLeastTwo index).Contains finish) :
    SegmentHomotopyFormula
      (Dense.Gaussian.Power.Coordinate.coordinatePositivePower (degree.value - 1))
      Dense.Gaussian.Monomial.Coordinate.coordinatePolynomial start finish source target := by
  apply unitRobustSegmentHomotopy_of_residual sourceUnit degree degreeAtLeastTwo
    index startInside finishInside
  intro time timeInside
  exact Power.Unit.Segment.Residual.unitRobustSegment_parameter_residual_le_eighth sourceUnit targetUnit
    degree degreeAtLeastTwo small index startInside finishInside timeInside
end Purelib.RootIsolation.Power.Unit.Segment.Homotopy

end
