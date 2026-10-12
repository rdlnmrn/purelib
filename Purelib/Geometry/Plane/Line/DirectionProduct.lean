module
import Purelib.Algebra.Field.Cancellation
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Geometry.Plane.Line.Basic
import Purelib.Geometry.Plane.Line.Relations
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Purelib.Tactic.Ring

open Purelib

open Purelib.Algebra.Field

open Purelib.Geometry.Plane

open Purelib.Geometry.Plane.Line

open Purelib.Geometry.Plane.Line.Basic

section
@[expose] public section

/-!
# Divine Proportions, Exercise 15.14

The quadratic coefficients of a grammola determine a binary quadratic whose
two factors are its diagonal directions.  This avoids diagonalizing a matrix
or selecting square roots.  The unique center then restores the affine line
offsets, and evaluation at that center restores the associated quadrance.
-/

namespace Purelib.Geometry.Plane.Line.DirectionProduct.Grammola

section

variable {K : Type*} [ExplicitField K]

/-- The homogeneous product of two displayed line direction forms. -/
def directionProduct (first second : Plane.Line K) (x
  y : K) : K :=
  (first.a * x + first.b * y) * (second.a * x + second.b * y)

/-- A nonparallel pair of line directions is determined, up to swapping, by the product of its two linear forms up to a
nonzero scale. -/
theorem directionPairs_unique_of_product_scale [DecidableEq
  K]
    (firstOne firstTwo secondOne secondTwo : Plane.Line K)
    (firstNotParallel : ¬ firstOne.Parallel firstTwo)
    (scale : K) (scaleNonzero : scale ≠ 0)
    (productsEqual : ∀ x y : K,
      directionProduct firstOne firstTwo x y =
        scale * directionProduct secondOne secondTwo x y) :
    ((firstOne.Parallel secondOne ∧ firstTwo.Parallel secondTwo) ∨
      (firstOne.Parallel secondTwo ∧ firstTwo.Parallel secondOne)) := by
  have firstDirection := productsEqual firstOne.b (-firstOne.a)
  have secondDirection := productsEqual firstTwo.b (-firstTwo.a)
  have firstProductZero :
      (secondOne.a * firstOne.b - secondOne.b * firstOne.a) *
          (secondTwo.a * firstOne.b - secondTwo.b * firstOne.a) = 0 := by
    apply ExplicitField.eq_zero_of_mul_eq_zero_left scaleNonzero
    calc
      scale *
          ((secondOne.a * firstOne.b - secondOne.b * firstOne.a) *
            (secondTwo.a * firstOne.b - secondTwo.b * firstOne.a)) =
        scale * directionProduct secondOne secondTwo
          firstOne.b (-firstOne.a) := by
            unfold directionProduct
            ring1
      _ = directionProduct firstOne firstTwo
          firstOne.b (-firstOne.a) := firstDirection.symm
      _ = 0 := by unfold directionProduct; ring1
  have secondProductZero :
      (secondOne.a * firstTwo.b - secondOne.b * firstTwo.a) *
          (secondTwo.a * firstTwo.b - secondTwo.b * firstTwo.a) = 0 := by
    apply ExplicitField.eq_zero_of_mul_eq_zero_left scaleNonzero
    calc
      scale *
          ((secondOne.a * firstTwo.b - secondOne.b * firstTwo.a) *
            (secondTwo.a * firstTwo.b - secondTwo.b * firstTwo.a)) =
        scale * directionProduct secondOne secondTwo
          firstTwo.b (-firstTwo.a) := by
            unfold directionProduct
            ring1
      _ = directionProduct firstOne firstTwo
          firstTwo.b (-firstTwo.a) := secondDirection.symm
      _ = 0 := by unfold directionProduct; ring1
  have parallelIffFactorZero (source target : Plane.Line K) :
      source.Parallel target ↔
        target.a * source.b - target.b * source.a = 0 := by
    unfold Line.Parallel
    constructor <;> intro equation
    · calc
        target.a * source.b - target.b * source.a =
            -(source.a * target.b - target.a * source.b) := by ring1
        _ = 0 := by rw [equation]; ring1
    · calc
        source.a * target.b - target.a * source.b =
            -(target.a * source.b - target.b * source.a) := by ring1
        _ = 0 := by rw [equation]; ring1
  by_cases firstFactorZero :
      secondOne.a * firstOne.b - secondOne.b * firstOne.a = 0
  · have firstToSecondOne : firstOne.Parallel secondOne :=
      (parallelIffFactorZero firstOne secondOne).2 firstFactorZero
    have secondOneAtFirstTwoNonzero :
        secondOne.a * firstTwo.b - secondOne.b * firstTwo.a ≠ 0 := by
      intro factorZero
      have firstTwoToSecondOne : firstTwo.Parallel secondOne :=
        (parallelIffFactorZero firstTwo secondOne).2 factorZero
      apply firstNotParallel
      exact Relations.line_parallel_trans firstToSecondOne
        (Plane.Line.parallel_symm firstTwoToSecondOne)
    have secondTwoAtFirstTwoZero :
        secondTwo.a * firstTwo.b - secondTwo.b * firstTwo.a = 0 := by
      exact ExplicitField.eq_zero_of_mul_eq_zero_left secondOneAtFirstTwoNonzero
        secondProductZero
    have firstTwoToSecondTwo : firstTwo.Parallel secondTwo :=
      (parallelIffFactorZero firstTwo secondTwo).2 secondTwoAtFirstTwoZero
    exact Or.inl ⟨firstToSecondOne, firstTwoToSecondTwo⟩
  · have secondTwoAtFirstOneZero :
        secondTwo.a * firstOne.b - secondTwo.b * firstOne.a = 0 := by
      exact ExplicitField.eq_zero_of_mul_eq_zero_left firstFactorZero firstProductZero
    have firstToSecondTwo : firstOne.Parallel secondTwo :=
      (parallelIffFactorZero firstOne secondTwo).2 secondTwoAtFirstOneZero
    have secondTwoAtFirstTwoNonzero :
        secondTwo.a * firstTwo.b - secondTwo.b * firstTwo.a ≠ 0 := by
      intro factorZero
      have firstTwoToSecondTwo : firstTwo.Parallel secondTwo :=
        (parallelIffFactorZero firstTwo secondTwo).2 factorZero
      apply firstNotParallel
      exact Relations.line_parallel_trans firstToSecondTwo
        (Plane.Line.parallel_symm firstTwoToSecondTwo)
    have secondOneAtFirstTwoZero :
        secondOne.a * firstTwo.b - secondOne.b * firstTwo.a = 0 := by
      exact ExplicitField.eq_zero_of_mul_eq_zero_right
        secondTwoAtFirstTwoNonzero
        secondProductZero
    have firstTwoToSecondOne : firstTwo.Parallel secondOne :=
      (parallelIffFactorZero firstTwo secondOne).2 secondOneAtFirstTwoZero
    exact Or.inr ⟨firstToSecondTwo, firstTwoToSecondOne⟩
end

end Purelib.Geometry.Plane.Line.DirectionProduct.Grammola

end
