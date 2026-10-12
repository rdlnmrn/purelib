module
import Purelib.Algebra.Field.Cancellation
import Purelib.Algebra.Field.ExplicitField
import Purelib.Curves.Plane.Conic.Basic
import Purelib.Curves.Plane.Conic.Center
public import Purelib.Curves.Plane.Conic.QuadraticPart
public import Purelib.Curves.Plane.Conic.Scale
public import Purelib.Geometry.Conics.Grammola.Basic
import Purelib.Geometry.Conics.Grammola.Center
import Purelib.Geometry.Plane.Line.Basic
public import Purelib.Geometry.Plane.Line.DirectionProduct
public import Purelib.Geometry.Plane.Line.Intersection
import Purelib.Geometry.Plane.Line.Relations
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Geometry.Plane.Point.Basic
import Purelib.Tactic.Ring
meta import Mathlib.Tactic.Linter.Lint

open Purelib

open Purelib.Curves.Plane

open Purelib.Curves.Plane.Conic

open Purelib.Curves.Plane.Conic.QuadraticPart

open Purelib.Geometry.Conics.Grammola

open Purelib.Geometry.Conics.Grammola

open Purelib.Geometry.Plane

open Purelib.Geometry.Plane.Line

open Purelib.Geometry.Plane.Line.DirectionProduct

section
@[expose] public section

/-!
# Divine Proportions, Exercise 15.14

The quadratic coefficients of a grammola determine a binary quadratic whose
two factors are its diagonal directions.  This avoids diagonalizing a matrix
or selecting square roots.  The unique center then restores the affine line
offsets, and evaluation at that center restores the associated quadrance.
-/

namespace Purelib.Geometry

namespace Conics.Grammola.Uniqueness

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-- The conic-determined binary quadratic whose factors are the two grammola diagonal directions. -/
def diagonalRecoveryValue (conic : Conic K) (x y
  : K) : K :=
  2 * (conic.d + conic.f) * Grammola.quadraticValue conic x y -
    Grammola.fourQuadraticDeterminant conic * (x ^ 2 + y ^ 2)

/-- For a grammola conic, the recovery quadratic is a visibly nonzero scalar multiple of the product of its two diagonal
direction forms. -/
theorem diagonalRecoveryValue_conic [DecidableEq K]
    (firstDiagonal secondDiagonal : Plane.Line K)
    (firstNonNull : ¬ firstDiagonal.IsNull)
    (secondNonNull : ¬ secondDiagonal.IsNull)
    (associatedQuadrance : K) (twoNonzero : (2 : K) ≠ 0)
    (x y : K) :
    diagonalRecoveryValue
        (Grammola.conic firstDiagonal secondDiagonal firstNonNull secondNonNull
          associatedQuadrance twoNonzero) x y =
      8 * Line.Basic.lineNorm firstDiagonal * Line.Basic.lineNorm secondDiagonal *
        (firstDiagonal.a * secondDiagonal.a +
          firstDiagonal.b * secondDiagonal.b) *
        Grammola.directionProduct firstDiagonal secondDiagonal x y := by
  unfold diagonalRecoveryValue Grammola.quadraticValue Grammola.fourQuadraticDeterminant
    Grammola.directionProduct Grammola.conic Grammola.conicD Grammola.conicE Grammola.conicF Line.Basic.lineNorm
  ring1

/-- The recovery quadratic scales quadratically when all six conic coefficients are rescaled. -/
theorem diagonalRecoveryValue_coefficientScale
    {source target : Conic K} {scale : K}
    (sameConic : Scale.CoefficientScale source target scale)
    (x y : K) :
    diagonalRecoveryValue source x y =
      scale ^ 2 * diagonalRecoveryValue target x y := by
  unfold diagonalRecoveryValue Grammola.quadraticValue Grammola.fourQuadraticDeterminant
  rw [sameConic.d, sameConic.e, sameConic.f]
  ring1

/-- The scalar in the diagonal recovery factorization is nonzero for a valid grammola. -/
theorem diagonalRecoveryFactor_nonzero
    (firstDiagonal secondDiagonal : Plane.Line K) (associatedQuadrance : K)
    (presentation : Grammola.Presentation firstDiagonal secondDiagonal
      associatedQuadrance)
    (twoNonzero : (2 : K) ≠ 0) :
    8 * Line.Basic.lineNorm firstDiagonal * Line.Basic.lineNorm secondDiagonal *
        (firstDiagonal.a * secondDiagonal.a +
          firstDiagonal.b * secondDiagonal.b) ≠ 0 := by
  have fourNonzero : (4 : K) ≠ 0 := by
    have productNonzero : (2 : K) * 2 ≠ 0 :=
      Algebra.Field.ExplicitField.mul_ne_zero twoNonzero twoNonzero
    simpa only [show (4 : K) = 2 * 2 by ring1] using productNonzero
  have eightNonzero : (8 : K) ≠ 0 := by
    have productNonzero : (4 : K) * 2 ≠ 0 :=
      Algebra.Field.ExplicitField.mul_ne_zero fourNonzero twoNonzero
    simpa only [show (8 : K) = 4 * 2 by ring1] using productNonzero
  have dotNonzero :
      firstDiagonal.a * secondDiagonal.a +
          firstDiagonal.b * secondDiagonal.b ≠ 0 :=
    presentation.notPerpendicular
  exact Algebra.Field.ExplicitField.mul_ne_zero
    (Algebra.Field.ExplicitField.mul_ne_zero
      (Algebra.Field.ExplicitField.mul_ne_zero eightNonzero
        presentation.firstNonNull)
      presentation.secondNonNull)
    dotNonzero

/-- At the intersection of the diagonals, twice the conic evaluation is the negative associated quadrance times the
quadratic trace. -/
theorem center_evaluation_relation [DecidableEq K]
    (firstDiagonal secondDiagonal : Plane.Line K) (associatedQuadrance : K)
    (presentation : Grammola.Presentation firstDiagonal secondDiagonal
      associatedQuadrance)
    (twoNonzero : (2 : K) ≠ 0) :
    let center := Intersection.lineIntersection firstDiagonal secondDiagonal
      presentation.notParallel
    let grammolaConic :=
      Grammola.conic firstDiagonal secondDiagonal presentation.firstNonNull
        presentation.secondNonNull associatedQuadrance twoNonzero
    2 * grammolaConic.evaluate center =
      -associatedQuadrance * (grammolaConic.d + grammolaConic.f) := by
  dsimp only
  let center := Intersection.lineIntersection firstDiagonal secondDiagonal
    presentation.notParallel
  have onFirst : firstDiagonal.Contains center :=
    Intersection.lineIntersection_on_first firstDiagonal secondDiagonal
      presentation.notParallel
  have onSecond : secondDiagonal.Contains center :=
    Intersection.lineIntersection_on_second firstDiagonal secondDiagonal
      presentation.notParallel
  unfold Plane.Line.Contains at onFirst onSecond
  rw [Grammola.conic_evaluate, Grammola.conic_trace]
  unfold Grammola.clearedEvaluate Basic.lineValue
  rw [onFirst, onSecond]
  ring1

/-- Exercise 15.14: two valid grammola presentations of the same displayed conic proportion have the same associated
quadrance and the same unordered pair of diagonal lines. -/
theorem exercise_15_14 [DecidableEq K]
    (firstDiagonal₁ firstDiagonal₂ secondDiagonal₁ secondDiagonal₂ :
      Plane.Line K)
    (firstAssociated secondAssociated : K)
    (firstPresentation :
      Grammola.Presentation firstDiagonal₁ firstDiagonal₂ firstAssociated)
    (secondPresentation :
      Grammola.Presentation secondDiagonal₁ secondDiagonal₂ secondAssociated)
    (twoNonzero : (2 : K) ≠ 0) (scale : K) (scaleNonzero : scale ≠ 0)
    (sameConic :
      Scale.CoefficientScale
        (Grammola.conic firstDiagonal₁ firstDiagonal₂
          firstPresentation.firstNonNull firstPresentation.secondNonNull
          firstAssociated twoNonzero)
        (Grammola.conic secondDiagonal₁ secondDiagonal₂
          secondPresentation.firstNonNull secondPresentation.secondNonNull
          secondAssociated twoNonzero)
        scale) :
    firstAssociated = secondAssociated ∧
      (((firstDiagonal₁.Equivalent secondDiagonal₁) ∧
          (firstDiagonal₂.Equivalent secondDiagonal₂)) ∨
        ((firstDiagonal₁.Equivalent secondDiagonal₂) ∧
          (firstDiagonal₂.Equivalent secondDiagonal₁))) := by
  let firstConic :=
    Grammola.conic firstDiagonal₁ firstDiagonal₂ firstPresentation.firstNonNull
      firstPresentation.secondNonNull firstAssociated twoNonzero
  let secondConic :=
    Grammola.conic secondDiagonal₁ secondDiagonal₂ secondPresentation.firstNonNull
      secondPresentation.secondNonNull secondAssociated twoNonzero
  let firstCenter := Intersection.lineIntersection firstDiagonal₁ firstDiagonal₂
    firstPresentation.notParallel
  let secondCenter := Intersection.lineIntersection secondDiagonal₁ secondDiagonal₂
    secondPresentation.notParallel
  have firstDiscriminantNonzero : firstConic.centerDiscriminant ≠ 0 := by
    unfold firstConic
    exact Center.conic_centerDiscriminant_nonzero firstDiagonal₁ firstDiagonal₂
      firstAssociated firstPresentation twoNonzero
  have firstIsCenter : firstConic.IsCenter firstCenter := by
    unfold firstConic firstCenter
    exact Center.exercise_15_15 firstDiagonal₁ firstDiagonal₂ firstAssociated
      firstPresentation twoNonzero
  have secondIsCenter : secondConic.IsCenter secondCenter := by
    unfold secondConic secondCenter
    exact Center.exercise_15_15 secondDiagonal₁ secondDiagonal₂ secondAssociated
      secondPresentation twoNonzero
  have secondCenterForFirst : firstConic.IsCenter secondCenter :=
    sameConic.isCenter secondCenter secondIsCenter
  have centersEqual : firstCenter = secondCenter := by
    have firstFormula := Conic.center_eq_centerPoint firstConic firstCenter
      firstDiscriminantNonzero firstIsCenter
    have secondFormula := Conic.center_eq_centerPoint firstConic secondCenter
      firstDiscriminantNonzero secondCenterForFirst
    exact firstFormula.trans secondFormula.symm
  have traceScale :
      firstConic.d + firstConic.f =
        scale * (secondConic.d + secondConic.f) := by
    rw [sameConic.d, sameConic.f]
    ring1
  have firstTraceNonzero : firstConic.d + firstConic.f ≠ 0 := by
    unfold firstConic
    exact Grammola.conic_trace_nonzero firstDiagonal₁ firstDiagonal₂
      firstPresentation.firstNonNull firstPresentation.secondNonNull
      firstAssociated twoNonzero
  have firstCenterRelation :
      2 * firstConic.evaluate firstCenter =
        -firstAssociated * (firstConic.d + firstConic.f) := by
    unfold firstConic firstCenter
    exact center_evaluation_relation firstDiagonal₁ firstDiagonal₂
      firstAssociated firstPresentation twoNonzero
  have secondCenterRelation :
      2 * secondConic.evaluate secondCenter =
        -secondAssociated * (secondConic.d + secondConic.f) := by
    unfold secondConic secondCenter
    exact center_evaluation_relation secondDiagonal₁ secondDiagonal₂
      secondAssociated secondPresentation twoNonzero
  have evaluationScale := sameConic.evaluate secondCenter
  have associatedTraceProducts :
      firstConic.d + firstConic.f |> fun trace => trace * firstAssociated =
        (firstConic.d + firstConic.f) * secondAssociated := by
    calc
      (firstConic.d + firstConic.f) * firstAssociated =
          -(-firstAssociated * (firstConic.d + firstConic.f)) := by ring1
      _ = -(2 * firstConic.evaluate firstCenter) := by
        rw [firstCenterRelation]
      _ = -(2 * firstConic.evaluate secondCenter) := by rw [centersEqual]
      _ = -(2 * (scale * secondConic.evaluate secondCenter)) := by
        rw [evaluationScale]
      _ = -scale *
          (2 * secondConic.evaluate secondCenter) := by ring1
      _ = -scale *
          (-secondAssociated * (secondConic.d + secondConic.f)) := by
            rw [secondCenterRelation]
      _ = (scale * (secondConic.d + secondConic.f)) *
          secondAssociated := by ring1
      _ = (firstConic.d + firstConic.f) * secondAssociated := by
        rw [traceScale]
  have associatedEqual : firstAssociated = secondAssociated :=
    Algebra.Field.ExplicitField.eq_of_mul_eq_mul_left firstTraceNonzero associatedTraceProducts
  have firstRecoveryFactorNonzero :=
    diagonalRecoveryFactor_nonzero firstDiagonal₁ firstDiagonal₂
      firstAssociated firstPresentation twoNonzero
  have secondRecoveryFactorNonzero :=
    diagonalRecoveryFactor_nonzero secondDiagonal₁ secondDiagonal₂
      secondAssociated secondPresentation twoNonzero
  let firstFactor :=
    8 * Line.Basic.lineNorm firstDiagonal₁ * Line.Basic.lineNorm firstDiagonal₂ *
      (firstDiagonal₁.a * firstDiagonal₂.a +
        firstDiagonal₁.b * firstDiagonal₂.b)
  let secondFactor :=
    8 * Line.Basic.lineNorm secondDiagonal₁ * Line.Basic.lineNorm secondDiagonal₂ *
      (secondDiagonal₁.a * secondDiagonal₂.a +
        secondDiagonal₁.b * secondDiagonal₂.b)
  let productScale := scale ^ 2 * secondFactor / firstFactor
  have productScaleNonzero : productScale ≠ 0 := by
    have scaleSquareNonzero : scale ^ 2 ≠ 0 := by
      simpa only [pow_two] using
        Algebra.Field.ExplicitField.mul_ne_zero scaleNonzero scaleNonzero
    apply Algebra.Field.ExplicitField.div_ne_zero
    · exact Algebra.Field.ExplicitField.mul_ne_zero scaleSquareNonzero
        secondRecoveryFactorNonzero
    · exact firstRecoveryFactorNonzero
  have productScaleCancel : productScale * firstFactor =
      scale ^ 2 * secondFactor := by
    unfold productScale
    exact Algebra.Field.ExplicitField.div_mul_cancel _ firstRecoveryFactorNonzero
  have directionProductsEqual (x y : K) :
      Grammola.directionProduct firstDiagonal₁ firstDiagonal₂ x y =
        productScale *
          Grammola.directionProduct secondDiagonal₁ secondDiagonal₂ x y := by
    apply Algebra.Field.ExplicitField.eq_of_mul_eq_mul_left firstRecoveryFactorNonzero
    calc
      firstFactor * Grammola.directionProduct firstDiagonal₁ firstDiagonal₂ x y =
          diagonalRecoveryValue firstConic x y := by
            unfold firstFactor firstConic
            exact (diagonalRecoveryValue_conic firstDiagonal₁
              firstDiagonal₂
              firstPresentation.firstNonNull firstPresentation.secondNonNull
              firstAssociated twoNonzero x y).symm
      _ = scale ^ 2 * diagonalRecoveryValue secondConic x y :=
        diagonalRecoveryValue_coefficientScale sameConic x y
      _ = scale ^ 2 *
          (secondFactor *
            Grammola.directionProduct secondDiagonal₁ secondDiagonal₂ x y) := by
              unfold secondFactor secondConic
              rw [diagonalRecoveryValue_conic]
      _ = firstFactor *
          (productScale *
            Grammola.directionProduct secondDiagonal₁ secondDiagonal₂ x y) := by
              calc
                scale ^ 2 *
                    (secondFactor *
                      Grammola.directionProduct secondDiagonal₁ secondDiagonal₂ x y) =
                    (scale ^ 2 * secondFactor) *
                      Grammola.directionProduct secondDiagonal₁ secondDiagonal₂ x y := by
                        ring1
                _ = (productScale * firstFactor) *
                    Grammola.directionProduct secondDiagonal₁ secondDiagonal₂ x y := by
                      rw [productScaleCancel]
                _ = firstFactor *
                    (productScale *
                      Grammola.directionProduct secondDiagonal₁ secondDiagonal₂ x y) := by
                        ring1
  have directionPairs := Grammola.directionPairs_unique_of_product_scale
    firstDiagonal₁ firstDiagonal₂ secondDiagonal₁ secondDiagonal₂
      firstPresentation.notParallel productScale productScaleNonzero
      directionProductsEqual
  have firstOneContains : firstDiagonal₁.Contains firstCenter :=
    Intersection.lineIntersection_on_first firstDiagonal₁ firstDiagonal₂
      firstPresentation.notParallel
  have firstTwoContains : firstDiagonal₂.Contains firstCenter :=
    Intersection.lineIntersection_on_second firstDiagonal₁ firstDiagonal₂
      firstPresentation.notParallel
  have secondOneContains : secondDiagonal₁.Contains firstCenter := by
    rw [centersEqual]
    exact Intersection.lineIntersection_on_first secondDiagonal₁ secondDiagonal₂
      secondPresentation.notParallel
  have secondTwoContains : secondDiagonal₂.Contains firstCenter := by
    rw [centersEqual]
    exact Intersection.lineIntersection_on_second secondDiagonal₁ secondDiagonal₂
      secondPresentation.notParallel
  refine ⟨associatedEqual, ?_⟩
  rcases directionPairs with ordered | swapped
  · exact Or.inl ⟨
      Relations.line_equivalent_of_parallel_and_common_point firstDiagonal₁
        secondDiagonal₁ firstCenter ordered.1 firstOneContains
        secondOneContains,
      Relations.line_equivalent_of_parallel_and_common_point firstDiagonal₂
        secondDiagonal₂ firstCenter ordered.2 firstTwoContains
        secondTwoContains⟩
  · exact Or.inr ⟨
      Relations.line_equivalent_of_parallel_and_common_point firstDiagonal₁
        secondDiagonal₂ firstCenter swapped.1 firstOneContains
        secondTwoContains,
      Relations.line_equivalent_of_parallel_and_common_point firstDiagonal₂
        secondDiagonal₁ firstCenter swapped.2 firstTwoContains
        secondOneContains⟩

end Conics.Grammola.Uniqueness

end Purelib.Geometry

end
