module
-- Retained public numeral and subtraction parents use their original operations.
public import Purelib.Data.Nat.Order
public import Purelib.Algebra.Group.Negation
import Purelib.Algebra.Field.Ratio
import Purelib.Algebra.Field.Cancellation
import Purelib.Algebra.Field.ExplicitField
import Purelib.Geometry.Plane.Line.Construction
import Purelib.Geometry.Plane.Line.Incidence
import Purelib.Geometry.Plane.Line.Intersection
import Purelib.Geometry.Plane.Point.Basic
public import Purelib.Geometry.Triangles.Orthocenter.Basic
import Purelib.LinearAlgebra.Alternating.Bracket.Fin3
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Logic.Nontrivial.Defs
import Purelib.Tactic.Ring

section
open Purelib
open Purelib.Algebra.Field
open Purelib.Geometry
open Purelib.Geometry.Plane.Line
open Purelib.Geometry.Triangles
open Purelib.LinearAlgebra.Alternating.Bracket

open scoped Purelib.Data.Nat
attribute [local instance 2000] Purelib.Data.Nat.successorNeZero
  Purelib.Data.Nat.successorAtLeastTwo
  Purelib.Algebra.Group.Negation.subNegZeroMonoid

section
public section

/-!
# Divine Proportions, §12.4: the orthocenter formula

The two numerators below are the source's antisymmetric brackets
`[x₁x₂y₂]⁻ + [y₁y₂²]⁻` and
`[x₁y₁y₂]⁻ + [x₁²x₂]⁻`.  Each is written with the reusable six-term
antisymmetric product introduced for Theorem 83.
-/

section

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

namespace Purelib.Geometry.Triangles.Orthocenter.Formula

/-- The printed x-numerator `[x₁x₂y₂]⁻ + [y₁y₂²]⁻`. -/
@[expose] def orthocenterXNumerator (first second third : Plane.Point K) : K :=
  Fin3.antisymmetricTripleProduct
      first.x second.x third.x
      (first.x * first.y) (second.x * second.y) (third.x * third.y) +
    Fin3.antisymmetricTripleProduct
      first.y second.y third.y
      (first.y ^ 2) (second.y ^ 2) (third.y ^ 2)

/-- The printed y-numerator `[x₁y₁y₂]⁻ + [x₁²x₂]⁻`. -/
@[expose] def orthocenterYNumerator (first second third : Plane.Point K) : K :=
  Fin3.antisymmetricTripleProduct
      (first.x * first.y) (second.x * second.y) (third.x * third.y)
      first.y second.y third.y +
    Fin3.antisymmetricTripleProduct
      (first.x ^ 2) (second.x ^ 2) (third.x ^ 2)
      first.x second.x third.x

/-- The orthocenter coordinates given by alternating-product numerators divided by the coordinate determinant.

The definition computes the displayed quotients; noncollinearity certifies their denominator in the equality theorem. -/
@[expose] def orthocenterFormula (first second third : Plane.Point K) : Plane.Point K :=
  let denominator := Fin3.antisymmetricTripleProduct
    first.x second.x third.x first.y second.y third.y
  ⟨Geometry.Triangles.Orthocenter.Formula.orthocenterXNumerator first second third / denominator,
    Geometry.Triangles.Orthocenter.Formula.orthocenterYNumerator first second third / denominator⟩

/-- The intersection-defined orthocenter equals the alternating-product coordinate formula.

Noncollinearity supplies the nonzero determinant used in the coordinate cancellations. -/
theorem orthocenter_formula
    [Nontrivial K] [DecidableEq K]
    (first second third : Plane.Point K)
    (firstThirdDistinct : first ≠ third)
    (secondThirdDistinct : second ≠ third)
    (notCollinear : ¬ Incidence.Collinear first second third) :
    Orthocenter.Basic.orthocenterPoint first second third firstThirdDistinct
        secondThirdDistinct notCollinear =
      Orthocenter.Formula.orthocenterFormula first second third := by
  let determinant := Incidence.pointDeterminant first second third
  let xNumerator := Geometry.Triangles.Orthocenter.Formula.orthocenterXNumerator first second third
  let yNumerator := Geometry.Triangles.Orthocenter.Formula.orthocenterYNumerator first second third
  let firstAltitude :=
    Orthocenter.Basic.triangleAltitudeFromFirst first second third secondThirdDistinct
  let secondAltitude :=
    Orthocenter.Basic.triangleAltitudeFromSecond first second third firstThirdDistinct
  have determinantNonzero : determinant ≠ 0 := by
    intro determinantZero
    apply notCollinear
    exact (Incidence.collinear_iff_pointDeterminant_eq_zero first second third).2
      determinantZero
  have negativeDeterminantNonzero : -determinant ≠ 0 :=
    (fun {K : Type _} [Purelib.Algebra.Field.ExplicitField K] {value : K} (nonzero : value ≠ 0) =>
      (Purelib.Algebra.Field.ExplicitField.neg_ne_zero_of_ne_zero (K := K) (value := value) nonzero : -value ≠ 0))
      determinantNonzero
  have antisymmetricDenominator :
      Fin3.antisymmetricTripleProduct
          first.x second.x third.x first.y second.y third.y =
        determinant := by
    exact (Incidence.pointDeterminant_eq_antisymmetricTripleProduct
      first second third).symm
  have formulaDenominatorNonzero :
      Fin3.antisymmetricTripleProduct
          first.x second.x third.x first.y second.y third.y ≠ 0 := by
    rw [antisymmetricDenominator]
    exact determinantNonzero
  have intersectionDenominator :
      firstAltitude.a * secondAltitude.b -
          secondAltitude.a * firstAltitude.b = -determinant := by
    unfold firstAltitude secondAltitude Orthocenter.Basic.triangleAltitudeFromFirst
      Orthocenter.Basic.triangleAltitudeFromSecond Construction.altitudeThrough Incidence.lineThrough determinant
      Incidence.pointDeterminant
    ring1
  have intersectionXNumerator :
      firstAltitude.b * secondAltitude.c -
          secondAltitude.b * firstAltitude.c = -xNumerator := by
    unfold firstAltitude secondAltitude Orthocenter.Basic.triangleAltitudeFromFirst
      Orthocenter.Basic.triangleAltitudeFromSecond Construction.altitudeThrough Incidence.lineThrough xNumerator
      Geometry.Triangles.Orthocenter.Formula.orthocenterXNumerator Fin3.antisymmetricTripleProduct
    ring1
  have intersectionYNumerator :
      firstAltitude.c * secondAltitude.a -
          secondAltitude.c * firstAltitude.a = -yNumerator := by
    unfold firstAltitude secondAltitude Orthocenter.Basic.triangleAltitudeFromFirst
      Orthocenter.Basic.triangleAltitudeFromSecond Construction.altitudeThrough Incidence.lineThrough yNumerator
      Geometry.Triangles.Orthocenter.Formula.orthocenterYNumerator Fin3.antisymmetricTripleProduct
    ring1
  have xRatio :
      (-xNumerator) / (-determinant) =
        xNumerator /
          Fin3.antisymmetricTripleProduct
            first.x second.x third.x first.y second.y third.y := by
    apply Ratio.ratio_eq_of_cross_product negativeDeterminantNonzero
      formulaDenominatorNonzero
    rw [antisymmetricDenominator]
    ring1
  have yRatio :
      (-yNumerator) / (-determinant) =
        yNumerator /
          Fin3.antisymmetricTripleProduct
            first.x second.x third.x first.y second.y third.y := by
    apply Ratio.ratio_eq_of_cross_product negativeDeterminantNonzero
      formulaDenominatorNonzero
    rw [antisymmetricDenominator]
    ring1
  unfold Orthocenter.Basic.orthocenterPoint
  change Intersection.lineIntersection firstAltitude secondAltitude
      (Orthocenter.Basic.triangle_altitudes_not_parallel first second third
        firstThirdDistinct secondThirdDistinct notCollinear) =
    Orthocenter.Formula.orthocenterFormula first second third
  apply Plane.Point.ext
  · unfold Intersection.lineIntersection Orthocenter.Formula.orthocenterFormula
    dsimp only
    rw [intersectionXNumerator, intersectionDenominator]
    exact xRatio
  · unfold Intersection.lineIntersection Orthocenter.Formula.orthocenterFormula
    dsimp only
    rw [intersectionYNumerator, intersectionDenominator]
    exact yRatio

end Purelib.Geometry.Triangles.Orthocenter.Formula

end

end

end
