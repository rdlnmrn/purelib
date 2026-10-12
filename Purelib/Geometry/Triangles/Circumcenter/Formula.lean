module
-- Retained public numeral and subtraction parents use their original operations.
public import Purelib.Data.Nat.Order
public import Purelib.Algebra.Group.Negation
import Purelib.Algebra.Field.Cancellation
import Purelib.Algebra.Field.Ratio
import Purelib.Algebra.Field.ExplicitField
import Purelib.Geometry.Plane.Line.Incidence
import Purelib.Geometry.Plane.Line.Intersection
import Purelib.Geometry.Plane.Line.PerpendicularBisector
import Purelib.Geometry.Plane.Point.Basic
public import Purelib.Geometry.Triangles.Circumcenter.Basic
import Purelib.LinearAlgebra.Alternating.Bracket.Fin3
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
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
# Divine Proportions, §12.2: the circumcenter formula

The source abbreviates its coordinate numerators with the six-term
antisymmetric bracket `[uv]⁻₁₂₃`.  We expose that polynomial directly and use
it to define the printed circumcenter.  The proof compares its two fractions
with the explicit intersection of two perpendicular bisectors.
-/

section

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

namespace Purelib.Geometry.Triangles.Circumcenter.Formula

/-- The numerator `[x²y]⁻ + [y²y]⁻` of the printed x-coordinate. -/
@[expose] def circumcenterXNumerator (first second third : Plane.Point K) : K :=
  Fin3.antisymmetricTripleProduct
      (first.x ^ 2) (second.x ^ 2) (third.x ^ 2)
      first.y second.y third.y +
    Fin3.antisymmetricTripleProduct
      (first.y ^ 2) (second.y ^ 2) (third.y ^ 2)
      first.y second.y third.y

/-- The numerator `[xx²]⁻ + [xy²]⁻` of the printed y-coordinate. -/
@[expose] def circumcenterYNumerator (first second third : Plane.Point K) : K :=
  Fin3.antisymmetricTripleProduct
      first.x second.x third.x
      (first.x ^ 2) (second.x ^ 2) (third.x ^ 2) +
    Fin3.antisymmetricTripleProduct
      first.x second.x third.x
      (first.y ^ 2) (second.y ^ 2) (third.y ^ 2)

/-- The circumcenter coordinates expressed by alternating triple products.

Both numerators are divided by twice the coordinate determinant; this definition alone does not assume that denominator
is nonzero. -/
@[expose] def circumcenterFormula (first second third : Plane.Point K) : Plane.Point K :=
  let denominator := 2 * Fin3.antisymmetricTripleProduct
    first.x second.x third.x first.y second.y third.y
  ⟨Geometry.Triangles.Circumcenter.Formula.circumcenterXNumerator first second third / denominator,
    Geometry.Triangles.Circumcenter.Formula.circumcenterYNumerator first second third / denominator⟩

/-- The intersection-defined circumcenter equals its alternating-product coordinate formula.

Noncollinearity and nonzero two certify the denominator cancellations. -/
theorem circumcenter_formula
    [Nontrivial K] [DecidableEq K]
    (first second third : Plane.Point K)
    (firstThirdDistinct : first ≠ third)
    (secondThirdDistinct : second ≠ third)
    (notCollinear : ¬ Incidence.Collinear first second third)
    (twoNonzero : (2 : K) ≠ 0) :
    Circumcenter.Basic.circumcenterPoint first second third firstThirdDistinct
        secondThirdDistinct notCollinear =
      Circumcenter.Formula.circumcenterFormula first second third := by
  let determinant := Incidence.pointDeterminant first second third
  let xNumerator := Geometry.Triangles.Circumcenter.Formula.circumcenterXNumerator first second third
  let yNumerator := Geometry.Triangles.Circumcenter.Formula.circumcenterYNumerator first second third
  let firstBisector := PerpendicularBisector.perpendicularBisector second third secondThirdDistinct
  let secondBisector := PerpendicularBisector.perpendicularBisector first third firstThirdDistinct
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
      2 * Fin3.antisymmetricTripleProduct
          first.x second.x third.x first.y second.y third.y ≠ 0 := by
    rw [antisymmetricDenominator]
    exact Algebra.Field.ExplicitField.mul_ne_zero twoNonzero determinantNonzero
  have twoCancel : (2 : K) * (2 : K)⁻¹ = 1 :=
    Algebra.Field.ExplicitField.mul_inv_cancel 2 twoNonzero
  have intersectionDenominator :
      firstBisector.a * secondBisector.b -
          secondBisector.a * firstBisector.b = -determinant := by
    unfold firstBisector secondBisector PerpendicularBisector.perpendicularBisector determinant
      Incidence.pointDeterminant
    ring1
  have intersectionXNumerator :
      firstBisector.b * secondBisector.c -
          secondBisector.b * firstBisector.c = -xNumerator / 2 := by
    unfold firstBisector secondBisector PerpendicularBisector.perpendicularBisector xNumerator
      Geometry.Triangles.Circumcenter.Formula.circumcenterXNumerator Fin3.antisymmetricTripleProduct
    simp only [Algebra.Field.ExplicitField.div_eq_mul_inv]
    ring1
  have intersectionYNumerator :
      firstBisector.c * secondBisector.a -
          secondBisector.c * firstBisector.a = -yNumerator / 2 := by
    unfold firstBisector secondBisector PerpendicularBisector.perpendicularBisector yNumerator
      Geometry.Triangles.Circumcenter.Formula.circumcenterYNumerator Fin3.antisymmetricTripleProduct
    simp only [Algebra.Field.ExplicitField.div_eq_mul_inv]
    ring1
  have xRatio :
      (-xNumerator / 2) / (-determinant) =
        xNumerator /
          (2 * Fin3.antisymmetricTripleProduct
            first.x second.x third.x first.y second.y third.y) := by
    apply Ratio.ratio_eq_of_cross_product negativeDeterminantNonzero
      formulaDenominatorNonzero
    rw [antisymmetricDenominator]
    simp only [Algebra.Field.ExplicitField.div_eq_mul_inv]
    calc
      (-xNumerator * (2 : K)⁻¹) * (2 * determinant) =
          -xNumerator * ((2 : K) * (2 : K)⁻¹) * determinant := by ring1
      _ = xNumerator * -determinant := by rw [twoCancel]; ring1
  have yRatio :
      (-yNumerator / 2) / (-determinant) =
        yNumerator /
          (2 * Fin3.antisymmetricTripleProduct
            first.x second.x third.x first.y second.y third.y) := by
    apply Ratio.ratio_eq_of_cross_product negativeDeterminantNonzero
      formulaDenominatorNonzero
    rw [antisymmetricDenominator]
    simp only [Algebra.Field.ExplicitField.div_eq_mul_inv]
    calc
      (-yNumerator * (2 : K)⁻¹) * (2 * determinant) =
          -yNumerator * ((2 : K) * (2 : K)⁻¹) * determinant := by ring1
      _ = yNumerator * -determinant := by rw [twoCancel]; ring1
  unfold Circumcenter.Basic.circumcenterPoint
  change Intersection.lineIntersection firstBisector secondBisector
      (Circumcenter.Basic.circumcenter_bisectors_not_parallel first second third
        firstThirdDistinct secondThirdDistinct notCollinear) =
    Circumcenter.Formula.circumcenterFormula first second third
  apply Plane.Point.ext
  · unfold Intersection.lineIntersection Circumcenter.Formula.circumcenterFormula
    dsimp only
    rw [intersectionXNumerator, intersectionDenominator]
    exact xRatio
  · unfold Intersection.lineIntersection Circumcenter.Formula.circumcenterFormula
    dsimp only
    rw [intersectionYNumerator, intersectionDenominator]
    exact yRatio

end Purelib.Geometry.Triangles.Circumcenter.Formula

end

end

end
