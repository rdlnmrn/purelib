import mathlib.Tactic.QuotientFreeRing
import DivineProportions.Isometries.Basic

/-!
# Divine Proportions, Theorem 92: specifying an isometry

The proof is the source's three finite quadrance equations.  Subtracting the
equations at the origin and the two coordinate points recovers twice each
coordinate; the explicit inverse of two then cancels that factor.
-/

namespace DivineProportions

variable {K : Type*} [RFAP.ExplicitField K]

/-- The reference point `I₁ ≡ [1,0]`. -/
def firstAxisPoint : Point K := ⟨1, 0⟩

/-- The reference point `I₂ ≡ [0,1]`. -/
def secondAxisPoint : Point K := ⟨0, 1⟩

private theorem eq_of_two_mul_eq_two_mul (left right : K)
    (twoNonzero : (2 : K) ≠ 0)
    (equalDoubles : (2 : K) * left = 2 * right) : left = right := by
  have twoCancel : (2 : K) * (2 : K)⁻¹ = 1 :=
    RFAP.ExplicitField.mul_inv_cancel 2 twoNonzero
  calc
    left = 1 * left := by ring1
    _ = (2 * (2 : K)⁻¹) * left := by rw [twoCancel]
    _ = (2 : K)⁻¹ * (2 * left) := by ring1
    _ = (2 : K)⁻¹ * (2 * right) := by rw [equalDoubles]
    _ = (2 * (2 : K)⁻¹) * right := by ring1
    _ = right := by rw [twoCancel]; ring1

namespace PlaneIsometry

/-- The coordinate rigidity calculation in the proof of Theorem 92: an
isometry fixing `O`, `I₁`, and `I₂` fixes every displayed point. -/
theorem fixingReferencePoints_eq_identity
    (isometry : PlaneIsometry K) (twoNonzero : (2 : K) ≠ 0)
    (fixesOrigin : isometry planeOrigin = planeOrigin)
    (fixesFirstAxis : isometry firstAxisPoint = firstAxisPoint)
    (fixesSecondAxis : isometry secondAxisPoint = secondAxisPoint)
    (point : Point K) : isometry point = point := by
  have originQuadrance :
      quadrance (isometry point) planeOrigin = quadrance point planeOrigin := by
    calc
      quadrance (isometry point) planeOrigin =
          quadrance (isometry point) (isometry planeOrigin) := by
            rw [fixesOrigin]
      _ = quadrance point planeOrigin :=
        isometry.preservesQuadrance point planeOrigin
  have firstAxisQuadrance :
      quadrance (isometry point) firstAxisPoint =
        quadrance point firstAxisPoint := by
    calc
      quadrance (isometry point) firstAxisPoint =
          quadrance (isometry point) (isometry firstAxisPoint) := by
            rw [fixesFirstAxis]
      _ = quadrance point firstAxisPoint :=
        isometry.preservesQuadrance point firstAxisPoint
  have secondAxisQuadrance :
      quadrance (isometry point) secondAxisPoint =
        quadrance point secondAxisPoint := by
    calc
      quadrance (isometry point) secondAxisPoint =
          quadrance (isometry point) (isometry secondAxisPoint) := by
            rw [fixesSecondAxis]
      _ = quadrance point secondAxisPoint :=
        isometry.preservesQuadrance point secondAxisPoint
  have equalXDouble : (2 : K) * (isometry point).x = 2 * point.x := by
    calc
      (2 : K) * (isometry point).x =
          quadrance (isometry point) planeOrigin -
            quadrance (isometry point) firstAxisPoint + 1 := by
              unfold quadrance planeOrigin firstAxisPoint
              ring1
      _ = quadrance point planeOrigin - quadrance point firstAxisPoint + 1 := by
        rw [originQuadrance, firstAxisQuadrance]
      _ = 2 * point.x := by
        unfold quadrance planeOrigin firstAxisPoint
        ring1
  have equalYDouble : (2 : K) * (isometry point).y = 2 * point.y := by
    calc
      (2 : K) * (isometry point).y =
          quadrance (isometry point) planeOrigin -
            quadrance (isometry point) secondAxisPoint + 1 := by
              unfold quadrance planeOrigin secondAxisPoint
              ring1
      _ = quadrance point planeOrigin - quadrance point secondAxisPoint + 1 := by
        rw [originQuadrance, secondAxisQuadrance]
      _ = 2 * point.y := by
        unfold quadrance planeOrigin secondAxisPoint
        ring1
  apply Point.ext
  · exact eq_of_two_mul_eq_two_mul
      (isometry point).x point.x twoNonzero equalXDouble
  · exact eq_of_two_mul_eq_two_mul
      (isometry point).y point.y twoNonzero equalYDouble

/-- Theorem 92 (Specifying isometries): two isometries agreeing on `O`, `I₁`,
and `I₂` agree on every point.  Equality is stated pointwise so the result
records exactly the observable transformation without equating stored inverse
proof data. -/
theorem specifiedByReferencePoints
    (first second : PlaneIsometry K) (twoNonzero : (2 : K) ≠ 0)
    (sameOrigin : first planeOrigin = second planeOrigin)
    (sameFirstAxis : first firstAxisPoint = second firstAxisPoint)
    (sameSecondAxis : first secondAxisPoint = second secondAxisPoint)
    (point : Point K) : first point = second point := by
  let comparison := second.inverse.comp first
  have comparisonFixesOrigin : comparison planeOrigin = planeOrigin := by
    unfold comparison PlaneIsometry.comp PlaneIsometry.inverse
    change second.inverseFun (first planeOrigin) = planeOrigin
    rw [sameOrigin, second.inverse_after]
  have comparisonFixesFirstAxis :
      comparison firstAxisPoint = firstAxisPoint := by
    unfold comparison PlaneIsometry.comp PlaneIsometry.inverse
    change second.inverseFun (first firstAxisPoint) = firstAxisPoint
    rw [sameFirstAxis, second.inverse_after]
  have comparisonFixesSecondAxis :
      comparison secondAxisPoint = secondAxisPoint := by
    unfold comparison PlaneIsometry.comp PlaneIsometry.inverse
    change second.inverseFun (first secondAxisPoint) = secondAxisPoint
    rw [sameSecondAxis, second.inverse_after]
  have comparisonFixesPoint : comparison point = point :=
    comparison.fixingReferencePoints_eq_identity twoNonzero
      comparisonFixesOrigin comparisonFixesFirstAxis comparisonFixesSecondAxis point
  have afterSecond := congrArg second comparisonFixesPoint
  calc
    first point = second (comparison point) := by
      unfold comparison PlaneIsometry.comp PlaneIsometry.inverse
      change first point = second (second.inverseFun (first point))
      rw [second.after_inverse]
    _ = second point := afterSecond

end PlaneIsometry

end DivineProportions
