import mathlib.Tactic.QuotientFreeRing
import DivineProportions.Isometries.Models
import DivineProportions.Isometries.Specification

/-!
# Divine Proportions, Theorem 93: orthogonalities

An orthogonality is determined by the images of the two coordinate points.
The first is a unit pair `[q,r]`; finite coordinate algebra shows the second
is exactly one of `[r,-q]` and `[-r,q]`.  Theorem 92 then identifies the whole
map with the corresponding central reflection or central rotation.
-/

namespace DivineProportions

variable {K : Type*} [RFAP.ExplicitField K]

/-- A second unit pair perpendicular to `[q,r]` has one of the two displayed
orientations.  The sign is selected by decidable equality, not by choice. -/
theorem perpendicularUnitPair_orientations [Nontrivial K] [DecidableEq K]
    (q r s t : K) (firstUnit : q ^ 2 + r ^ 2 = 1)
    (secondUnit : s ^ 2 + t ^ 2 = 1)
    (perpendicular : q * s + r * t = 0) :
    (s = r ∧ t = -q) ∨ (s = -r ∧ t = q) := by
  let scale := r * s - q * t
  have sFormula : s = r * scale := by
    calc
      s = (q ^ 2 + r ^ 2) * s := by rw [firstUnit]; ring1
      _ = r * (r * s - q * t) + q * (q * s + r * t) := by ring1
      _ = r * scale := by rw [perpendicular]; unfold scale; ring1
  have tFormula : t = -q * scale := by
    calc
      t = (q ^ 2 + r ^ 2) * t := by rw [firstUnit]; ring1
      _ = -q * (r * s - q * t) + r * (q * s + r * t) := by ring1
      _ = -q * scale := by rw [perpendicular]; unfold scale; ring1
  have scaleSquare : scale ^ 2 = 1 := by
    calc
      scale ^ 2 =
          (q ^ 2 + r ^ 2) * (s ^ 2 + t ^ 2) -
            (q * s + r * t) ^ 2 := by unfold scale; ring1
      _ = 1 := by rw [firstUnit, secondUnit, perpendicular]; ring1
  have factoredZero : (scale - 1) * (scale + 1) = 0 := by
    calc
      (scale - 1) * (scale + 1) = scale ^ 2 - 1 := by ring1
      _ = 0 := by rw [scaleSquare]; ring1
  by_cases scaleOne : scale = 1
  · left
    constructor
    · calc
        s = r * scale := sFormula
        _ = r := by rw [scaleOne]; ring1
    · calc
        t = -q * scale := tFormula
        _ = -q := by rw [scaleOne]; ring1
  · have scaleMinusOneNonzero : scale - 1 ≠ 0 := by
      intro differenceZero
      apply scaleOne
      calc
        scale = (scale - 1) + 1 := by ring1
        _ = 1 := by rw [differenceZero]; ring1
    have scalePlusOneZero : scale + 1 = 0 := by
      by_cases equalZero : scale + 1 = 0
      · exact equalZero
      · exact False.elim
          ((RFAP.ExplicitField.mul_ne_zero
            scaleMinusOneNonzero equalZero) factoredZero)
    have scaleNegOne : scale = -1 := by
      calc
        scale = (scale + 1) - 1 := by ring1
        _ = -1 := by rw [scalePlusOneZero]; ring1
    right
    constructor
    · calc
        s = r * scale := sFormula
        _ = -r := by rw [scaleNegOne]; ring1
    · calc
        t = -q * scale := tFormula
        _ = q := by rw [scaleNegOne]; ring1

namespace PlaneIsometry

/-- Theorem 93 (Orthogonality): every isometry fixing the origin is pointwise
either a central rotation or a central reflection. -/
theorem orthogonalityClassification [Nontrivial K] [DecidableEq K]
    (isometry : PlaneIsometry K) (twoNonzero : (2 : K) ≠ 0)
    (fixesOrigin : isometry.IsOrthogonality) :
    ∃ q r : K, ∃ unit : q ^ 2 + r ^ 2 = 1,
      (∀ point : Point K,
          isometry point = centralRotation q r unit point) ∨
        (∀ point : Point K,
          isometry point = centralReflection q r unit point) := by
  let firstImage := isometry firstAxisPoint
  let secondImage := isometry secondAxisPoint
  let q := firstImage.x
  let r := firstImage.y
  let s := secondImage.x
  let t := secondImage.y
  have firstUnit : q ^ 2 + r ^ 2 = 1 := by
    have preserved := isometry.preservesQuadrance planeOrigin firstAxisPoint
    rw [fixesOrigin] at preserved
    change q ^ 2 + r ^ 2 = 1
    simpa [firstImage, q, r, quadrance, planeOrigin, firstAxisPoint] using
      preserved
  have secondUnit : s ^ 2 + t ^ 2 = 1 := by
    have preserved := isometry.preservesQuadrance planeOrigin secondAxisPoint
    rw [fixesOrigin] at preserved
    change s ^ 2 + t ^ 2 = 1
    simpa [secondImage, s, t, quadrance, planeOrigin, secondAxisPoint] using
      preserved
  have imageDistance :
      quadrance firstImage secondImage = (2 : K) := by
    have preserved :=
      isometry.preservesQuadrance firstAxisPoint secondAxisPoint
    change quadrance firstImage secondImage = quadrance firstAxisPoint secondAxisPoint
      at preserved
    calc
      quadrance firstImage secondImage =
          quadrance firstAxisPoint secondAxisPoint := preserved
      _ = 2 := by unfold quadrance firstAxisPoint secondAxisPoint; ring1
  have twiceDotZero : (2 : K) * (q * s + r * t) = 0 := by
    calc
      (2 : K) * (q * s + r * t) =
          (q ^ 2 + r ^ 2) + (s ^ 2 + t ^ 2) -
            quadrance firstImage secondImage := by
              unfold quadrance q r s t firstImage secondImage
              ring1
      _ = 0 := by rw [firstUnit, secondUnit, imageDistance]; ring1
  have twoCancel : (2 : K) * (2 : K)⁻¹ = 1 :=
    RFAP.ExplicitField.mul_inv_cancel 2 twoNonzero
  have perpendicular : q * s + r * t = 0 := by
    calc
      q * s + r * t = 1 * (q * s + r * t) := by ring1
      _ = (2 * (2 : K)⁻¹) * (q * s + r * t) := by rw [twoCancel]
      _ = (2 : K)⁻¹ * (2 * (q * s + r * t)) := by ring1
      _ = 0 := by rw [twiceDotZero]; ring1
  refine ⟨q, r, firstUnit, ?_⟩
  rcases perpendicularUnitPair_orientations q r s t
      firstUnit secondUnit perpendicular with
    reflectionOrientation | rotationOrientation
  · right
    intro point
    apply isometry.specifiedByReferencePoints
      (centralReflection q r firstUnit) twoNonzero
    · calc
        isometry planeOrigin = planeOrigin := fixesOrigin
        _ = centralReflection q r firstUnit planeOrigin :=
          (centralReflection_orthogonality q r firstUnit).symm
    · apply Point.ext <;>
        simp only [firstImage, q, r, firstAxisPoint,
          centralReflection, centralReflectionPoint] <;>
        ring1
    · apply Point.ext
      · simpa [s, secondImage, secondAxisPoint, centralReflection,
          centralReflectionPoint] using reflectionOrientation.1
      · simpa [t, secondImage, secondAxisPoint, centralReflection,
          centralReflectionPoint] using reflectionOrientation.2
  · left
    intro point
    apply isometry.specifiedByReferencePoints
      (centralRotation q r firstUnit) twoNonzero
    · calc
        isometry planeOrigin = planeOrigin := fixesOrigin
        _ = centralRotation q r firstUnit planeOrigin :=
          (centralRotation_orthogonality q r firstUnit).symm
    · apply Point.ext <;>
        simp only [firstImage, q, r, firstAxisPoint,
          centralRotation, centralRotationPoint] <;>
        ring1
    · apply Point.ext
      · simpa [s, secondImage, secondAxisPoint, centralRotation,
          centralRotationPoint] using rotationOrientation.1
      · simpa [t, secondImage, secondAxisPoint, centralRotation,
          centralRotationPoint] using rotationOrientation.2

end PlaneIsometry

end DivineProportions
