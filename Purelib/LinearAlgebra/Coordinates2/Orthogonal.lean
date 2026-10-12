module

public import Purelib.Algebra.Field.ExplicitField
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Ring.Defs
import Purelib.Tactic.Ring

open Purelib.Algebra.Field

section
/-!
# Divine Proportions, §13.1: translations, rotations, and reflections

This file gives executable isometries for the coordinate transformations in
Examples 13.1–13.3 and proves the composition calculations requested in
Exercises 13.2, 13.4, and 13.5.
-/

@[expose] public section

namespace Purelib.LinearAlgebra.Coordinates2.Orthogonal

variable {K : Type*} [ExplicitField K]

/-- The output parameters for a composition of two central reflections are
again a unit pair. -/
theorem centralReflectionComposition_unit
    (q r t u : K) (firstUnit : q ^ 2 + r ^ 2 = 1)
    (secondUnit : t ^ 2 + u ^ 2 = 1) :
    (q * t + r * u) ^ 2 + (q * u - r * t) ^ 2 = 1 := by
  calc
    (q * t + r * u) ^ 2 + (q * u - r * t) ^ 2 =
        (q ^ 2 + r ^ 2) * (t ^ 2 + u ^ 2) := by ring1
    _ = 1 := by rw [firstUnit, secondUnit]; ring1

/-- The output parameters for a composition of central rotations are again a
unit pair. -/
theorem centralRotationComposition_unit
    (q r t u : K) (firstUnit : q ^ 2 + r ^ 2 = 1)
    (secondUnit : t ^ 2 + u ^ 2 = 1) :
    (q * t - r * u) ^ 2 + (q * u + r * t) ^ 2 = 1 := by
  calc
    (q * t - r * u) ^ 2 + (q * u + r * t) ^ 2 =
        (q ^ 2 + r ^ 2) * (t ^ 2 + u ^ 2) := by ring1
    _ = 1 := by rw [firstUnit, secondUnit]; ring1
end Purelib.LinearAlgebra.Coordinates2.Orthogonal

end

end

section
section
@[expose] public section

/-!
# Divine Proportions, Theorem 93: orthogonalities

An orthogonality is determined by the images of the two coordinate points.
The first is a unit pair `[q,r]`; finite coordinate algebra shows the second
is exactly one of `[r,-q]` and `[-r,q]`.  Theorem 92 then identifies the whole
map with the corresponding central reflection or central rotation.
-/

namespace Purelib.LinearAlgebra.Coordinates2.Orthogonal

variable {K : Type*} [ExplicitField K]

attribute [local instance high] SubNegMonoid.toNeg in
/-- A second unit pair perpendicular to `[q,r]` has one of the two displayed
orientations.  The sign is selected by decidable equality, not by choice. -/
theorem perpendicularUnitPair_orientations [Nontrivial K]
  [DecidableEq K]
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
          ((ExplicitField.mul_ne_zero
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
end PlaneIsometry

end Purelib.LinearAlgebra.Coordinates2.Orthogonal

end

end
