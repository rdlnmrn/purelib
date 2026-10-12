module
import Purelib.Geometry.Plane.Isometry.Basic
public import Purelib.Geometry.Plane.Isometry.Rotation
public import Purelib.Geometry.Plane.Isometry.Translation
import Purelib.Geometry.Plane.Line.Basic
import Purelib.Geometry.Plane.Point.Affine
import Purelib.Geometry.Plane.Point.Basic
import Purelib.Geometry.Plane.HalfTurn.Basic
public import Purelib.Geometry.Plane.Reflection.Point

import Purelib.Algebra.Field.ExplicitField
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Geometry.Plane.Point.Quadrance
import Purelib.Tactic.Ring

open Purelib

open Purelib.Geometry

open Purelib.Geometry.Plane

open Purelib.Geometry.Plane.Isometry

open Purelib.Geometry.Plane.Point

@[expose] public section

/-!
# Divine Proportions, Theorem 94: classification of isometries

Every isometry is split constructively into translation by its displayed image
of the origin and an isometry fixing the origin.  The factorization and its
uniqueness are pointwise finite coordinate equalities.
-/

namespace Purelib.Geometry.Plane.Isometry.Decomposition

open Purelib.Algebra

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

namespace PlaneIsometry

/-- The canonical translation factor, read directly from the image of the origin. -/
def translationComponent (isometry : Isometry.Basic.PlaneIsometry K) : Isometry.Basic.PlaneIsometry K :=
  Translation.translation (isometry Plane.Point.Basic.planeOrigin).x (isometry Plane.Point.Basic.planeOrigin).y

/-- Translate the image of the origin back to zero; this is the canonical orthogonality factor. -/
def orthogonalityComponent (isometry : Isometry.Basic.PlaneIsometry K) : Isometry.Basic.PlaneIsometry K :=
  (Translation.translation (-(isometry Plane.Point.Basic.planeOrigin).x) (-(isometry
    Plane.Point.Basic.planeOrigin).y)).comp
    isometry

/-- The canonical second factor fixes the origin. -/
theorem orthogonalityComponent_fixesOrigin (isometry : Isometry.Basic.PlaneIsometry K) :
    ((Decomposition.PlaneIsometry.orthogonalityComponent isometry)).IsOrthogonality := by
  unfold Basic.PlaneIsometry.IsOrthogonality Decomposition.PlaneIsometry.orthogonalityComponent Basic.PlaneIsometry.comp
    Translation.translation Plane.Point.Basic.planeOrigin Affine.translationPoint
  apply Point.ext <;>
    ring1

/-- The canonical factors multiply back to the original isometry. -/
theorem translation_orthogonality_decomposition
    (isometry : Isometry.Basic.PlaneIsometry K) (point : Point K) :
    isometry point =
      (Decomposition.PlaneIsometry.translationComponent isometry)
        ((Decomposition.PlaneIsometry.orthogonalityComponent isometry) point) := by
  apply Point.ext <;>
    unfold Decomposition.PlaneIsometry.translationComponent Decomposition.PlaneIsometry.orthogonalityComponent
      Basic.PlaneIsometry.comp
      Translation.translation Affine.translationPoint <;>
    ring1

/-- Any translation-orthogonality factorization has the canonical translation parameters and the canonical orthogonality
point map. -/
theorem translation_orthogonality_unique
    (isometry orthogonality : Isometry.Basic.PlaneIsometry K) (u v : K)
    (fixesOrigin : orthogonality.IsOrthogonality)
    (decomposition : ∀ point : Point K,
      isometry point = Translation.translation u v (orthogonality point)) :
    u = (isometry Plane.Point.Basic.planeOrigin).x ∧
      v = (isometry Plane.Point.Basic.planeOrigin).y ∧
      ∀ point : Point K,
        orthogonality point = (Geometry.Plane.Isometry.Decomposition.PlaneIsometry.orthogonalityComponent isometry)
          point := by
  have atOrigin := decomposition Plane.Point.Basic.planeOrigin
  have uCanonical : u = (isometry Plane.Point.Basic.planeOrigin).x := by
    have xEquality := congrArg Point.x atOrigin
    unfold Basic.PlaneIsometry.IsOrthogonality at fixesOrigin
    rw [fixesOrigin] at xEquality
    simpa [Translation.translation, Affine.translationPoint, Plane.Point.Basic.planeOrigin] using xEquality.symm
  have vCanonical : v = (isometry Plane.Point.Basic.planeOrigin).y := by
    have yEquality := congrArg Point.y atOrigin
    unfold Basic.PlaneIsometry.IsOrthogonality at fixesOrigin
    rw [fixesOrigin] at yEquality
    simpa [Translation.translation, Affine.translationPoint, Plane.Point.Basic.planeOrigin] using yEquality.symm
  refine ⟨uCanonical, vCanonical, ?_⟩
  intro point
  have atPoint := decomposition point
  apply Point.ext
  · have xEquality := congrArg Point.x atPoint
    change
      (orthogonality point).x =
        (isometry point).x + -(isometry Plane.Point.Basic.planeOrigin).x
    change
      (isometry point).x = (orthogonality point).x + u
      at xEquality
    calc
      (orthogonality point).x = (isometry point).x - u := by
        rw [xEquality]
        ring1
      _ = (isometry point).x + -(isometry Plane.Point.Basic.planeOrigin).x := by
        rw [uCanonical]
        ring1
  · have yEquality := congrArg Point.y atPoint
    change
      (orthogonality point).y =
        (isometry point).y + -(isometry Plane.Point.Basic.planeOrigin).y
    change
      (isometry point).y = (orthogonality point).y + v
      at yEquality
    calc
      (orthogonality point).y = (isometry point).y - v := by
        rw [yEquality]
        ring1
      _ = (isometry point).y + -(isometry Plane.Point.Basic.planeOrigin).y := by
        rw [vCanonical]
        ring1

/-- Theorem 94 (Classification of isometries): existence and uniqueness of the translation-orthogonality factorization.
Equality of stored isometries is expressed pointwise, avoiding irrelevant equality of inverse proof fields. -/
theorem isometryClassification (isometry : Isometry.Basic.PlaneIsometry K) :
    ∃ u v : K, ∃ orthogonality : Isometry.Basic.PlaneIsometry K,
      orthogonality.IsOrthogonality ∧
      (∀ point : Point K,
        isometry point = Translation.translation u v (orthogonality point)) ∧
      ∀ u' v' : K, ∀ orthogonality' : Isometry.Basic.PlaneIsometry K,
        orthogonality'.IsOrthogonality →
        (∀ point : Point K,
          isometry point = Translation.translation u' v' (orthogonality' point)) →
        u' = u ∧ v' = v ∧
          ∀ point : Point K, orthogonality' point = orthogonality point := by
  let u := (isometry Plane.Point.Basic.planeOrigin).x
  let v := (isometry Plane.Point.Basic.planeOrigin).y
  let orthogonality := (Geometry.Plane.Isometry.Decomposition.PlaneIsometry.orthogonalityComponent isometry)
  refine ⟨u, v, orthogonality,
    (Geometry.Plane.Isometry.Decomposition.PlaneIsometry.orthogonalityComponent_fixesOrigin isometry), ?_, ?_⟩
  · intro point
    exact (Geometry.Plane.Isometry.Decomposition.PlaneIsometry.translation_orthogonality_decomposition isometry) point
  · intro u' v' orthogonality' fixesOrigin decomposition
    have unique := (Geometry.Plane.Isometry.Decomposition.PlaneIsometry.translation_orthogonality_unique isometry)
      orthogonality' u' v' fixesOrigin decomposition
    exact ⟨unique.1, unique.2.1, unique.2.2⟩

end PlaneIsometry

/-- Exercise 13.6: rotation in the origin is the central rotation with unit parameters `[-1,0]`. -/
theorem rotationInOrigin_eq_centralRotationPoint (point : Point K) :
    HalfTurn.Basic.rotateInPoint Basic.planeOrigin point = Rotation.centralRotationPoint (-1) 0 point := by
  apply Point.ext <;>
    unfold HalfTurn.Basic.rotateInPoint Basic.planeOrigin Rotation.centralRotationPoint <;>
    ring1

/-- Exercise 13.6: rotation in an arbitrary point is rotation in the origin followed by translation by the image of the
origin. -/
theorem rotationInPoint_decomposition (center point : Point K) :
    HalfTurn.Basic.rotateInPoint center point =
      Affine.translationPoint
        (HalfTurn.Basic.rotateInPoint center Basic.planeOrigin).x
        (HalfTurn.Basic.rotateInPoint center Basic.planeOrigin).y
        (HalfTurn.Basic.rotateInPoint Basic.planeOrigin point) := by
  apply Point.ext <;>
    unfold HalfTurn.Basic.rotateInPoint Basic.planeOrigin Affine.translationPoint <;>
    ring1

/-- Replace the constant term of a line by zero, producing the central line `k ≡ ⟨a:b:0⟩` from Exercise 13.7. -/
def centralLine (line : Line K) : Line K where
  a := line.a
  b := line.b
  c := 0
  direction_nonzero := line.direction_nonzero

/-- Centralizing a line preserves its non-null direction pair. -/
theorem centralLine_nonNull (line : Line K) (nonNull : ¬ line.IsNull) :
    ¬ (Geometry.Plane.Isometry.Decomposition.centralLine line).IsNull := by
  intro centralNull
  apply nonNull
  exact centralNull

/-- The translation point `B = σ_l(O)` displayed in Exercise 13.7. -/
def reflectionTranslationPoint (line : Line K) : Point K :=
  ⟨(-2 * line.a * line.c) / Line.Basic.lineNorm line,
    (-2 * line.b * line.c) / Line.Basic.lineNorm line⟩

/-- Exercise 13.7: the printed formula for reflection in the associated central line `k ≡ ⟨a:b:0⟩`. -/
theorem centralLine_reflection_formula (line : Line K)
    (nonNull : ¬ line.IsNull) (point : Point K) :
    Reflection.Point.reflectPoint (Geometry.Plane.Isometry.Decomposition.centralLine line)
      (Geometry.Plane.Isometry.Decomposition.centralLine_nonNull line nonNull) point =
      ⟨(((line.b ^ 2 - line.a ^ 2) * point.x -
          2 * line.a * line.b * point.y) / Line.Basic.lineNorm line),
        ((-2 * line.a * line.b * point.x +
          (line.a ^ 2 - line.b ^ 2) * point.y) / Line.Basic.lineNorm line)⟩ := by
  rw [Reflection.Point.reflectPoint_formula]
  have zeroDifference (amount : K) : amount - 0 = amount := by ring1
  apply Point.ext <;>
    simp only [Reflection.Point.reflectionFormula, Geometry.Plane.Isometry.Decomposition.centralLine,
      Line.Basic.lineNorm, mul_zero, zeroDifference, -eq_self, -iff_self] <;> rfl

/-- Exercise 13.7: reflection in `l` is reflection in its associated central line followed by translation by `B =
σ_l(O)`. -/
theorem lineReflection_decomposition (line : Line K)
    (nonNull : ¬ line.IsNull) (point : Point K) :
    Reflection.Point.reflectPoint line nonNull point =
      Affine.translationPoint
        (Geometry.Plane.Isometry.Decomposition.reflectionTranslationPoint line).x
        (Geometry.Plane.Isometry.Decomposition.reflectionTranslationPoint line).y
        (Reflection.Point.reflectPoint (Geometry.Plane.Isometry.Decomposition.centralLine line)
          (Geometry.Plane.Isometry.Decomposition.centralLine_nonNull line nonNull) point) := by
  rw [Reflection.Point.reflectPoint_formula, Reflection.Point.reflectPoint_formula]
  apply Point.ext <;>
    simp only [Reflection.Point.reflectionFormula, Geometry.Plane.Isometry.Decomposition.reflectionTranslationPoint,
      Affine.translationPoint,
      Geometry.Plane.Isometry.Decomposition.centralLine, Line.Basic.lineNorm] <;>
    simp only [Algebra.Field.ExplicitField.div_eq_mul_inv] <;>
    ring1

end Purelib.Geometry.Plane.Isometry.Decomposition
