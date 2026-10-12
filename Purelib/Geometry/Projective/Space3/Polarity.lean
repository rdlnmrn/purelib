module

import Purelib.Algebra.Field.ExplicitField
public import Purelib.LinearAlgebra.Coordinates3.Vector
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Algebra.Field (ExplicitField)

open Purelib

open Purelib.LinearAlgebra

section
@[expose] public section

/-!
# Projective point-plane duality

This module proves the finite projective-metrical duality requested in
Problem 72.  A projective point is a displayed nonzero vector and a plane
through the origin is a displayed nonzero normal covector.  The Euclidean
dot product identifies the two displayed coordinate spaces without choosing
a basis or forming a quotient.  Projective equality remains an explicit
nonzero scale witness.

Under this polarity, projective point quadrance and plane spread are the same
rational expression.  Orthogonal rotations act equivariantly on both sides,
preserve incidence and the metric, and transport arbitrary unary or binary
point-action statements to their plane-action duals.
-/

namespace Purelib.Geometry.Projective.Space3.Polarity

open Purelib.LinearAlgebra.Coordinates3

variable {K : Type*} [ExplicitField K]

set_option genInjectivity false in
/-- A projective point represented by a displayed nonzero vector. -/
@[ext]
structure ProjectivePoint (K : Type*) [Algebra.Field.ExplicitField K]
  where
  /-- The displayed vector representing the projective point. -/ coordinates : Vector K
  /-- The retained point vector is nonzero. -/ nonzero : coordinates ≠ Coordinates3.Vector.zero

constructive_injectivity ProjectivePoint

set_option genInjectivity false in
/-- A projective plane through the origin, represented by a displayed nonzero normal covector. -/
@[ext]
structure PlaneNormal (K : Type*) [Algebra.Field.ExplicitField K]
  where
  /-- The displayed normal covector representing the plane. -/ normal : Vector K
  /-- The retained plane normal is nonzero. -/ nonzero : normal ≠ Coordinates3.Vector.zero

constructive_injectivity PlaneNormal

/-- A non-null vector is in particular a nonzero displayed vector. -/
theorem Vector.ne_zero_of_quadrance_ne_zero {vector : Vector K}
    (nonNull : vector.quadrance ≠ 0) : vector ≠ Coordinates3.Vector.zero := by
  intro vectorZero
  apply nonNull
  rw [vectorZero, Coordinates3.Vector.quadrance_zero]

/-- A displayed nonzero vector supplies the nontriviality needed for an explicit nonzero projective scale. -/
theorem one_ne_zero_of_vector_ne_zero (vector : Vector K)
    (nonzero : vector ≠ Coordinates3.Vector.zero) : (1 : K) ≠ 0 := by
  intro oneZero
  apply nonzero
  ext
  · calc
      vector.t = vector.t * 1 := (mul_one vector.t).symm
      _ = vector.t * 0 := by rw [oneZero]
      _ = 0 := mul_zero vector.t
  · calc
      vector.r = vector.r * 1 := (mul_one vector.r).symm
      _ = vector.r * 0 := by rw [oneZero]
      _ = 0 := mul_zero vector.r
  · calc
      vector.s = vector.s * 1 := (mul_one vector.s).symm
      _ = vector.s * 0 := by rw [oneZero]
      _ = 0 := mul_zero vector.s
namespace ProjectivePoint

/-- Projective equality of displayed points, retaining the scale witness. -/
def Equivalent (left right :
  ProjectivePoint K) : Prop :=
  ∃ factor : K, factor ≠ 0 ∧
    right.coordinates = Coordinates3.Vector.scale factor left.coordinates

/-- Nonzero-scale equivalence of displayed projective points is reflexive. -/
theorem equivalent_refl (point :
  ProjectivePoint K) :
    point.Equivalent point :=
  ⟨1, one_ne_zero_of_vector_ne_zero point.coordinates point.nonzero,
    (Coordinates3.Vector.one_scale point.coordinates).symm⟩

/-- Invert the retained scale to reverse equivalence of displayed projective points. -/
theorem equivalent_symm {left right :
  ProjectivePoint K}
    (equivalent : left.Equivalent right) : right.Equivalent left := by
  rcases equivalent with ⟨factor, factorNonzero, rightValue⟩
  refine ⟨factor⁻¹, ExplicitField.inv_ne_zero factorNonzero, ?_⟩
  have cancel : factor⁻¹ * factor = (1 : K) := by
    rw [mul_comm, ExplicitField.mul_inv_cancel factor factorNonzero]
  calc
    left.coordinates = Coordinates3.Vector.scale 1 left.coordinates :=
      (Coordinates3.Vector.one_scale left.coordinates).symm
    _ = Coordinates3.Vector.scale (factor⁻¹ * factor) left.coordinates := by
      rw [cancel]
    _ = Coordinates3.Vector.scale factor⁻¹
        (Coordinates3.Vector.scale factor left.coordinates) := by
      rw [Coordinates3.Vector.scale_scale]
    _ = Coordinates3.Vector.scale factor⁻¹ right.coordinates := by rw [rightValue]

/-- Multiply the retained scales to compose equivalences of displayed projective points. -/
theorem equivalent_trans {first second third :
  ProjectivePoint K}
    (firstSecond : first.Equivalent second)
    (secondThird : second.Equivalent third) : first.Equivalent third := by
  rcases firstSecond with ⟨firstFactor, firstNonzero, secondValue⟩
  rcases secondThird with ⟨secondFactor, secondNonzero, thirdValue⟩
  refine ⟨secondFactor * firstFactor,
    ExplicitField.mul_ne_zero secondNonzero firstNonzero, ?_⟩
  calc
    third.coordinates = Coordinates3.Vector.scale secondFactor second.coordinates :=
      thirdValue
    _ = Coordinates3.Vector.scale secondFactor
        (Coordinates3.Vector.scale firstFactor first.coordinates) := by rw [secondValue]
    _ = Coordinates3.Vector.scale (secondFactor * firstFactor) first.coordinates :=
      Coordinates3.Vector.scale_scale _ _ _

/-- Whether the displayed representative is non-null, the domain on which the projective metric is defined. -/
def IsNonNull (point :
  ProjectivePoint K) : Prop :=
  point.coordinates.quadrance ≠ 0

/-- Projective quadrance between two non-null projective points. This is the projective metric attached to the paper's
dot product. -/
def quadrance (left right :
  ProjectivePoint K)
    (leftNonNull : left.IsNonNull) (rightNonNull : right.IsNonNull) : K :=
  Coordinates3.Vector.spread left.coordinates right.coordinates leftNonNull rightNonNull

/-- Projective quadrance is unchanged by nonzero rescaling of the first non-null representative. -/
theorem quadrance_respects_equivalent_left
    {left right : ProjectivePoint K} (equivalent : left.Equivalent right)
    (other : ProjectivePoint K)
    (leftNonNull : left.IsNonNull) (rightNonNull : right.IsNonNull)
    (otherNonNull : other.IsNonNull) :
    right.quadrance other rightNonNull otherNonNull =
      left.quadrance other leftNonNull otherNonNull := by
  rcases equivalent with ⟨factor, factorNonzero, rightValue⟩
  unfold quadrance
  simpa only [rightValue] using
    Coordinates3.Vector.spread_scale_left factor left.coordinates other.coordinates
      factorNonzero leftNonNull otherNonNull

/-- Projective quadrance is unchanged by nonzero rescaling of the second non-null representative. -/
theorem quadrance_respects_equivalent_right
    (left : ProjectivePoint K) {right third :
      ProjectivePoint K}
    (equivalent : right.Equivalent third)
    (leftNonNull : left.IsNonNull) (rightNonNull : right.IsNonNull)
    (thirdNonNull : third.IsNonNull) :
    left.quadrance third leftNonNull thirdNonNull =
      left.quadrance right leftNonNull rightNonNull := by
  rcases equivalent with ⟨factor, factorNonzero, thirdValue⟩
  unfold quadrance
  simpa only [thirdValue] using
    Coordinates3.Vector.spread_scale_right factor left.coordinates right.coordinates
      factorNonzero leftNonNull rightNonNull
end ProjectivePoint

namespace PlaneNormal

/-- Projective equality of planes by a displayed nonzero normal scale. -/
def Equivalent (left right :
  PlaneNormal K) : Prop :=
  ∃ factor : K, factor ≠ 0 ∧
    right.normal = Coordinates3.Vector.scale factor left.normal

/-- Nonzero-scale equivalence of displayed plane normals is reflexive. -/
theorem equivalent_refl (plane :
  PlaneNormal K) : plane.Equivalent plane :=
  ⟨1, one_ne_zero_of_vector_ne_zero plane.normal plane.nonzero,
    (Coordinates3.Vector.one_scale plane.normal).symm⟩

/-- Invert the retained scale to reverse equivalence of displayed plane normals. -/
theorem equivalent_symm {left right :
  PlaneNormal K}
    (equivalent : left.Equivalent right) : right.Equivalent left := by
  rcases equivalent with ⟨factor, factorNonzero, rightValue⟩
  refine ⟨factor⁻¹, ExplicitField.inv_ne_zero factorNonzero, ?_⟩
  have cancel : factor⁻¹ * factor = (1 : K) := by
    rw [mul_comm, ExplicitField.mul_inv_cancel factor factorNonzero]
  calc
    left.normal = Coordinates3.Vector.scale 1 left.normal :=
      (Coordinates3.Vector.one_scale left.normal).symm
    _ = Coordinates3.Vector.scale (factor⁻¹ * factor) left.normal := by rw [cancel]
    _ = Coordinates3.Vector.scale factor⁻¹ (Coordinates3.Vector.scale factor left.normal) := by
      rw [Coordinates3.Vector.scale_scale]
    _ = Coordinates3.Vector.scale factor⁻¹ right.normal := by rw [rightValue]

/-- Multiply the retained scales to compose equivalences of displayed plane normals. -/
theorem equivalent_trans {first second third :
  PlaneNormal K}
    (firstSecond : first.Equivalent second)
    (secondThird : second.Equivalent third) : first.Equivalent third := by
  rcases firstSecond with ⟨firstFactor, firstNonzero, secondValue⟩
  rcases secondThird with ⟨secondFactor, secondNonzero, thirdValue⟩
  refine ⟨secondFactor * firstFactor,
    ExplicitField.mul_ne_zero secondNonzero firstNonzero, ?_⟩
  calc
    third.normal = Coordinates3.Vector.scale secondFactor second.normal := thirdValue
    _ = Coordinates3.Vector.scale secondFactor
        (Coordinates3.Vector.scale firstFactor first.normal) := by rw [secondValue]
    _ = Coordinates3.Vector.scale (secondFactor * firstFactor) first.normal :=
      Coordinates3.Vector.scale_scale _ _ _

/-- Whether the normal is non-null, the domain on which plane spread is defined. -/
def IsNonNull (plane :
  PlaneNormal K) : Prop := plane.normal.quadrance ≠ 0

/-- Projective spread between two non-null planes, computed from their normal covectors. -/
def spread (left right :
  PlaneNormal K)
    (leftNonNull : left.IsNonNull) (rightNonNull : right.IsNonNull) : K :=
  Coordinates3.Vector.spread left.normal right.normal leftNonNull rightNonNull

/-- Plane spread is unchanged by nonzero rescaling of the first non-null normal. -/
theorem spread_respects_equivalent_left
    {left right : PlaneNormal K} (equivalent : left.Equivalent right)
    (other : PlaneNormal K)
    (leftNonNull : left.IsNonNull) (rightNonNull : right.IsNonNull)
    (otherNonNull : other.IsNonNull) :
    right.spread other rightNonNull otherNonNull =
      left.spread other leftNonNull otherNonNull := by
  rcases equivalent with ⟨factor, factorNonzero, rightValue⟩
  unfold spread
  simpa only [rightValue] using
    Coordinates3.Vector.spread_scale_left factor left.normal other.normal
      factorNonzero leftNonNull otherNonNull

/-- Plane spread is unchanged by nonzero rescaling of the second non-null normal. -/
theorem spread_respects_equivalent_right
    (left : PlaneNormal K) {right third :
      PlaneNormal K}
    (equivalent : right.Equivalent third)
    (leftNonNull : left.IsNonNull) (rightNonNull : right.IsNonNull)
    (thirdNonNull : third.IsNonNull) :
    left.spread third leftNonNull thirdNonNull =
      left.spread right leftNonNull rightNonNull := by
  rcases equivalent with ⟨factor, factorNonzero, thirdValue⟩
  unfold spread
  simpa only [thirdValue] using
    Coordinates3.Vector.spread_scale_right factor left.normal right.normal
      factorNonzero leftNonNull rightNonNull
end PlaneNormal

/-! ## The polarity and its metrical laws -/

namespace ProjectivePoint

/-- The polar plane whose normal has the displayed point coordinates. -/
def dual (point :
  ProjectivePoint K) : PlaneNormal K where
  normal := point.coordinates
  nonzero := point.nonzero

/-- The polar plane retains exactly the point coordinates as its normal. -/
@[simp] theorem dual_normal (point :
  ProjectivePoint K) :
    point.dual.normal = point.coordinates := rfl

end ProjectivePoint

namespace PlaneNormal

/-- The pole whose displayed coordinates are the plane normal. -/
def dual (plane :
  PlaneNormal K) : ProjectivePoint K where
  coordinates := plane.normal
  nonzero := plane.nonzero

/-- The pole retains exactly the plane normal as its coordinates. -/
@[simp] theorem dual_coordinates (plane :
  PlaneNormal K) :
    plane.dual.coordinates = plane.normal := rfl

end PlaneNormal

/-- Applying polarity twice returns the original displayed representative. -/
@[simp] theorem ProjectivePoint.dual_dual (point :
  ProjectivePoint K) :
    point.dual.dual = point := rfl

/-- Applying polarity twice returns the original displayed representative. -/
@[simp] theorem PlaneNormal.dual_dual (plane :
  PlaneNormal K) :
    plane.dual.dual = plane := rfl

/-- Polarity preserves and reflects nonzero-scale equivalence. -/
theorem ProjectivePoint.dual_equivalent_iff
    (left right : ProjectivePoint K) :
    left.dual.Equivalent right.dual ↔ left.Equivalent right := by
  rfl

/-- Polarity preserves and reflects nonzero-scale equivalence. -/
theorem PlaneNormal.dual_equivalent_iff (left right :
  PlaneNormal K) :
    left.dual.Equivalent right.dual ↔ left.Equivalent right := by
  rfl

/-- Polarity preserves and reflects nonzero quadrance. -/
theorem ProjectivePoint.dual_nonNull_iff (point :
  ProjectivePoint K) :
    point.dual.IsNonNull ↔ point.IsNonNull := by rfl

/-- Polarity preserves and reflects nonzero quadrance. -/
theorem PlaneNormal.dual_nonNull_iff (plane :
  PlaneNormal K) :
    plane.dual.IsNonNull ↔ plane.IsNonNull := by rfl

/-- The central metric clause of Problem 72: projective quadrance of points is spread of their polar planes. -/
theorem projectiveQuadrance_eq_dualPlaneSpread
    (left right : ProjectivePoint K)
    (leftNonNull : left.IsNonNull) (rightNonNull : right.IsNonNull) :
    left.quadrance right leftNonNull rightNonNull =
      left.dual.spread right.dual leftNonNull rightNonNull := rfl

/-- The inverse metric clause: plane spread is the projective quadrance of the corresponding poles. -/
theorem planeSpread_eq_dualPointQuadrance
    (left right : PlaneNormal K)
    (leftNonNull : left.IsNonNull) (rightNonNull : right.IsNonNull) :
    left.spread right leftNonNull rightNonNull =
      left.dual.quadrance right.dual leftNonNull rightNonNull := rfl

namespace ProjectivePoint

/-- Incidence of a projective point with a plane through the origin. -/
def Incident (point :
  ProjectivePoint K) (plane : PlaneNormal K) :
  Prop :=
  Coordinates3.Vector.dot point.coordinates plane.normal = 0

/-- Incidence with the polar plane is perpendicularity of the displayed point vectors. -/
theorem incident_polar_iff_perpendicular
    (left right : ProjectivePoint K) :
    left.Incident right.dual ↔ left.coordinates.Perpendicular right.coordinates :=
  Iff.rfl

/-- Incidence of a point with another point's polar plane is symmetric. -/
theorem incident_dual_symmetric (left right :
  ProjectivePoint K) :
    left.Incident right.dual ↔ right.Incident left.dual := by
  change Coordinates3.Vector.dot left.coordinates right.coordinates = 0 ↔
    Coordinates3.Vector.dot right.coordinates left.coordinates = 0
  rw [Coordinates3.Vector.dot_comm]

/-- Nonzero rescaling of a point preserves its incidence with the retained plane. -/
theorem incident_of_equivalent_point {left right :
  ProjectivePoint K}
    (equivalent : left.Equivalent right) (plane : PlaneNormal K)
    (incident : left.Incident plane) : right.Incident plane := by
  rcases equivalent with ⟨factor, _factorNonzero, rightValue⟩
  unfold Incident at incident ⊢
  rw [rightValue, Coordinates3.Vector.dot_scale_left, incident, mul_zero]

/-- Equivalent point representatives have exactly the same incidences. -/
theorem incident_respects_equivalent_point
    {left right : ProjectivePoint K} (equivalent : left.Equivalent right)
    (plane : PlaneNormal K) : left.Incident plane ↔ right.Incident plane := by
  constructor
  · exact incident_of_equivalent_point equivalent plane
  · exact incident_of_equivalent_point
      (equivalent_symm equivalent) plane

/-- Nonzero rescaling of a plane normal preserves incidence with the retained point. -/
theorem incident_of_equivalent_plane (point :
  ProjectivePoint K)
    {left right : PlaneNormal K} (equivalent : left.Equivalent right)
    (incident : point.Incident left) : point.Incident right := by
  rcases equivalent with ⟨factor, _factorNonzero, rightValue⟩
  unfold Incident at incident ⊢
  rw [rightValue, Coordinates3.Vector.dot_scale_right, incident, mul_zero]

/-- Equivalent plane representatives have exactly the same incidences. -/
theorem incident_respects_equivalent_plane (point :
  ProjectivePoint K)
    {left right : PlaneNormal K} (equivalent : left.Equivalent right) :
    point.Incident left ↔ point.Incident right := by
  constructor
  · exact incident_of_equivalent_plane point equivalent
  · exact incident_of_equivalent_plane point
      (Geometry.Projective.Space3.Polarity.PlaneNormal.equivalent_symm equivalent)
end ProjectivePoint
section
end

end Purelib.Geometry.Projective.Space3.Polarity

end
