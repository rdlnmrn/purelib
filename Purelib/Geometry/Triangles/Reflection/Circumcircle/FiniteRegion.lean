module
import Purelib.Data.List.Filter
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Geometry.Circles.Concyclic.Determinant
import Purelib.Geometry.Plane.Line.Incidence
import Purelib.Geometry.Plane.Point.Basic
public import Purelib.Geometry.Plane.Reflection.Point
import Init.Prelude
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Purelib.Geometry.Plane.Line.Basic

open Purelib

open Purelib.Geometry

open Purelib.Geometry.Plane

open Purelib.Geometry.Plane.Line

open Purelib.Geometry.Quadrilaterals.Basic

section
@[expose] public section

/-!
# Divine Proportions, Chapter 25: resection and Hansen's problem

The large rational calculations are represented by common-denominator
integer certificates.  The general resection theorem is proved from the
denominator-free Four-point polynomial, so neither a root search nor a
completed coordinate field is used.
-/

namespace Purelib.Geometry.Triangles.Reflection.Circumcircle.FiniteRegion

section ResectionApplications

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-! ## The reflected-circle correspondence after Example 25.1 -/

set_option genInjectivity false in
/-- The finite data needed to construct the three reflections in the sides of a non-null reference triangle. -/
structure ReflectionTriangleData (K : Type*)
  [Algebra.Field.ExplicitField K]
    [DecidableEq K] where
  /-- The first reference vertex. -/ first : Plane.Point K
  /-- The second reference vertex. -/ second : Plane.Point K
  /-- The third reference vertex. -/ third : Plane.Point K
  /-- The point reflected in each reference side. -/ base : Plane.Point K
  /-- The first two vertices are distinct. -/ firstSecondDistinct : first ≠ second
  /-- The first and third vertices are distinct. -/ firstThirdDistinct : first ≠ third
  /-- The last two vertices are distinct. -/ secondThirdDistinct : second ≠ third
  /-- The line through the first two vertices is non-null. -/ firstSecondNonNull :
    ¬ (Incidence.lineThrough first second firstSecondDistinct).IsNull
  /-- The line through the first and third vertices is non-null. -/ firstThirdNonNull :
    ¬ (Incidence.lineThrough first third firstThirdDistinct).IsNull
  /-- The line through the last two vertices is non-null. -/ secondThirdNonNull :
    ¬ (Incidence.lineThrough second third secondThirdDistinct).IsNull

constructive_injectivity ReflectionTriangleData

section ReflectionTriangleData

/-- Reflect the retained base point in the side joining the second and third vertices. -/
def ReflectionTriangleData.reflectedInSecondThird
  [DecidableEq K]
    (data : Geometry.Triangles.Reflection.Circumcircle.FiniteRegion.ReflectionTriangleData K) : Plane.Point
      K :=
  Reflection.Point.reflectPoint
    (Incidence.lineThrough data.second data.third data.secondThirdDistinct)
    data.secondThirdNonNull data.base

/-- Reflect the retained base point in the side joining the first and third vertices. -/
def ReflectionTriangleData.reflectedInFirstThird
  [DecidableEq K]
    (data : Geometry.Triangles.Reflection.Circumcircle.FiniteRegion.ReflectionTriangleData K) : Plane.Point
      K :=
  Reflection.Point.reflectPoint
    (Incidence.lineThrough data.first data.third data.firstThirdDistinct)
    data.firstThirdNonNull data.base

/-- Reflect the retained base point in the side joining the first and second vertices. -/
def ReflectionTriangleData.reflectedInFirstSecond
  [DecidableEq K]
    (data : Geometry.Triangles.Reflection.Circumcircle.FiniteRegion.ReflectionTriangleData K) : Plane.Point
      K :=
  Reflection.Point.reflectPoint
    (Incidence.lineThrough data.first data.second data.firstSecondDistinct)
    data.firstSecondNonNull data.base

/-- A candidate lies on all three reflected circumcircles in the exact determinant sense used by Theorem 109. -/
def
  ReflectionTriangleData.IsCommonReflectedCirclePoint
  [DecidableEq K]
    (data : Geometry.Triangles.Reflection.Circumcircle.FiniteRegion.ReflectionTriangleData K) (candidate :
      Plane.Point K) : Prop :=
  Quadrilateral.coordinateCircleDeterminant
      data.second data.third data.reflectedInSecondThird candidate = 0 ∧
    Quadrilateral.coordinateCircleDeterminant
      data.first data.third data.reflectedInFirstThird candidate = 0 ∧
    Quadrilateral.coordinateCircleDeterminant
      data.first data.second data.reflectedInFirstSecond candidate = 0

/-- Decide the three circle-determinant equalities using the supplied field equality decision. -/
instance
  ReflectionTriangleData.isCommonReflectedCirclePointDecidable
  [DecidableEq K]
    (data : Geometry.Triangles.Reflection.Circumcircle.FiniteRegion.ReflectionTriangleData K) (candidate :
      Plane.Point K) :
    Decidable (data.IsCommonReflectedCirclePoint candidate) := by
  unfold
    Purelib.Geometry.Triangles.Reflection.Circumcircle.FiniteRegion.ReflectionTriangleData.IsCommonReflectedCirclePoint
  infer_instance

/-- The constructive finite version of the common-point construction cited after Example 25.1: inspect an explicit
finite region and retain precisely the common reflected-circle points. -/
def
  ReflectionTriangleData.commonReflectedCirclePoints
  [DecidableEq K]
    (data : Geometry.Triangles.Reflection.Circumcircle.FiniteRegion.ReflectionTriangleData K) (candidates : List
      (Plane.Point K)) :
    List (Plane.Point K) :=
  candidates.filter fun candidate => decide
    (data.IsCommonReflectedCirclePoint candidate)

open Purelib.Data in
/-- Membership in the filtered list is exactly membership in the candidate region together with all three circle
incidences. -/
theorem
  ReflectionTriangleData.memCommonReflectedCirclePoints
  [DecidableEq K]
    (data : Geometry.Triangles.Reflection.Circumcircle.FiniteRegion.ReflectionTriangleData K) (candidates : List
      (Plane.Point K))
    (candidate : Plane.Point K) :
    candidate ∈ data.commonReflectedCirclePoints candidates ↔
      candidate ∈ candidates ∧ data.IsCommonReflectedCirclePoint candidate := by
  constructor
  · intro member
    rewrite [Geometry.Triangles.Reflection.Circumcircle.FiniteRegion.ReflectionTriangleData.commonReflectedCirclePoints]
      at member
    have filtered := List.Filter.mem_filter.mp member
    exact ⟨filtered.1, of_decide_eq_true filtered.2⟩
  · intro member
    rewrite [Geometry.Triangles.Reflection.Circumcircle.FiniteRegion.ReflectionTriangleData.commonReflectedCirclePoints]
    exact List.Filter.mem_filter.mpr ⟨member.1, decide_eq_true member.2⟩

/-- A singleton result is an exact uniqueness certificate on the supplied finite search region. -/
theorem
  ReflectionTriangleData.common_reflected_circle_point_unique_in_region
    [DecidableEq K]
    (data : Geometry.Triangles.Reflection.Circumcircle.FiniteRegion.ReflectionTriangleData K) (candidates : List
      (Plane.Point K))
    (common candidate : Plane.Point K)
    (singleton : data.commonReflectedCirclePoints candidates = [common])
    (candidateMember : candidate ∈ candidates)
    (candidateCommon : data.IsCommonReflectedCirclePoint candidate) :
    candidate = common := by
  have retained :
      candidate ∈ data.commonReflectedCirclePoints candidates :=
    (data.memCommonReflectedCirclePoints candidates candidate).2
      ⟨candidateMember, candidateCommon⟩
  rewrite [singleton] at retained
  cases retained with
  | head => rfl
  | tail _ impossible => exact False.elim (List.not_mem_nil impossible)

end ReflectionTriangleData
end ResectionApplications
end Purelib.Geometry.Triangles.Reflection.Circumcircle.FiniteRegion

end
