module

public import Purelib.Curves.Legendre.Paths
public import Purelib.Curves.Legendre.Paths.Projection
public import Purelib.Data.Fin
import Purelib.Data.Gaussian.Coordinates.Rotation
import Purelib.Tactic.QuotientFreeOmega

/-!
# Original vertices and common charts of finite safe Legendre paths

The retained path supplies one original initial vertex and the vertices of
its same structural tail. Segment safety derives later vertex regularity.
Intrinsic regularity at the original start also handles an empty path, and
the existing finite parameter-family constructor computes one shared chart.
-/

public section

namespace Purelib.Curves.Legendre.Paths.SafePath

open Purelib
open Purelib.Data.Gaussian.Coordinates

/-- Fold an original finite axis family into the existing safe path from intrinsic whole-unit avoidance.

Every original axis is retained at its original consecutive vertex indices.
Its two clearance certificates are computed internally once. Structural
recursion retains the same successor-index tail; an empty family keeps its
one original point and supplies no regularity claim about that point.
-/
@[expose] def ofAxisSegments : (size : Nat) → (points : Fin (size + 1) → Gaussian) →
    (axes : (index : Fin size) → AxisSegment (points index.castSucc) (points index.succ)) →
    (∀ index : Fin size, (axes index).Avoids 0) → (∀ index : Fin size, (axes index).Avoids 1) →
    SafePath (points 0) (points ⟨size, Nat.lt_succ_self size⟩)
  | 0, points, _, _, _ => .nil (points 0)
  | size + 1, points, axes, avoidsZero, avoidsOne =>
      let head := axes 0
      let safe := AxisSegment.Safe.ofAvoidance head (avoidsZero 0) (avoidsOne 0)
      .cons head safe (ofAxisSegments size (fun index => points index.succ) (fun index => axes index.succ)
        (fun index => avoidsZero index.succ) (fun index => avoidsOne index.succ))

/-- The actual finite-axis fold retains the complete original head, its computed safety and the same original tail. -/
theorem ofAxisSegments_cons (size : Nat) (points : Fin (size + 2) → Gaussian)
    (axes : (index : Fin (size + 1)) → AxisSegment (points index.castSucc) (points index.succ))
    (avoidsZero : ∀ index : Fin (size + 1), (axes index).Avoids 0)
    (avoidsOne : ∀ index : Fin (size + 1), (axes index).Avoids 1) :
    ofAxisSegments (size + 1) points axes avoidsZero avoidsOne =
      SafePath.cons (axes 0) (AxisSegment.Safe.ofAvoidance (axes 0) (avoidsZero 0) (avoidsOne 0))
        (ofAxisSegments size (fun index => points index.succ) (fun index => axes index.succ)
          (fun index => avoidsZero index.succ) (fun index => avoidsOne index.succ)) := rfl

/-- The same existing safe path retains every original indexed axis and its original traversal order.

Each nonempty input head occurs as that exact original axis, with its actual
retained safety certificate and remaining safe path. The tail follows the
same successor-index input families. Empty input has no retained axis. This
geometric readback is independent of how the clearance data was computed.
-/
def FollowsAxes : (size : Nat) → (points : Fin (size + 1) → Gaussian) →
    ((index : Fin size) → AxisSegment (points index.castSucc) (points index.succ)) →
    SafePath (points 0) (points ⟨size, Nat.lt_succ_self size⟩) → Prop
  | 0, _, _, original => original.stepCount = 0
  | size + 1, points, axes, original =>
      ∃ safe : AxisSegment.Safe (axes 0),
        ∃ remaining : SafePath (points (0 : Fin (size + 1)).succ)
            (points ⟨size + 1, Nat.lt_succ_self (size + 1)⟩),
          original = SafePath.cons (axes 0) safe remaining ∧
            FollowsAxes size (fun index => points index.succ) (fun index => axes index.succ) remaining

namespace FollowsAxes

/-- The original empty safe path follows the same one-point input family. -/
theorem nil (points : Fin 1 → Gaussian) (axes : (index : Fin 0) →
    AxisSegment (points index.castSucc) (points index.succ)) :
    (SafePath.nil (points 0)).FollowsAxes 0 points axes := by
  change (SafePath.nil (points 0)).stepCount = 0
  rfl

/-- An empty input family has no retained axis in its same original safe path. -/
theorem nil_data {points : Fin 1 → Gaussian} {axes : (index : Fin 0) →
    AxisSegment (points index.castSucc) (points index.succ)}
    {original : SafePath (points 0) (points ⟨0, Nat.lt_succ_self 0⟩)}
    (follows : original.FollowsAxes 0 points axes) : original.stepCount = 0 := follows

/-- Empty input determines the same original empty safe path at its original point. -/
theorem nil_eq {points : Fin 1 → Gaussian} {axes : (index : Fin 0) →
    AxisSegment (points index.castSucc) (points index.succ)}
    {original : SafePath (points 0) (points ⟨0, Nat.lt_succ_self 0⟩)}
    (follows : original.FollowsAxes 0 points axes) : original = SafePath.nil (points 0) := by
  have count := nil_data follows
  cases original with
  | nil => rfl
  | cons head safe tail => exact False.elim (Nat.noConfusion count)

/-- Prepending an exact original head and its retained safety preserves the indexed original axis family. -/
theorem cons {size : Nat} {points : Fin (size + 2) → Gaussian}
    {axes : (index : Fin (size + 1)) → AxisSegment (points index.castSucc) (points index.succ)}
    (safe : AxisSegment.Safe (axes 0))
    {remaining : SafePath (points (0 : Fin (size + 1)).succ)
      (points ⟨size + 1, Nat.lt_succ_self (size + 1)⟩)}
    (follows : remaining.FollowsAxes size (fun index => points index.succ) (fun index => axes index.succ)) :
    (SafePath.cons (axes 0) safe remaining).FollowsAxes (size + 1) points axes :=
  ⟨safe, remaining, rfl, follows⟩

/-- Read the actual original head safety, retained tail and complete head equality from indexed geometric readback. -/
theorem cons_data {size : Nat} {points : Fin (size + 2) → Gaussian}
    {axes : (index : Fin (size + 1)) → AxisSegment (points index.castSucc) (points index.succ)}
    {original : SafePath (points 0) (points ⟨size + 1, Nat.lt_succ_self (size + 1)⟩)}
    (follows : original.FollowsAxes (size + 1) points axes) :
    ∃ safe : AxisSegment.Safe (axes 0),
      ∃ remaining : SafePath (points (0 : Fin (size + 1)).succ)
          (points ⟨size + 1, Nat.lt_succ_self (size + 1)⟩),
        original = SafePath.cons (axes 0) safe remaining ∧
          remaining.FollowsAxes size (fun index => points index.succ) (fun index => axes index.succ) := follows

/-- Indexed geometric readback retains exactly the original number of axes. -/
theorem stepCount : {size : Nat} → {points : Fin (size + 1) → Gaussian} →
    {axes : (index : Fin size) → AxisSegment (points index.castSucc) (points index.succ)} →
    {original : SafePath (points 0) (points ⟨size, Nat.lt_succ_self size⟩)} →
    original.FollowsAxes size points axes → original.stepCount = size
  | 0, _, _, _, follows => nil_data follows
  | size + 1, _, _, _, follows => by
      rcases cons_data follows with ⟨safe, remaining, readback, tailFollows⟩
      rewrite [readback]
      change remaining.stepCount + 1 = size + 1
      exact congrArg Nat.succ (stepCount tailFollows)

end FollowsAxes

/-- The internally computed safety fold follows the same complete original indexed geometry. -/
theorem ofAxisSegments_followsAxes : (size : Nat) → (points : Fin (size + 1) → Gaussian) →
    (axes : (index : Fin size) → AxisSegment (points index.castSucc) (points index.succ)) →
    (avoidsZero : ∀ index : Fin size, (axes index).Avoids 0) →
    (avoidsOne : ∀ index : Fin size, (axes index).Avoids 1) →
    (ofAxisSegments size points axes avoidsZero avoidsOne).FollowsAxes size points axes
  | 0, points, axes, _, _ => FollowsAxes.nil points axes
  | size + 1, points, axes, avoidsZero, avoidsOne =>
      FollowsAxes.cons (AxisSegment.Safe.ofAvoidance (axes 0) (avoidsZero 0) (avoidsOne 0))
        (ofAxisSegments_followsAxes size (fun index => points index.succ) (fun index => axes index.succ)
          (fun index => avoidsZero index.succ) (fun index => avoidsOne index.succ))

/-- Internally deriving safety preserves the same original finite axis count. -/
theorem ofAxisSegments_stepCount (size : Nat) (points : Fin (size + 1) → Gaussian)
    (axes : (index : Fin size) → AxisSegment (points index.castSucc) (points index.succ))
    (avoidsZero : ∀ index : Fin size, (axes index).Avoids 0) (avoidsOne : ∀ index : Fin size, (axes index).Avoids 1) :
    (ofAxisSegments size points axes avoidsZero avoidsOne).stepCount = size :=
  (ofAxisSegments_followsAxes size points axes avoidsZero avoidsOne).stepCount

/-- A point lies on an original retained unit axis or the final point of the same finite safe path. -/
def Visits : {start finish : Gaussian} → SafePath start finish → Gaussian → Prop
  | start, _, .nil _, point => point = start
  | _, _, .cons segment _ tail, point =>
      (∃ parameter : Coordinate, 0 ≤ parameter ∧ parameter ≤ 1 ∧ segment.pointAt parameter = point) ∨
        Visits tail point

namespace Visits

/-- The original empty safe path visits its same actual point. -/
theorem nil {start : Gaussian} {point : Gaussian} (same : point = start) : (SafePath.nil start).Visits point := same

/-- Read the original point equality from membership in the same empty safe path. -/
theorem nil_data {start : Gaussian} {point : Gaussian} (visited : (SafePath.nil start).Visits point) :
    point = start := visited

/-- An actual original unit-axis point remains a point of the same retained nonempty safe path. -/
theorem cons_head {start middle finish : Gaussian} (segment : AxisSegment start middle)
    (safe : AxisSegment.Safe segment) {tail : SafePath middle finish} {point : Gaussian} (parameter : Coordinate)
    (inside : 0 ≤ parameter ∧ parameter ≤ 1) (hits : segment.pointAt parameter = point) :
    (SafePath.cons segment safe tail).Visits point := Or.inl ⟨parameter, inside.1, inside.2, hits⟩

/-- An original tail point remains a point of the same safe path after prepending its retained axis. -/
theorem cons_tail {start middle finish : Gaussian} (segment : AxisSegment start middle)
    (safe : AxisSegment.Safe segment) {tail : SafePath middle finish} {point : Gaussian}
    (visited : tail.Visits point) : (SafePath.cons segment safe tail).Visits point := Or.inr visited

/-- Read the actual original head parameter or the retained tail membership from a nonempty safe path. -/
theorem cons_data {start middle finish : Gaussian} {segment : AxisSegment start middle}
    {safe : AxisSegment.Safe segment} {tail : SafePath middle finish} {point : Gaussian}
    (visited : (SafePath.cons segment safe tail).Visits point) :
    (∃ parameter : Coordinate, 0 ≤ parameter ∧ parameter ≤ 1 ∧ segment.pointAt parameter = point) ∨
      tail.Visits point := visited

end Visits

/-- Read the original finite vertex family of the same retained safe path, including both outer endpoints.

The first index selects the original source parameter. Each successor index
selects its retained predecessor in the same original tail; the empty path
has its one actual point. No vertex or path owner is reconstructed.
-/
@[expose] def vertices : {start finish : Gaussian} → (path : SafePath start finish) →
    Fin (path.stepCount + 1) → Gaussian
  | _, _, .nil point => fun _ => point
  | start, _, .cons _ _ tail => Data.Fin.cases start tail.vertices

/-- The first vertex is the same original safe-path source parameter. -/
theorem vertices_source {start finish : Gaussian} (path : SafePath start finish) : path.vertices 0 = start := by
  cases path with
  | nil point => rfl
  | cons segment safe tail => exact Data.Fin.cases_zero _ _

/-- Prepending an original segment retains the same tail vertex at each successor index. -/
theorem vertices_tail {start middle finish : Gaussian} (segment : AxisSegment start middle)
    (safe : AxisSegment.Safe segment) (tail : SafePath middle finish) (index : Fin (tail.stepCount + 1)) :
    (SafePath.cons segment safe tail).vertices index.succ = tail.vertices index := Data.Fin.cases_succ _ _ _

/-- The last vertex is the same original safe-path target parameter. -/
theorem vertices_target {start finish : Gaussian} (path : SafePath start finish) :
    path.vertices ⟨path.stepCount, Nat.lt_succ_self path.stepCount⟩ = finish := by
  induction path with
  | nil point => rfl
  | cons segment safe tail inductionHypothesis =>
      exact (vertices_tail segment safe tail
        ⟨tail.stepCount, Nat.lt_succ_self tail.stepCount⟩).trans inductionHypothesis

/-- Intrinsic start regularity and the original segment safety data exclude both singular parameters at every vertex.

Every original segment's retained whole-unit clearances exclude its actual
target point. Those same exclusions supply the original tail's start
regularity; no numerical clearance or enumerated regularity certificate is
requested for the vertex family.
-/
theorem vertices_regular {start finish : Gaussian} (path : SafePath start finish)
    (nonzero : start ≠ 0) (notOne : start ≠ 1) (index : Fin (path.stepCount + 1)) :
    path.vertices index ≠ 0 ∧ path.vertices index ≠ 1 := by
  induction path with
  | nil point => exact ⟨nonzero, notOne⟩
  | cons segment safe tail inductionHypothesis =>
      apply Data.Fin.cases_induction (motive := fun index =>
        (SafePath.cons segment safe tail).vertices index ≠ 0 ∧
          (SafePath.cons segment safe tail).vertices index ≠ 1) _ _ index
      · exact ⟨nonzero, notOne⟩
      · intro following
        change tail.vertices following ≠ 0 ∧ tail.vertices following ≠ 1
        have tailNonzero := safe.avoidsZero.avoids 1 (by decide) (by decide)
        have tailNotOne := safe.avoidsOne.avoids 1 (by decide) (by decide)
        rewrite [segment.pointAt_one] at tailNonzero tailNotOne
        exact inductionHypothesis tailNonzero tailNotOne following

/-- Intrinsic vertex regularity separates the fixed readings in every chart paying all original vertex costs. -/
theorem vertices_separated_of_slopeCost {start finish : Gaussian} (path : SafePath start finish)
    (slope : Coordinate) (nonzero : start ≠ 0) (notOne : start ≠ 1)
    (paid : ∀ index : Fin (path.stepCount + 1), Paths.Projection.slopeCost (path.vertices index) < slope)
    (index : Fin (path.stepCount + 1)) :
    (Rotation.rotate slope (path.vertices index)).re ≠ 0 ∧
      (Rotation.rotate slope (path.vertices index)).re ≠ 1 := by
  have regular := path.vertices_regular nonzero notOne index
  have separated := Paths.Projection.separates_of_slopeCost (path.vertices index) slope (paid index) regular.1 regular.2
  rewrite [← Rotation.rotate_real] at separated
  exact separated

/-- Compute one shared original projection slope from every retained vertex of the same finite safe path. -/
@[expose] def projectionSlope {start finish : Gaussian} (path : SafePath start finish) : Coordinate :=
  Paths.Projection.forParameters path.vertices

/-- Every regular original vertex separates the fixed readings in the same internally computed path chart. -/
theorem projectionSlope_separates {start finish : Gaussian} (path : SafePath start finish)
    (nonzero : start ≠ 0) (notOne : start ≠ 1) (index : Fin (path.stepCount + 1)) :
    (Rotation.rotate path.projectionSlope (path.vertices index)).re ≠ 0 ∧
      (Rotation.rotate path.projectionSlope (path.vertices index)).re ≠ 1 := by
  have regular := path.vertices_regular nonzero notOne index
  have separated := Paths.Projection.forParameters_separates path.vertices index regular.1 regular.2
  rewrite [← Rotation.rotate_real] at separated
  exact separated

namespace FollowsAxes

/-- Every original input axis point is visited by the same retained safe path that follows its indexed family. -/
theorem visits : {size : Nat} → {points : Fin (size + 1) → Gaussian} →
    {axes : (index : Fin size) → AxisSegment (points index.castSucc) (points index.succ)} →
    {original : SafePath (points 0) (points ⟨size, Nat.lt_succ_self size⟩)} →
    original.FollowsAxes size points axes → (index : Fin size) → (parameter : Coordinate) →
    (0 ≤ parameter ∧ parameter ≤ 1) → original.Visits ((axes index).pointAt parameter)
  | 0, _, _, _, _, index, _, _ => Fin.elim0 index
  | size + 1, points, axes, _, follows, index, parameter, inside => by
      rcases cons_data follows with ⟨safe, remaining, readback, tailFollows⟩
      rewrite [readback]
      apply Data.Fin.cases_induction (motive := fun index =>
        (SafePath.cons (axes 0) safe remaining).Visits ((axes index).pointAt parameter)) _ _ index
      · exact Visits.cons_head (axes 0) safe parameter inside rfl
      · intro following
        exact Visits.cons_tail (axes 0) safe (visits tailFollows following parameter inside)

/-- Every retained vertex has the same Gaussian reading at its original finite input ordinal.

The count equality transports only the finite index bound. Structural
readback retains the original source at ordinal zero and the original tail
vertex at each successor; no equality between function families is used.
-/
theorem vertices : {size : Nat} → {points : Fin (size + 1) → Gaussian} →
    {axes : (index : Fin size) → AxisSegment (points index.castSucc) (points index.succ)} →
    {original : SafePath (points 0) (points ⟨size, Nat.lt_succ_self size⟩)} →
    (follows : original.FollowsAxes size points axes) → (index : Fin (size + 1)) →
    original.vertices (Fin.cast (congrArg (fun count : Nat => count + 1) follows.stepCount).symm index) = points index
  | 0, points, _, original, follows, index => by
      have same : index = 0 := Fin.ext (Nat.le_antisymm (Nat.le_of_lt_succ index.isLt) (Nat.zero_le _))
      subst index
      exact original.vertices_source
  | size + 1, points, axes, original, follows, index => by
      rcases cons_data follows with ⟨safe, remaining, readback, tailFollows⟩
      subst original
      apply Data.Fin.cases_induction (motive := fun index =>
        (SafePath.cons (axes 0) safe remaining).vertices
          (Fin.cast (congrArg (fun count : Nat => count + 1) follows.stepCount).symm index) = points index) _ _ index
      · exact (SafePath.cons (axes 0) safe remaining).vertices_source
      · intro following
        change remaining.vertices
          (Fin.cast (congrArg (fun count : Nat => count + 1) tailFollows.stepCount).symm following) =
            points following.succ
        exact vertices tailFollows following

end FollowsAxes

/-- Check every original unit axis and retain either its actual safety fold or an exact original singular collision.

Each head invokes the original whole-unit safety checker once. Success keeps
that same computed certificate and the same checked tail. Failure retains
the original finite axis index, violated singular value and actual unit
collision parameter; an empty family has no axis to check.
-/
@[expose] def checkAxisSegments : (size : Nat) → (points : Fin (size + 1) → Gaussian) →
    (axes : (index : Fin size) → AxisSegment (points index.castSucc) (points index.succ)) →
    {original : SafePath (points 0) (points ⟨size, Nat.lt_succ_self size⟩) // original.FollowsAxes size points axes} ⊕
      (Σ index : Fin size, AxisSegment.Collision (axes index) 0 ⊕ AxisSegment.Collision (axes index) 1)
  | 0, points, axes => .inl ⟨SafePath.nil (points 0), FollowsAxes.nil points axes⟩
  | size + 1, points, axes =>
      match (axes 0).checkSafety with
      | .inr collision => .inr ⟨0, collision⟩
      | .inl safe =>
          match checkAxisSegments size (fun index => points index.succ) (fun index => axes index.succ) with
          | .inl remaining => .inl ⟨SafePath.cons (axes 0) safe remaining.val, FollowsAxes.cons safe remaining.property⟩
          | .inr collision => .inr ⟨collision.1.succ, collision.2⟩

end Purelib.Curves.Legendre.Paths.SafePath
