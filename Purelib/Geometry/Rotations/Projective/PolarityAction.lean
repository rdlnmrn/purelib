module
public import Purelib.Data.Nat.Order
public import Purelib.Algebra.Group.Negation
import Purelib.Geometry.Rotations.Axis.Recovery
public import Purelib.Geometry.Rotations.Cayley.Product
public import Purelib.Geometry.Rotations.Orientation.Handedness
import Purelib.Geometry.Rotations.Spread

import Purelib.Algebra.Field.ExplicitField
public import Purelib.Geometry.Projective.Space3.Polarity
import Purelib.Geometry.Rotations.Basic
import Purelib.Geometry.Rotations.Cayley.Cap
import Purelib.Geometry.Rotations.Reflection
public import Purelib.LinearAlgebra.Coordinates3.Independence
import Purelib.LinearAlgebra.Coordinates3.Matrix
import Purelib.LinearAlgebra.Coordinates3.Vector
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Tactic.Ring

section
open Purelib.Algebra
open Purelib.Data

-- These owned adapters retain the complete original operation dictionaries.
attribute [local instance 2000] Group.Negation.subNegZeroMonoid
  Nat.successorNeZero Nat.successorAtLeastTwo

open Purelib

open Purelib.Geometry

open Purelib.Geometry.Projective.Space3

open Purelib.Geometry.Projective.Space3.Polarity

open Purelib.Geometry.Rotations

open Purelib.Geometry.Rotations.Axis

open Purelib.Geometry.Rotations.Orientation

open Purelib.LinearAlgebra

section
public section

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

section

open Purelib.Geometry.Rotations.Basic
open Purelib.Geometry.Rotations.Reflection
open Purelib.Geometry.Rotations.Cayley.Cap

open Purelib.LinearAlgebra.Coordinates3

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

namespace Purelib.Geometry.Rotations.Projective.PolarityAction

/-- A rotation cannot send a displayed nonzero vector to zero. -/
theorem rowMul_rotation_ne_zero (rotation :
  Rotations.Basic.Rotation K) (vector : Coordinates3.Vector K)
    (nonzero : vector ≠ Coordinates3.Vector.zero) :
    Matrix3.rowMul vector rotation.matrix ≠ Coordinates3.Vector.zero := by
  intro imageZero
  apply nonzero
  calc
    vector = Matrix3.rowMul vector Matrix3.identity := by
      rw [Matrix3.rowMul_identity]
    _ = Matrix3.rowMul vector
        (Matrix3.mul rotation.matrix (Matrix3.transpose rotation.matrix)) := by
      rw [rotation.orthogonal]
    _ = Matrix3.rowMul (Matrix3.rowMul vector rotation.matrix)
        (Matrix3.transpose rotation.matrix) := by
      rw [Matrix3.rowMul_mul]
    _ = Matrix3.rowMul Coordinates3.Vector.zero (Matrix3.transpose rotation.matrix) := by
      rw [imageZero]
    _ = Coordinates3.Vector.zero := by
      ext <;> unfold Matrix3.rowMul Coordinates3.Vector.zero <;> ring1

end Purelib.Geometry.Rotations.Projective.PolarityAction

namespace Purelib.Geometry.Rotations.Projective.PolarityAction.Vector

/-- Orthogonal action preserves the spread expression on two non-null displayed directions. -/
theorem spread_rowMul_rotation (rotation :
  Rotations.Basic.Rotation K)
    (left right : Coordinates3.Vector K)
    (leftNonNull : left.quadrance ≠ 0)
    (rightNonNull : right.quadrance ≠ 0) :
    Coordinates3.Vector.spread (Matrix3.rowMul left rotation.matrix)
        (Matrix3.rowMul right rotation.matrix)
        (Spread.rowMul_rotation_nonNull rotation left leftNonNull)
        (Spread.rowMul_rotation_nonNull rotation right rightNonNull) =
      Coordinates3.Vector.spread left right leftNonNull rightNonNull := by
  unfold Coordinates3.Vector.spread
  rw [Matrix3.dot_rowMul_of_isOrthogonal rotation.orthogonal,
    Spread.quadrance_rowMul_rotation, Spread.quadrance_rowMul_rotation]

end Purelib.Geometry.Rotations.Projective.PolarityAction.Vector

namespace Purelib.Geometry.Rotations.Projective.PolarityAction

/-- The identity rotation, used to state the projective action laws over an arbitrary explicit field. -/
@[expose] def rotationIdentity : Rotations.Basic.Rotation K
  where
  matrix := Matrix3.identity
  orthogonal := by
    unfold Purelib.LinearAlgebra.Coordinates3.Matrix3.IsOrthogonal
    rw [Matrix3.transpose_identity, Matrix3.identity_mul]
  determinantOne := Matrix3.determinant_identity

end Purelib.Geometry.Rotations.Projective.PolarityAction

section

namespace Purelib.Geometry.Projective.Space3.Polarity.ProjectivePoint

/-- The row-vector rotation action on a displayed projective point. -/
@[expose] def act (point : Polarity.ProjectivePoint
  K) (rotation : Rotations.Basic.Rotation K) :
    Polarity.ProjectivePoint K where
  coordinates := Matrix3.rowMul point.coordinates rotation.matrix
  nonzero := Rotations.Projective.PolarityAction.rowMul_rotation_ne_zero rotation point.coordinates
    point.nonzero

/-- Rotation preserves non-nullness of the displayed projective point. -/
theorem act_nonNull (point : Polarity.ProjectivePoint
  K) (rotation : Rotations.Basic.Rotation K)
    (nonNull : point.IsNonNull) : (point.act rotation).IsNonNull :=
  Spread.rowMul_rotation_nonNull rotation point.coordinates nonNull

/-- Rotation respects explicit nonzero-scale equivalence of projective points. -/
theorem act_respects_equivalent {left right :
  Polarity.ProjectivePoint K}
    (equivalent : left.Equivalent right) (rotation : Rotations.Basic.Rotation K) :
    (left.act rotation).Equivalent (right.act rotation) := by
  rcases equivalent with ⟨factor, factorNonzero, rightValue⟩
  refine ⟨factor, factorNonzero, ?_⟩
  change Matrix3.rowMul right.coordinates rotation.matrix =
    Coordinates3.Vector.scale factor
      (Matrix3.rowMul left.coordinates rotation.matrix)
  rw [rightValue]
  ext <;> unfold Matrix3.rowMul Coordinates3.Vector.scale <;> ring1

/-- The identity rotation fixes the displayed projective point. -/
@[simp] theorem act_identity (point :
  Polarity.ProjectivePoint K) :
    point.act (Rotations.Projective.PolarityAction.rotationIdentity (K := K)) = point := by
  apply ProjectivePoint.ext
  exact Matrix3.rowMul_identity point.coordinates

/-- Successive actions on a projective point agree with the row-order rotation product. -/
theorem act_product (point : Polarity.ProjectivePoint
  K) (left right : Rotations.Basic.Rotation K) :
    (point.act left).act right = point.act (Cayley.Product.rotationProduct left right) := by
  apply ProjectivePoint.ext
  exact Matrix3.rowMul_mul point.coordinates left.matrix right.matrix

/-- Acting by a rotation and then its inverse recovers the original projective point. -/
@[simp] theorem act_inverse_right (point :
  Polarity.ProjectivePoint K)
    (rotation : Rotations.Basic.Rotation K) :
    (point.act rotation).act (Handedness.inverseRotation rotation) = point := by
  apply ProjectivePoint.ext
  change Matrix3.rowMul
      (Matrix3.rowMul point.coordinates rotation.matrix)
      (Matrix3.transpose rotation.matrix) = point.coordinates
  rw [Matrix3.rowMul_mul, rotation.orthogonal, Matrix3.rowMul_identity]

/-- Acting by the inverse and then the rotation recovers the original projective point. -/
@[simp] theorem act_inverse_left (point :
  Polarity.ProjectivePoint K)
    (rotation : Rotations.Basic.Rotation K) :
    (point.act (Handedness.inverseRotation rotation)).act rotation = point := by
  apply ProjectivePoint.ext
  change Matrix3.rowMul
      (Matrix3.rowMul point.coordinates (Matrix3.transpose rotation.matrix))
      rotation.matrix = point.coordinates
  rw [Matrix3.rowMul_mul, Recovery.transpose_mul_rotation,
    Matrix3.rowMul_identity]

/-- Simultaneous rotation preserves the projective quadrance of two non-null points. -/
theorem quadrance_act (left right :
  Polarity.ProjectivePoint K)
    (rotation : Rotations.Basic.Rotation K)
    (leftNonNull : left.IsNonNull) (rightNonNull : right.IsNonNull) :
    (left.act rotation).quadrance (right.act rotation)
        (left.act_nonNull rotation leftNonNull)
        (right.act_nonNull rotation rightNonNull) =
      left.quadrance right leftNonNull rightNonNull :=
  Rotations.Projective.PolarityAction.Vector.spread_rowMul_rotation rotation left.coordinates right.coordinates
    leftNonNull rightNonNull

end Purelib.Geometry.Projective.Space3.Polarity.ProjectivePoint

end

section

namespace Purelib.Geometry.Projective.Space3.Polarity.PlaneNormal

/-- Contravariant plane action. In the row-vector orthogonal convention its normal transforms by the same displayed
rotation matrix: simultaneous point and normal action preserves their dot product. -/
@[expose] def act (plane : Polarity.PlaneNormal K)
  (rotation : Rotations.Basic.Rotation K) : Polarity.PlaneNormal K where
  normal := Matrix3.rowMul plane.normal rotation.matrix
  nonzero := Rotations.Projective.PolarityAction.rowMul_rotation_ne_zero rotation plane.normal plane.nonzero

/-- Any displayed fixed vector gives the corresponding exactly fixed polar plane. This is the direct adapter for
fixed-axis theorems throughout the paper. -/
theorem fixed_of_normal_fixed (rotation :
  Rotations.Basic.Rotation K) (plane : Polarity.PlaneNormal K)
    (fixed : Matrix3.rowMul plane.normal rotation.matrix = plane.normal) :
    plane.act rotation = plane := by
  apply PlaneNormal.ext
  exact fixed

/-- Rotation preserves non-nullness of the displayed plane normal. -/
theorem act_nonNull (plane : Polarity.PlaneNormal K)
  (rotation : Rotations.Basic.Rotation K)
    (nonNull : plane.IsNonNull) : (plane.act rotation).IsNonNull :=
  Spread.rowMul_rotation_nonNull rotation plane.normal nonNull

/-- Rotation preserves the quadrance of the displayed plane normal. -/
theorem act_preserves_quadrance (plane :
  Polarity.PlaneNormal K)
    (rotation : Rotations.Basic.Rotation K) :
    (plane.act rotation).normal.quadrance = plane.normal.quadrance :=
  Spread.quadrance_rowMul_rotation rotation plane.normal

/-- Rotation respects explicit nonzero-scale equivalence of plane normals. -/
theorem act_respects_equivalent {left right :
  Polarity.PlaneNormal K}
    (equivalent : left.Equivalent right) (rotation : Rotations.Basic.Rotation K) :
    (left.act rotation).Equivalent (right.act rotation) := by
  rcases equivalent with ⟨factor, factorNonzero, rightValue⟩
  refine ⟨factor, factorNonzero, ?_⟩
  change Matrix3.rowMul right.normal rotation.matrix =
    Coordinates3.Vector.scale factor (Matrix3.rowMul left.normal rotation.matrix)
  rw [rightValue]
  ext <;> unfold Matrix3.rowMul Coordinates3.Vector.scale <;> ring1

/-- The identity rotation fixes the displayed plane normal. -/
@[simp] theorem act_identity (plane :
  Polarity.PlaneNormal K) :
    plane.act (Rotations.Projective.PolarityAction.rotationIdentity (K := K)) = plane := by
  apply PlaneNormal.ext
  exact Matrix3.rowMul_identity plane.normal

/-- Successive actions on a plane normal agree with the row-order rotation product. -/
theorem act_product (plane : Polarity.PlaneNormal K)
  (left right : Rotations.Basic.Rotation K) :
    (plane.act left).act right = plane.act (Cayley.Product.rotationProduct left right) := by
  apply PlaneNormal.ext
  exact Matrix3.rowMul_mul plane.normal left.matrix right.matrix

/-- Acting by a rotation and then its inverse recovers the original plane normal. -/
@[simp] theorem act_inverse_right (plane :
  Polarity.PlaneNormal K)
    (rotation : Rotations.Basic.Rotation K) :
    (plane.act rotation).act (Handedness.inverseRotation rotation) = plane := by
  apply PlaneNormal.ext
  change Matrix3.rowMul (Matrix3.rowMul plane.normal rotation.matrix)
      (Matrix3.transpose rotation.matrix) = plane.normal
  rw [Matrix3.rowMul_mul, rotation.orthogonal, Matrix3.rowMul_identity]

/-- Acting by the inverse and then the rotation recovers the original plane normal. -/
@[simp] theorem act_inverse_left (plane :
  Polarity.PlaneNormal K)
    (rotation : Rotations.Basic.Rotation K) :
    (plane.act (Handedness.inverseRotation rotation)).act rotation = plane := by
  apply PlaneNormal.ext
  change Matrix3.rowMul
      (Matrix3.rowMul plane.normal (Matrix3.transpose rotation.matrix))
      rotation.matrix = plane.normal
  rw [Matrix3.rowMul_mul, Recovery.transpose_mul_rotation,
    Matrix3.rowMul_identity]

/-- Simultaneous rotation preserves the spread of two non-null plane normals. -/
theorem spread_act (left right : Polarity.PlaneNormal K)
  (rotation : Rotations.Basic.Rotation K)
    (leftNonNull : left.IsNonNull) (rightNonNull : right.IsNonNull) :
    (left.act rotation).spread (right.act rotation)
        (left.act_nonNull rotation leftNonNull)
        (right.act_nonNull rotation rightNonNull) =
      left.spread right leftNonNull rightNonNull :=
  Rotations.Projective.PolarityAction.Vector.spread_rowMul_rotation rotation left.normal right.normal
    leftNonNull rightNonNull

end Purelib.Geometry.Projective.Space3.Polarity.PlaneNormal

end

/-! ## The polarity and its metrical laws -/

section
end

section
end

namespace Purelib.Geometry.Projective.Space3.Polarity.ProjectivePoint

/-- Taking the polar dual commutes with rotation of a projective point. -/
@[simp] theorem dual_act (point :
  Polarity.ProjectivePoint K)
    (rotation : Rotations.Basic.Rotation K) :
    (point.act rotation).dual = point.dual.act rotation := rfl

end Purelib.Geometry.Projective.Space3.Polarity.ProjectivePoint

namespace Purelib.Geometry.Projective.Space3.Polarity.PlaneNormal

/-- Taking the polar dual commutes with rotation of a plane normal. -/
@[simp] theorem dual_act (plane : Polarity.PlaneNormal K)
    (rotation : Rotations.Basic.Rotation K) :
    (plane.act rotation).dual = plane.dual.act rotation := rfl

end Purelib.Geometry.Projective.Space3.Polarity.PlaneNormal

section

namespace Purelib.Geometry.Projective.Space3.Polarity.ProjectivePoint

/-- Simultaneous rotation of a point and plane preserves incidence. -/
theorem incident_act_iff (point :
  Polarity.ProjectivePoint K) (plane : Polarity.PlaneNormal K)
    (rotation : Rotations.Basic.Rotation K) :
    (point.act rotation).Incident (plane.act rotation) ↔
      point.Incident plane := by
  unfold ProjectivePoint.Incident act PlaneNormal.act
  rw [Matrix3.dot_rowMul_of_isOrthogonal rotation.orthogonal]

end Purelib.Geometry.Projective.Space3.Polarity.ProjectivePoint

end

namespace Purelib.Geometry.Rotations.Projective.PolarityAction

/-! ## Constructive theorem-level translation -/

/-- A theorem schema about a projective point and its rotated image. All other parameters and hypotheses can be closed
over by `property`. -/
@[expose] def PointActionStatement (rotation :
  Rotations.Basic.Rotation K)
    (property : Coordinates3.Vector K → Coordinates3.Vector K → Prop) : Prop :=
  ∀ point : Polarity.ProjectivePoint K,
    property point.coordinates (point.act rotation).coordinates

/-- The plane-normal dual of `PointActionStatement`. -/
@[expose] def PlaneActionStatement (rotation :
  Rotations.Basic.Rotation K)
    (property : Coordinates3.Vector K → Coordinates3.Vector K → Prop) : Prop :=
  ∀ plane : Polarity.PlaneNormal K,
    property plane.normal (plane.act rotation).normal

/-- Every unary theorem about rotation acting on projective points is equivalent, constructively, to its derived theorem
about plane normals. -/
theorem pointActionStatement_iff_planeActionStatement
    (rotation : Rotations.Basic.Rotation K) (property : Coordinates3.Vector K → Coordinates3.Vector K → Prop) :
    PointActionStatement rotation property ↔
      PlaneActionStatement rotation property := by
  constructor
  · intro pointTheorem plane
    exact pointTheorem plane.dual
  · intro planeTheorem point
    exact planeTheorem point.dual

/-- Apply any existing raw-vector action theorem directly to displayed plane normals. This is the entry point for the
paper's already formalized vector theorems. -/
theorem planeActionStatement_of_vectorActionTheorem
    (rotation : Rotations.Basic.Rotation K) (property : Coordinates3.Vector K → Coordinates3.Vector K → Prop)
    (vectorTheorem : ∀ vector : Coordinates3.Vector K,
      property vector (Matrix3.rowMul vector rotation.matrix)) :
    PlaneActionStatement rotation property := by
  intro plane
  exact vectorTheorem plane.normal

/-- A theorem schema about two projective points and both rotated images. -/
@[expose] def PointPairActionStatement (rotation :
  Rotations.Basic.Rotation K)
    (property : Coordinates3.Vector K → Coordinates3.Vector K → Coordinates3.Vector K → Coordinates3.Vector K → Prop) :
    Prop :=
  ∀ left right : Polarity.ProjectivePoint K,
    property left.coordinates right.coordinates
      (left.act rotation).coordinates (right.act rotation).coordinates

/-- The plane-normal dual of `PointPairActionStatement`. -/
@[expose] def PlanePairActionStatement (rotation :
  Rotations.Basic.Rotation K)
    (property : Coordinates3.Vector K → Coordinates3.Vector K → Coordinates3.Vector K → Coordinates3.Vector K → Prop) :
    Prop :=
  ∀ left right : Polarity.PlaneNormal K,
    property left.normal right.normal
      (left.act rotation).normal (right.act rotation).normal

/-- Every binary theorem about simultaneous rotation of projective points is equivalent to its plane theorem. In
particular this transports all metrical relations expressible on two displayed representatives. -/
theorem
  pointPairActionStatement_iff_planePairActionStatement
    (rotation : Rotations.Basic.Rotation K)
    (property : Coordinates3.Vector K → Coordinates3.Vector K → Coordinates3.Vector K → Coordinates3.Vector K → Prop) :
    PointPairActionStatement rotation property ↔
      PlanePairActionStatement rotation property := by
  constructor
  · intro pointTheorem left right
    exact pointTheorem left.dual right.dual
  · intro planeTheorem left right
    exact planeTheorem left.dual right.dual

/-- Apply any existing two-vector action theorem to two displayed plane normals. -/
theorem planePairActionStatement_of_vectorActionTheorem
    (rotation : Rotations.Basic.Rotation K)
    (property : Coordinates3.Vector K → Coordinates3.Vector K → Coordinates3.Vector K → Coordinates3.Vector K → Prop)
    (vectorTheorem : ∀ left right : Coordinates3.Vector K,
      property left right
        (Matrix3.rowMul left rotation.matrix)
        (Matrix3.rowMul right rotation.matrix)) :
    PlanePairActionStatement rotation property := by
  intro left right
  exact vectorTheorem left.normal right.normal

/-- The completed finite content of Problem 72, packaged as one audited interface: involutive polarity, rotation
equivariance, incidence invariance, quadrance--spread correspondence, and theorem-level unary and binary translation. -/
structure ProblemSeventyTwoSolution (K : Type*)
  [Algebra.Field.ExplicitField K] where
  /-- Taking the polar dual twice recovers every displayed projective point. -/ pointRoundTrip : ∀ point :
    Polarity.ProjectivePoint K, point.dual.dual = point
  /-- Taking the polar dual twice recovers every displayed plane normal. -/ planeRoundTrip : ∀ plane :
    Polarity.PlaneNormal K, plane.dual.dual = plane
  /-- Point polarity commutes with every displayed rotation. -/ actionEquivariant : ∀ (point : Polarity.ProjectivePoint
    K) (rotation : Rotations.Basic.Rotation K),
    (point.act rotation).dual = point.dual.act rotation
  /-- Simultaneous rotation preserves and reflects point-plane incidence. -/ incidenceInvariant : ∀ (point :
    Polarity.ProjectivePoint K) (plane : Polarity.PlaneNormal K)
    (rotation : Rotations.Basic.Rotation K),
    (point.act rotation).Incident (plane.act rotation) ↔ point.Incident plane
  /-- Projective point quadrance equals the spread of the polar planes. -/ metricCorrespondence : ∀ (left right :
    Polarity.ProjectivePoint K)
    (leftNonNull : left.IsNonNull) (rightNonNull : right.IsNonNull),
    left.quadrance right leftNonNull rightNonNull =
      left.dual.spread right.dual leftNonNull rightNonNull
  /-- Every unary point-action statement is equivalent to its plane-normal dual. -/ unaryTranslation : ∀ (rotation :
    Rotations.Basic.Rotation K)
    (property : Coordinates3.Vector K → Coordinates3.Vector K → Prop),
    PointActionStatement rotation property ↔
      PlaneActionStatement rotation property
  /-- Every two-point action statement is equivalent to its two-plane-normal dual. -/ binaryTranslation : ∀ (rotation :
    Rotations.Basic.Rotation K)
    (property : Coordinates3.Vector K → Coordinates3.Vector K → Coordinates3.Vector K → Coordinates3.Vector K → Prop),
    PointPairActionStatement rotation property ↔
      PlanePairActionStatement rotation property

/-- The constructive solution of Problem 72. -/
theorem problemSeventyTwoSolution :
  ProblemSeventyTwoSolution K where
  pointRoundTrip := ProjectivePoint.dual_dual
  planeRoundTrip := PlaneNormal.dual_dual
  actionEquivariant := Purelib.Geometry.Projective.Space3.Polarity.ProjectivePoint.dual_act
  incidenceInvariant := Purelib.Geometry.Projective.Space3.Polarity.ProjectivePoint.incident_act_iff
  metricCorrespondence := Polarity.projectiveQuadrance_eq_dualPlaneSpread
  unaryTranslation := pointActionStatement_iff_planeActionStatement
  binaryTranslation :=
    pointPairActionStatement_iff_planePairActionStatement

/-! ## Duals of the paper's principal vector-action theorems -/

end Purelib.Geometry.Rotations.Projective.PolarityAction

section

namespace Purelib.Geometry.Projective.Space3.Polarity.PlaneNormal

/-- Dual of Theorem 17's fixed-axis clause: the half turn fixes the plane whose normal is its axis. -/
theorem halfTurn_axis_plane_fixed (axis :
  Coordinates3.Vector K)
    (axisNonNull : axis.quadrance ≠ 0) :
    let plane : Polarity.PlaneNormal K :=
      ⟨axis, Polarity.Vector.ne_zero_of_quadrance_ne_zero axisNonNull⟩
    plane.act (halfTurnRotation axis axisNonNull) = plane := by
  apply PlaneNormal.ext
  exact rowMul_self_halfTurn axis axisNonNull

/-- Dual of Theorem 17's perpendicular clause: a half turn negates a perpendicular normal, hence fixes the corresponding
projective plane. -/
theorem halfTurn_perpendicular_plane_equivalent (axis :
  Coordinates3.Vector K)
    (axisNonNull : axis.quadrance ≠ 0) (twoNonzero : (2 : K) ≠ 0)
    (plane : Polarity.PlaneNormal K) (perpendicular : plane.normal.Perpendicular axis) :
    plane.Equivalent (plane.act (halfTurnRotation axis axisNonNull)) := by
  have oneNonzero : (1 : K) ≠ 0 :=
    Polarity.one_ne_zero_of_vector_ne_zero plane.normal plane.nonzero
  refine ⟨-1, (by intro negZero; have restored := congrArg (fun value : K => -value) negZero; rewrite [neg_neg,
    SubNegZeroMonoid.neg_zero] at restored; exact oneNonzero restored), ?_⟩
  change Matrix3.rowMul plane.normal (halfTurn axis axisNonNull) =
    Coordinates3.Vector.scale (-1) plane.normal
  rw [rowMul_halfTurn_of_perpendicular axis axisNonNull twoNonzero
    plane.normal perpendicular]
  ext <;> unfold Coordinates3.Vector.neg Coordinates3.Vector.scale <;> ring1

/-- Dual of Theorem 19: the plane normal to the cross-product axis is fixed by the product of the two reflections. -/
theorem reflectionProduct_axis_plane_fixed
    (first second : Coordinates3.Vector K)
    (firstNonNull : first.quadrance ≠ 0)
    (secondNonNull : second.quadrance ≠ 0)
    (independent : Coordinates3.Vector.Independent first second)
    (twoNonzero : (2 : K) ≠ 0) :
    let plane : Polarity.PlaneNormal K := ⟨Coordinates3.Vector.cross first second, independent⟩
    plane.act (reflectionProductRotation first second firstNonNull secondNonNull) =
      plane := by
  apply PlaneNormal.ext
  exact rowMul_cross_reflection_product first second firstNonNull secondNonNull
    twoNonzero

/-- Dual of Theorem 24.2: a cap fixes the plane normal to its anchor. -/
theorem cap_axis_plane_fixed (axis : Coordinates3.Vector
  K)
    (axisNonzero : axis ≠ Coordinates3.Vector.zero)
    (defined : capDenominator axis ≠ 0) :
    let plane : Polarity.PlaneNormal K := ⟨axis, axisNonzero⟩
    plane.act (capRotation axis defined) = plane := by
  apply PlaneNormal.ext
  exact rowMul_self_cap axis defined

/-- Dual of Theorem 35.3: away from the half-turn chart, the recovered anchor is the normal of a fixed plane. -/
theorem recoveredAnchor_plane_fixed (rotation :
  Rotations.Basic.Rotation K)
    (notHalfTurn : Spread.halfSpread rotation ≠ 1)
    (twoNonzero : (2 : K) ≠ 0)
    (axisNonzero : Recovery.rotationAnchorVector rotation notHalfTurn ≠ Coordinates3.Vector.zero) :
    let plane : Polarity.PlaneNormal K :=
      ⟨Recovery.rotationAnchorVector rotation notHalfTurn, axisNonzero⟩
    plane.act rotation = plane := by
  apply PlaneNormal.ext
  exact Recovery.rowMul_rotationAnchorVector rotation notHalfTurn twoNonzero

end Purelib.Geometry.Projective.Space3.Polarity.PlaneNormal

namespace Purelib.Geometry.Projective.Space3.Polarity.PlaneNormal.RotationAxisSpreadWitness

/-- The dual of the uniform fixed-axis result cached by the canonical axis/spread wrapper. The identity branch has zero
canonical axis, so a nonzero hypothesis is exactly what is needed to obtain a projective plane. -/
theorem axis_plane_fixed
    {rotation : Rotations.Basic.Rotation K} (witness : Recovery.RotationAxisSpreadWitness rotation)
    (axisNonzero : witness.axis ≠ Coordinates3.Vector.zero) :
    let plane : Polarity.PlaneNormal K := ⟨witness.axis, axisNonzero⟩
    plane.act rotation = plane := by
  apply PlaneNormal.ext
  change Matrix3.rowMul witness.axis rotation.matrix = witness.axis
  cases witness.chart with
  | affine notHalfTurn defined matrixEq =>
      rw [matrixEq]
      exact rowMul_self_cap witness.axis defined
  | halfTurn halfTurnSpread axisNonNull matrixEq =>
      rw [matrixEq]
      exact rowMul_self_halfTurn witness.axis axisNonNull

end Purelib.Geometry.Projective.Space3.Polarity.PlaneNormal.RotationAxisSpreadWitness

namespace Purelib.Geometry.Projective.Space3.Polarity.PlaneNormal

/-- Dual of Theorem 31 in its uniform canonical form: the spread between a plane and its rotated image is the rotation's
second spread polynomial. -/
theorem canonical_plane_spread [DecidableEq K] (rotation
  : Rotations.Basic.Rotation K)
    (twoNonzero : (2 : K) ≠ 0) :
    let normal := Recovery.canonicalRotationSpreadDirection rotation twoNonzero
    let normalNonNull :=
      Recovery.canonicalRotationSpreadDirection_nonNull rotation twoNonzero
    let plane : Polarity.PlaneNormal K :=
      ⟨normal, Polarity.Vector.ne_zero_of_quadrance_ne_zero normalNonNull⟩
    plane.spread (plane.act rotation) normalNonNull
        (plane.act_nonNull rotation normalNonNull) =
      Spread.rotationSpread rotation := by
  exact Recovery.rotationSpreadAt_canonical rotation twoNonzero

/-- The same dual theorem with the second spread polynomial displayed literally. -/
theorem canonical_plane_spread_eq_halfSpreadPolynomial
  [DecidableEq K]
    (rotation : Rotations.Basic.Rotation K) (twoNonzero : (2 : K) ≠ 0) :
    let normal := Recovery.canonicalRotationSpreadDirection rotation twoNonzero
    let normalNonNull :=
      Recovery.canonicalRotationSpreadDirection_nonNull rotation twoNonzero
    let plane : Polarity.PlaneNormal K :=
      ⟨normal, Polarity.Vector.ne_zero_of_quadrance_ne_zero normalNonNull⟩
    plane.spread (plane.act rotation) normalNonNull
        (plane.act_nonNull rotation normalNonNull) =
      4 * Spread.halfSpread rotation * (1 - Spread.halfSpread rotation) := by
  exact Recovery.rotationSpreadAt_canonical_eq_halfSpreadPolynomial rotation twoNonzero

/-- Full dual of Theorem 31: every supplied non-null plane whose normal is perpendicular to the canonical rotation axis
has the same plane displacement spread. -/
theorem spread_of_normal_perpendicular_canonicalAxis
  [DecidableEq K]
    (rotation : Rotations.Basic.Rotation K) (twoNonzero : (2 : K) ≠ 0)
    (plane : Polarity.PlaneNormal K) (normalNonNull : plane.IsNonNull)
    (perpendicular : plane.normal.Perpendicular
      (Recovery.canonicalRotationAxis rotation twoNonzero)) :
    plane.spread (plane.act rotation) normalNonNull
        (plane.act_nonNull rotation normalNonNull) =
      Spread.rotationSpread rotation :=
  Recovery.rotationSpreadAt_canonicalAxis rotation twoNonzero plane.normal
    normalNonNull perpendicular

/-- The plane displacement spread is independent of which admissible perpendicular normal is supplied. -/
theorem spread_independent_of_perpendicular_normals
  [DecidableEq K]
    (rotation : Rotations.Basic.Rotation K) (twoNonzero : (2 : K) ≠ 0)
    (first second : Polarity.PlaneNormal K)
    (firstNonNull : first.IsNonNull) (secondNonNull : second.IsNonNull)
    (firstPerpendicular : first.normal.Perpendicular
      (Recovery.canonicalRotationAxis rotation twoNonzero))
    (secondPerpendicular : second.normal.Perpendicular
      (Recovery.canonicalRotationAxis rotation twoNonzero)) :
    first.spread (first.act rotation) firstNonNull
        (first.act_nonNull rotation firstNonNull) =
      second.spread (second.act rotation) secondNonNull
        (second.act_nonNull rotation secondNonNull) := by
  rw [spread_of_normal_perpendicular_canonicalAxis rotation twoNonzero
    first
      firstNonNull firstPerpendicular,
    spread_of_normal_perpendicular_canonicalAxis rotation twoNonzero
      second
      secondNonNull secondPerpendicular]

end Purelib.Geometry.Projective.Space3.Polarity.PlaneNormal

end

end

end

end
