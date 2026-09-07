import RationalRotations.AnchorProducts
import RationalRotations.Handedness

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

namespace RationalRotations

variable {K : Type*} [RFAP.ExplicitField K]

/-- A projective point represented by a displayed nonzero vector. -/
@[ext]
structure ProjectivePoint (K : Type*) [RFAP.ExplicitField K] where
  coordinates : Vector K
  nonzero : coordinates ≠ Vector.zero

/-- A projective plane through the origin, represented by a displayed
nonzero normal covector. -/
@[ext]
structure PlaneNormal (K : Type*) [RFAP.ExplicitField K] where
  normal : Vector K
  nonzero : normal ≠ Vector.zero

/-- A non-null vector is in particular a nonzero displayed vector. -/
theorem Vector.ne_zero_of_quadrance_ne_zero {vector : Vector K}
    (nonNull : vector.quadrance ≠ 0) : vector ≠ Vector.zero := by
  intro vectorZero
  apply nonNull
  rw [vectorZero, Vector.quadrance_zero]

/-- A displayed nonzero vector supplies the nontriviality needed for an
explicit nonzero projective scale. -/
theorem one_ne_zero_of_vector_ne_zero (vector : Vector K)
    (nonzero : vector ≠ Vector.zero) : (1 : K) ≠ 0 := by
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

/-- A rotation cannot send a displayed nonzero vector to zero. -/
theorem rowMul_rotation_ne_zero (rotation : Rotation K) (vector : Vector K)
    (nonzero : vector ≠ Vector.zero) :
    Matrix3.rowMul vector rotation.matrix ≠ Vector.zero := by
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
    _ = Matrix3.rowMul Vector.zero (Matrix3.transpose rotation.matrix) := by
      rw [imageZero]
    _ = Vector.zero := by
      ext <;> unfold Matrix3.rowMul Vector.zero <;> ring1

/-- Orthogonal action preserves the spread expression on two non-null
displayed directions. -/
theorem Vector.spread_rowMul_rotation (rotation : Rotation K)
    (left right : Vector K)
    (leftNonNull : left.quadrance ≠ 0)
    (rightNonNull : right.quadrance ≠ 0) :
    Vector.spread (Matrix3.rowMul left rotation.matrix)
        (Matrix3.rowMul right rotation.matrix)
        (rowMul_rotation_nonNull rotation left leftNonNull)
        (rowMul_rotation_nonNull rotation right rightNonNull) =
      Vector.spread left right leftNonNull rightNonNull := by
  unfold Vector.spread
  rw [Matrix3.dot_rowMul_of_isOrthogonal rotation.orthogonal,
    quadrance_rowMul_rotation, quadrance_rowMul_rotation]

/-- The identity rotation, used to state the projective action laws over an
arbitrary explicit field. -/
def rotationIdentity : Rotation K where
  matrix := Matrix3.identity
  orthogonal := by
    unfold Matrix3.IsOrthogonal
    rw [Matrix3.transpose_identity, Matrix3.identity_mul]
  determinantOne := Matrix3.determinant_identity

namespace ProjectivePoint

/-- Projective equality of displayed points, retaining the scale witness. -/
def Equivalent (left right : ProjectivePoint K) : Prop :=
  ∃ factor : K, factor ≠ 0 ∧
    right.coordinates = Vector.scale factor left.coordinates

theorem equivalent_refl (point : ProjectivePoint K) :
    point.Equivalent point :=
  ⟨1, one_ne_zero_of_vector_ne_zero point.coordinates point.nonzero,
    (Vector.one_scale point.coordinates).symm⟩

theorem equivalent_symm {left right : ProjectivePoint K}
    (equivalent : left.Equivalent right) : right.Equivalent left := by
  rcases equivalent with ⟨factor, factorNonzero, rightValue⟩
  refine ⟨factor⁻¹, RFAP.ExplicitField.inv_ne_zero factorNonzero, ?_⟩
  have cancel : factor⁻¹ * factor = (1 : K) := by
    rw [mul_comm, RFAP.ExplicitField.mul_inv_cancel factor factorNonzero]
  calc
    left.coordinates = Vector.scale 1 left.coordinates :=
      (Vector.one_scale left.coordinates).symm
    _ = Vector.scale (factor⁻¹ * factor) left.coordinates := by
      rw [cancel]
    _ = Vector.scale factor⁻¹
        (Vector.scale factor left.coordinates) := by
      rw [Vector.scale_scale]
    _ = Vector.scale factor⁻¹ right.coordinates := by rw [rightValue]

theorem equivalent_trans {first second third : ProjectivePoint K}
    (firstSecond : first.Equivalent second)
    (secondThird : second.Equivalent third) : first.Equivalent third := by
  rcases firstSecond with ⟨firstFactor, firstNonzero, secondValue⟩
  rcases secondThird with ⟨secondFactor, secondNonzero, thirdValue⟩
  refine ⟨secondFactor * firstFactor,
    RFAP.ExplicitField.mul_ne_zero secondNonzero firstNonzero, ?_⟩
  calc
    third.coordinates = Vector.scale secondFactor second.coordinates :=
      thirdValue
    _ = Vector.scale secondFactor
        (Vector.scale firstFactor first.coordinates) := by rw [secondValue]
    _ = Vector.scale (secondFactor * firstFactor) first.coordinates :=
      Vector.scale_scale _ _ _

/-- The row-vector rotation action on a displayed projective point. -/
def act (point : ProjectivePoint K) (rotation : Rotation K) :
    ProjectivePoint K where
  coordinates := Matrix3.rowMul point.coordinates rotation.matrix
  nonzero := rowMul_rotation_ne_zero rotation point.coordinates point.nonzero

/-- Whether the displayed representative is non-null, the domain on which
the projective metric is defined. -/
def IsNonNull (point : ProjectivePoint K) : Prop :=
  point.coordinates.quadrance ≠ 0

theorem act_nonNull (point : ProjectivePoint K) (rotation : Rotation K)
    (nonNull : point.IsNonNull) : (point.act rotation).IsNonNull :=
  rowMul_rotation_nonNull rotation point.coordinates nonNull

theorem act_respects_equivalent {left right : ProjectivePoint K}
    (equivalent : left.Equivalent right) (rotation : Rotation K) :
    (left.act rotation).Equivalent (right.act rotation) := by
  rcases equivalent with ⟨factor, factorNonzero, rightValue⟩
  refine ⟨factor, factorNonzero, ?_⟩
  change Matrix3.rowMul right.coordinates rotation.matrix =
    Vector.scale factor
      (Matrix3.rowMul left.coordinates rotation.matrix)
  rw [rightValue]
  ext <;> unfold Matrix3.rowMul Vector.scale <;> ring1

@[simp] theorem act_identity (point : ProjectivePoint K) :
    point.act (rotationIdentity (K := K)) = point := by
  apply ProjectivePoint.ext
  exact Matrix3.rowMul_identity point.coordinates

theorem act_product (point : ProjectivePoint K) (left right : Rotation K) :
    (point.act left).act right = point.act (rotationProduct left right) := by
  apply ProjectivePoint.ext
  exact Matrix3.rowMul_mul point.coordinates left.matrix right.matrix

@[simp] theorem act_inverse_right (point : ProjectivePoint K)
    (rotation : Rotation K) :
    (point.act rotation).act (inverseRotation rotation) = point := by
  apply ProjectivePoint.ext
  change Matrix3.rowMul
      (Matrix3.rowMul point.coordinates rotation.matrix)
      (Matrix3.transpose rotation.matrix) = point.coordinates
  rw [Matrix3.rowMul_mul, rotation.orthogonal, Matrix3.rowMul_identity]

@[simp] theorem act_inverse_left (point : ProjectivePoint K)
    (rotation : Rotation K) :
    (point.act (inverseRotation rotation)).act rotation = point := by
  apply ProjectivePoint.ext
  change Matrix3.rowMul
      (Matrix3.rowMul point.coordinates (Matrix3.transpose rotation.matrix))
      rotation.matrix = point.coordinates
  rw [Matrix3.rowMul_mul, transpose_mul_rotation,
    Matrix3.rowMul_identity]

/-- Projective quadrance between two non-null projective points.  This is
the projective metric attached to the paper's dot product. -/
def quadrance (left right : ProjectivePoint K)
    (leftNonNull : left.IsNonNull) (rightNonNull : right.IsNonNull) : K :=
  Vector.spread left.coordinates right.coordinates leftNonNull rightNonNull

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
    Vector.spread_scale_left factor left.coordinates other.coordinates
      factorNonzero leftNonNull otherNonNull

theorem quadrance_respects_equivalent_right
    (left : ProjectivePoint K) {right third : ProjectivePoint K}
    (equivalent : right.Equivalent third)
    (leftNonNull : left.IsNonNull) (rightNonNull : right.IsNonNull)
    (thirdNonNull : third.IsNonNull) :
    left.quadrance third leftNonNull thirdNonNull =
      left.quadrance right leftNonNull rightNonNull := by
  rcases equivalent with ⟨factor, factorNonzero, thirdValue⟩
  unfold quadrance
  simpa only [thirdValue] using
    Vector.spread_scale_right factor left.coordinates right.coordinates
      factorNonzero leftNonNull rightNonNull

theorem quadrance_act (left right : ProjectivePoint K)
    (rotation : Rotation K)
    (leftNonNull : left.IsNonNull) (rightNonNull : right.IsNonNull) :
    (left.act rotation).quadrance (right.act rotation)
        (left.act_nonNull rotation leftNonNull)
        (right.act_nonNull rotation rightNonNull) =
      left.quadrance right leftNonNull rightNonNull :=
  Vector.spread_rowMul_rotation rotation left.coordinates right.coordinates
    leftNonNull rightNonNull

end ProjectivePoint

namespace PlaneNormal

/-- Projective equality of planes by a displayed nonzero normal scale. -/
def Equivalent (left right : PlaneNormal K) : Prop :=
  ∃ factor : K, factor ≠ 0 ∧
    right.normal = Vector.scale factor left.normal

theorem equivalent_refl (plane : PlaneNormal K) : plane.Equivalent plane :=
  ⟨1, one_ne_zero_of_vector_ne_zero plane.normal plane.nonzero,
    (Vector.one_scale plane.normal).symm⟩

theorem equivalent_symm {left right : PlaneNormal K}
    (equivalent : left.Equivalent right) : right.Equivalent left := by
  rcases equivalent with ⟨factor, factorNonzero, rightValue⟩
  refine ⟨factor⁻¹, RFAP.ExplicitField.inv_ne_zero factorNonzero, ?_⟩
  have cancel : factor⁻¹ * factor = (1 : K) := by
    rw [mul_comm, RFAP.ExplicitField.mul_inv_cancel factor factorNonzero]
  calc
    left.normal = Vector.scale 1 left.normal :=
      (Vector.one_scale left.normal).symm
    _ = Vector.scale (factor⁻¹ * factor) left.normal := by rw [cancel]
    _ = Vector.scale factor⁻¹ (Vector.scale factor left.normal) := by
      rw [Vector.scale_scale]
    _ = Vector.scale factor⁻¹ right.normal := by rw [rightValue]

theorem equivalent_trans {first second third : PlaneNormal K}
    (firstSecond : first.Equivalent second)
    (secondThird : second.Equivalent third) : first.Equivalent third := by
  rcases firstSecond with ⟨firstFactor, firstNonzero, secondValue⟩
  rcases secondThird with ⟨secondFactor, secondNonzero, thirdValue⟩
  refine ⟨secondFactor * firstFactor,
    RFAP.ExplicitField.mul_ne_zero secondNonzero firstNonzero, ?_⟩
  calc
    third.normal = Vector.scale secondFactor second.normal := thirdValue
    _ = Vector.scale secondFactor
        (Vector.scale firstFactor first.normal) := by rw [secondValue]
    _ = Vector.scale (secondFactor * firstFactor) first.normal :=
      Vector.scale_scale _ _ _

/-- Contravariant plane action.  In the row-vector orthogonal convention its
normal transforms by the same displayed rotation matrix: simultaneous point
and normal action preserves their dot product. -/
def act (plane : PlaneNormal K) (rotation : Rotation K) : PlaneNormal K where
  normal := Matrix3.rowMul plane.normal rotation.matrix
  nonzero := rowMul_rotation_ne_zero rotation plane.normal plane.nonzero

/-- Any displayed fixed vector gives the corresponding exactly fixed polar
plane.  This is the direct adapter for fixed-axis theorems throughout the
paper. -/
theorem fixed_of_normal_fixed (rotation : Rotation K) (plane : PlaneNormal K)
    (fixed : Matrix3.rowMul plane.normal rotation.matrix = plane.normal) :
    plane.act rotation = plane := by
  apply PlaneNormal.ext
  exact fixed

/-- Whether the normal is non-null, the domain on which plane spread is
defined. -/
def IsNonNull (plane : PlaneNormal K) : Prop := plane.normal.quadrance ≠ 0

theorem act_nonNull (plane : PlaneNormal K) (rotation : Rotation K)
    (nonNull : plane.IsNonNull) : (plane.act rotation).IsNonNull :=
  rowMul_rotation_nonNull rotation plane.normal nonNull

theorem act_preserves_quadrance (plane : PlaneNormal K)
    (rotation : Rotation K) :
    (plane.act rotation).normal.quadrance = plane.normal.quadrance :=
  quadrance_rowMul_rotation rotation plane.normal

theorem act_respects_equivalent {left right : PlaneNormal K}
    (equivalent : left.Equivalent right) (rotation : Rotation K) :
    (left.act rotation).Equivalent (right.act rotation) := by
  rcases equivalent with ⟨factor, factorNonzero, rightValue⟩
  refine ⟨factor, factorNonzero, ?_⟩
  change Matrix3.rowMul right.normal rotation.matrix =
    Vector.scale factor (Matrix3.rowMul left.normal rotation.matrix)
  rw [rightValue]
  ext <;> unfold Matrix3.rowMul Vector.scale <;> ring1

@[simp] theorem act_identity (plane : PlaneNormal K) :
    plane.act (rotationIdentity (K := K)) = plane := by
  apply PlaneNormal.ext
  exact Matrix3.rowMul_identity plane.normal

theorem act_product (plane : PlaneNormal K) (left right : Rotation K) :
    (plane.act left).act right = plane.act (rotationProduct left right) := by
  apply PlaneNormal.ext
  exact Matrix3.rowMul_mul plane.normal left.matrix right.matrix

@[simp] theorem act_inverse_right (plane : PlaneNormal K)
    (rotation : Rotation K) :
    (plane.act rotation).act (inverseRotation rotation) = plane := by
  apply PlaneNormal.ext
  change Matrix3.rowMul (Matrix3.rowMul plane.normal rotation.matrix)
      (Matrix3.transpose rotation.matrix) = plane.normal
  rw [Matrix3.rowMul_mul, rotation.orthogonal, Matrix3.rowMul_identity]

@[simp] theorem act_inverse_left (plane : PlaneNormal K)
    (rotation : Rotation K) :
    (plane.act (inverseRotation rotation)).act rotation = plane := by
  apply PlaneNormal.ext
  change Matrix3.rowMul
      (Matrix3.rowMul plane.normal (Matrix3.transpose rotation.matrix))
      rotation.matrix = plane.normal
  rw [Matrix3.rowMul_mul, transpose_mul_rotation,
    Matrix3.rowMul_identity]

/-- Projective spread between two non-null planes, computed from their
normal covectors. -/
def spread (left right : PlaneNormal K)
    (leftNonNull : left.IsNonNull) (rightNonNull : right.IsNonNull) : K :=
  Vector.spread left.normal right.normal leftNonNull rightNonNull

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
    Vector.spread_scale_left factor left.normal other.normal
      factorNonzero leftNonNull otherNonNull

theorem spread_respects_equivalent_right
    (left : PlaneNormal K) {right third : PlaneNormal K}
    (equivalent : right.Equivalent third)
    (leftNonNull : left.IsNonNull) (rightNonNull : right.IsNonNull)
    (thirdNonNull : third.IsNonNull) :
    left.spread third leftNonNull thirdNonNull =
      left.spread right leftNonNull rightNonNull := by
  rcases equivalent with ⟨factor, factorNonzero, thirdValue⟩
  unfold spread
  simpa only [thirdValue] using
    Vector.spread_scale_right factor left.normal right.normal
      factorNonzero leftNonNull rightNonNull

theorem spread_act (left right : PlaneNormal K) (rotation : Rotation K)
    (leftNonNull : left.IsNonNull) (rightNonNull : right.IsNonNull) :
    (left.act rotation).spread (right.act rotation)
        (left.act_nonNull rotation leftNonNull)
        (right.act_nonNull rotation rightNonNull) =
      left.spread right leftNonNull rightNonNull :=
  Vector.spread_rowMul_rotation rotation left.normal right.normal
    leftNonNull rightNonNull

end PlaneNormal

/-! ## The polarity and its metrical laws -/

namespace ProjectivePoint

/-- The polar plane whose normal has the displayed point coordinates. -/
def dual (point : ProjectivePoint K) : PlaneNormal K where
  normal := point.coordinates
  nonzero := point.nonzero

@[simp] theorem dual_normal (point : ProjectivePoint K) :
    point.dual.normal = point.coordinates := rfl

end ProjectivePoint

namespace PlaneNormal

/-- The pole whose displayed coordinates are the plane normal. -/
def dual (plane : PlaneNormal K) : ProjectivePoint K where
  coordinates := plane.normal
  nonzero := plane.nonzero

@[simp] theorem dual_coordinates (plane : PlaneNormal K) :
    plane.dual.coordinates = plane.normal := rfl

end PlaneNormal

@[simp] theorem ProjectivePoint.dual_dual (point : ProjectivePoint K) :
    point.dual.dual = point := rfl

@[simp] theorem PlaneNormal.dual_dual (plane : PlaneNormal K) :
    plane.dual.dual = plane := rfl

theorem ProjectivePoint.dual_equivalent_iff
    (left right : ProjectivePoint K) :
    left.dual.Equivalent right.dual ↔ left.Equivalent right := by
  rfl

theorem PlaneNormal.dual_equivalent_iff (left right : PlaneNormal K) :
    left.dual.Equivalent right.dual ↔ left.Equivalent right := by
  rfl

@[simp] theorem ProjectivePoint.dual_act (point : ProjectivePoint K)
    (rotation : Rotation K) :
    (point.act rotation).dual = point.dual.act rotation := rfl

@[simp] theorem PlaneNormal.dual_act (plane : PlaneNormal K)
    (rotation : Rotation K) :
    (plane.act rotation).dual = plane.dual.act rotation := rfl

theorem ProjectivePoint.dual_nonNull_iff (point : ProjectivePoint K) :
    point.dual.IsNonNull ↔ point.IsNonNull := by rfl

theorem PlaneNormal.dual_nonNull_iff (plane : PlaneNormal K) :
    plane.dual.IsNonNull ↔ plane.IsNonNull := by rfl

/-- The central metric clause of Problem 72: projective quadrance of points
is spread of their polar planes. -/
theorem projectiveQuadrance_eq_dualPlaneSpread
    (left right : ProjectivePoint K)
    (leftNonNull : left.IsNonNull) (rightNonNull : right.IsNonNull) :
    left.quadrance right leftNonNull rightNonNull =
      left.dual.spread right.dual leftNonNull rightNonNull := rfl

/-- The inverse metric clause: plane spread is the projective quadrance of
the corresponding poles. -/
theorem planeSpread_eq_dualPointQuadrance
    (left right : PlaneNormal K)
    (leftNonNull : left.IsNonNull) (rightNonNull : right.IsNonNull) :
    left.spread right leftNonNull rightNonNull =
      left.dual.quadrance right.dual leftNonNull rightNonNull := rfl

namespace ProjectivePoint

/-- Incidence of a projective point with a plane through the origin. -/
def Incident (point : ProjectivePoint K) (plane : PlaneNormal K) : Prop :=
  Vector.dot point.coordinates plane.normal = 0

theorem incident_polar_iff_perpendicular
    (left right : ProjectivePoint K) :
    left.Incident right.dual ↔ left.coordinates.Perpendicular right.coordinates :=
  Iff.rfl

theorem incident_dual_symmetric (left right : ProjectivePoint K) :
    left.Incident right.dual ↔ right.Incident left.dual := by
  change Vector.dot left.coordinates right.coordinates = 0 ↔
    Vector.dot right.coordinates left.coordinates = 0
  rw [Vector.dot_comm]

theorem incident_of_equivalent_point {left right : ProjectivePoint K}
    (equivalent : left.Equivalent right) (plane : PlaneNormal K)
    (incident : left.Incident plane) : right.Incident plane := by
  rcases equivalent with ⟨factor, _factorNonzero, rightValue⟩
  unfold Incident at incident ⊢
  rw [rightValue, Vector.dot_scale_left, incident, mul_zero]

theorem incident_respects_equivalent_point
    {left right : ProjectivePoint K} (equivalent : left.Equivalent right)
    (plane : PlaneNormal K) : left.Incident plane ↔ right.Incident plane := by
  constructor
  · exact incident_of_equivalent_point equivalent plane
  · exact incident_of_equivalent_point
      (ProjectivePoint.equivalent_symm equivalent) plane

theorem incident_of_equivalent_plane (point : ProjectivePoint K)
    {left right : PlaneNormal K} (equivalent : left.Equivalent right)
    (incident : point.Incident left) : point.Incident right := by
  rcases equivalent with ⟨factor, _factorNonzero, rightValue⟩
  unfold Incident at incident ⊢
  rw [rightValue, Vector.dot_scale_right, incident, mul_zero]

theorem incident_respects_equivalent_plane (point : ProjectivePoint K)
    {left right : PlaneNormal K} (equivalent : left.Equivalent right) :
    point.Incident left ↔ point.Incident right := by
  constructor
  · exact incident_of_equivalent_plane point equivalent
  · exact incident_of_equivalent_plane point
      (PlaneNormal.equivalent_symm equivalent)

/-- Simultaneous rotation of a point and plane preserves incidence. -/
theorem incident_act_iff (point : ProjectivePoint K) (plane : PlaneNormal K)
    (rotation : Rotation K) :
    (point.act rotation).Incident (plane.act rotation) ↔
      point.Incident plane := by
  unfold Incident act PlaneNormal.act
  rw [Matrix3.dot_rowMul_of_isOrthogonal rotation.orthogonal]

end ProjectivePoint

/-! ## Constructive theorem-level translation -/

/-- A theorem schema about a projective point and its rotated image.  All
other parameters and hypotheses can be closed over by `property`. -/
def PointActionStatement (rotation : Rotation K)
    (property : Vector K → Vector K → Prop) : Prop :=
  ∀ point : ProjectivePoint K,
    property point.coordinates (point.act rotation).coordinates

/-- The plane-normal dual of `PointActionStatement`. -/
def PlaneActionStatement (rotation : Rotation K)
    (property : Vector K → Vector K → Prop) : Prop :=
  ∀ plane : PlaneNormal K,
    property plane.normal (plane.act rotation).normal

/-- Every unary theorem about rotation acting on projective points is
equivalent, constructively, to its derived theorem about plane normals. -/
theorem pointActionStatement_iff_planeActionStatement
    (rotation : Rotation K) (property : Vector K → Vector K → Prop) :
    PointActionStatement rotation property ↔
      PlaneActionStatement rotation property := by
  constructor
  · intro pointTheorem plane
    exact pointTheorem plane.dual
  · intro planeTheorem point
    exact planeTheorem point.dual

/-- Apply any existing raw-vector action theorem directly to displayed plane
normals.  This is the entry point for the paper's already formalized vector
theorems. -/
theorem planeActionStatement_of_vectorActionTheorem
    (rotation : Rotation K) (property : Vector K → Vector K → Prop)
    (vectorTheorem : ∀ vector : Vector K,
      property vector (Matrix3.rowMul vector rotation.matrix)) :
    PlaneActionStatement rotation property := by
  intro plane
  exact vectorTheorem plane.normal

/-- A theorem schema about two projective points and both rotated images. -/
def PointPairActionStatement (rotation : Rotation K)
    (property : Vector K → Vector K → Vector K → Vector K → Prop) :
    Prop :=
  ∀ left right : ProjectivePoint K,
    property left.coordinates right.coordinates
      (left.act rotation).coordinates (right.act rotation).coordinates

/-- The plane-normal dual of `PointPairActionStatement`. -/
def PlanePairActionStatement (rotation : Rotation K)
    (property : Vector K → Vector K → Vector K → Vector K → Prop) :
    Prop :=
  ∀ left right : PlaneNormal K,
    property left.normal right.normal
      (left.act rotation).normal (right.act rotation).normal

/-- Every binary theorem about simultaneous rotation of projective points is
equivalent to its plane theorem.  In particular this transports all metrical
relations expressible on two displayed representatives. -/
theorem pointPairActionStatement_iff_planePairActionStatement
    (rotation : Rotation K)
    (property : Vector K → Vector K → Vector K → Vector K → Prop) :
    PointPairActionStatement rotation property ↔
      PlanePairActionStatement rotation property := by
  constructor
  · intro pointTheorem left right
    exact pointTheorem left.dual right.dual
  · intro planeTheorem left right
    exact planeTheorem left.dual right.dual

/-- Apply any existing two-vector action theorem to two displayed plane
normals. -/
theorem planePairActionStatement_of_vectorActionTheorem
    (rotation : Rotation K)
    (property : Vector K → Vector K → Vector K → Vector K → Prop)
    (vectorTheorem : ∀ left right : Vector K,
      property left right
        (Matrix3.rowMul left rotation.matrix)
        (Matrix3.rowMul right rotation.matrix)) :
    PlanePairActionStatement rotation property := by
  intro left right
  exact vectorTheorem left.normal right.normal

/-- The completed finite content of Problem 72, packaged as one audited
interface: involutive polarity, rotation equivariance, incidence invariance,
quadrance--spread correspondence, and theorem-level unary and binary
translation. -/
structure ProblemSeventyTwoSolution (K : Type*) [RFAP.ExplicitField K] where
  pointRoundTrip : ∀ point : ProjectivePoint K, point.dual.dual = point
  planeRoundTrip : ∀ plane : PlaneNormal K, plane.dual.dual = plane
  actionEquivariant : ∀ (point : ProjectivePoint K) (rotation : Rotation K),
    (point.act rotation).dual = point.dual.act rotation
  incidenceInvariant : ∀ (point : ProjectivePoint K) (plane : PlaneNormal K)
    (rotation : Rotation K),
    (point.act rotation).Incident (plane.act rotation) ↔ point.Incident plane
  metricCorrespondence : ∀ (left right : ProjectivePoint K)
    (leftNonNull : left.IsNonNull) (rightNonNull : right.IsNonNull),
    left.quadrance right leftNonNull rightNonNull =
      left.dual.spread right.dual leftNonNull rightNonNull
  unaryTranslation : ∀ (rotation : Rotation K)
    (property : Vector K → Vector K → Prop),
    PointActionStatement rotation property ↔
      PlaneActionStatement rotation property
  binaryTranslation : ∀ (rotation : Rotation K)
    (property : Vector K → Vector K → Vector K → Vector K → Prop),
    PointPairActionStatement rotation property ↔
      PlanePairActionStatement rotation property

/-- The constructive solution of Problem 72. -/
theorem problemSeventyTwoSolution : ProblemSeventyTwoSolution K where
  pointRoundTrip := ProjectivePoint.dual_dual
  planeRoundTrip := PlaneNormal.dual_dual
  actionEquivariant := ProjectivePoint.dual_act
  incidenceInvariant := ProjectivePoint.incident_act_iff
  metricCorrespondence := projectiveQuadrance_eq_dualPlaneSpread
  unaryTranslation := pointActionStatement_iff_planeActionStatement
  binaryTranslation := pointPairActionStatement_iff_planePairActionStatement

/-! ## Duals of the paper's principal vector-action theorems -/

namespace PlaneNormal

/-- Dual of Theorem 17's fixed-axis clause: the half turn fixes the plane
whose normal is its axis. -/
theorem halfTurn_axis_plane_fixed (axis : Vector K)
    (axisNonNull : axis.quadrance ≠ 0) :
    let plane : PlaneNormal K :=
      ⟨axis, Vector.ne_zero_of_quadrance_ne_zero axisNonNull⟩
    plane.act (halfTurnRotation axis axisNonNull) = plane := by
  apply PlaneNormal.ext
  exact rowMul_self_halfTurn axis axisNonNull

/-- Dual of Theorem 17's perpendicular clause: a half turn negates a
perpendicular normal, hence fixes the corresponding projective plane. -/
theorem halfTurn_perpendicular_plane_equivalent (axis : Vector K)
    (axisNonNull : axis.quadrance ≠ 0) (twoNonzero : (2 : K) ≠ 0)
    (plane : PlaneNormal K) (perpendicular : plane.normal.Perpendicular axis) :
    plane.Equivalent (plane.act (halfTurnRotation axis axisNonNull)) := by
  have oneNonzero : (1 : K) ≠ 0 :=
    one_ne_zero_of_vector_ne_zero plane.normal plane.nonzero
  refine ⟨-1, neg_ne_zero.mpr oneNonzero, ?_⟩
  change Matrix3.rowMul plane.normal (halfTurn axis axisNonNull) =
    Vector.scale (-1) plane.normal
  rw [rowMul_halfTurn_of_perpendicular axis axisNonNull twoNonzero
    plane.normal perpendicular]
  ext <;> unfold Vector.neg Vector.scale <;> ring1

/-- Dual of Theorem 19: the plane normal to the cross-product axis is fixed
by the product of the two reflections. -/
theorem reflectionProduct_axis_plane_fixed
    (first second : Vector K)
    (firstNonNull : first.quadrance ≠ 0)
    (secondNonNull : second.quadrance ≠ 0)
    (independent : first.Independent second)
    (twoNonzero : (2 : K) ≠ 0) :
    let plane : PlaneNormal K := ⟨Vector.cross first second, independent⟩
    plane.act (reflectionProductRotation first second firstNonNull secondNonNull) =
      plane := by
  apply PlaneNormal.ext
  exact rowMul_cross_reflection_product first second firstNonNull secondNonNull
    twoNonzero

/-- Dual of Theorem 24.2: a cap fixes the plane normal to its anchor. -/
theorem cap_axis_plane_fixed (axis : Vector K)
    (axisNonzero : axis ≠ Vector.zero)
    (defined : capDenominator axis ≠ 0) :
    let plane : PlaneNormal K := ⟨axis, axisNonzero⟩
    plane.act (capRotation axis defined) = plane := by
  apply PlaneNormal.ext
  exact rowMul_self_cap axis defined

/-- Dual of Theorem 35.3: away from the half-turn chart, the recovered
anchor is the normal of a fixed plane. -/
theorem recoveredAnchor_plane_fixed (rotation : Rotation K)
    (notHalfTurn : halfSpread rotation ≠ 1)
    (twoNonzero : (2 : K) ≠ 0)
    (axisNonzero : rotationAnchorVector rotation notHalfTurn ≠ Vector.zero) :
    let plane : PlaneNormal K :=
      ⟨rotationAnchorVector rotation notHalfTurn, axisNonzero⟩
    plane.act rotation = plane := by
  apply PlaneNormal.ext
  exact rowMul_rotationAnchorVector rotation notHalfTurn twoNonzero

/-- The dual of the uniform fixed-axis result cached by the canonical
axis/spread wrapper.  The identity branch has zero canonical axis, so a
nonzero hypothesis is exactly what is needed to obtain a projective plane. -/
theorem RotationAxisSpreadWitness.axis_plane_fixed
    {rotation : Rotation K} (witness : RotationAxisSpreadWitness rotation)
    (axisNonzero : witness.axis ≠ Vector.zero) :
    let plane : PlaneNormal K := ⟨witness.axis, axisNonzero⟩
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

/-- Dual of Theorem 31 in its uniform canonical form: the spread between a
plane and its rotated image is the rotation's second spread polynomial. -/
theorem canonical_plane_spread [DecidableEq K] (rotation : Rotation K)
    (twoNonzero : (2 : K) ≠ 0) :
    let normal := canonicalRotationSpreadDirection rotation twoNonzero
    let normalNonNull :=
      canonicalRotationSpreadDirection_nonNull rotation twoNonzero
    let plane : PlaneNormal K :=
      ⟨normal, Vector.ne_zero_of_quadrance_ne_zero normalNonNull⟩
    plane.spread (plane.act rotation) normalNonNull
        (plane.act_nonNull rotation normalNonNull) =
      rotationSpread rotation := by
  exact rotationSpreadAt_canonical rotation twoNonzero

/-- The same dual theorem with the second spread polynomial displayed
literally. -/
theorem canonical_plane_spread_eq_halfSpreadPolynomial [DecidableEq K]
    (rotation : Rotation K) (twoNonzero : (2 : K) ≠ 0) :
    let normal := canonicalRotationSpreadDirection rotation twoNonzero
    let normalNonNull :=
      canonicalRotationSpreadDirection_nonNull rotation twoNonzero
    let plane : PlaneNormal K :=
      ⟨normal, Vector.ne_zero_of_quadrance_ne_zero normalNonNull⟩
    plane.spread (plane.act rotation) normalNonNull
        (plane.act_nonNull rotation normalNonNull) =
      4 * halfSpread rotation * (1 - halfSpread rotation) := by
  exact rotationSpreadAt_canonical_eq_halfSpreadPolynomial rotation twoNonzero

/-- Full dual of Theorem 31: every supplied non-null plane whose normal is
perpendicular to the canonical rotation axis has the same plane displacement
spread. -/
theorem spread_of_normal_perpendicular_canonicalAxis [DecidableEq K]
    (rotation : Rotation K) (twoNonzero : (2 : K) ≠ 0)
    (plane : PlaneNormal K) (normalNonNull : plane.IsNonNull)
    (perpendicular : plane.normal.Perpendicular
      (canonicalRotationAxis rotation twoNonzero)) :
    plane.spread (plane.act rotation) normalNonNull
        (plane.act_nonNull rotation normalNonNull) =
      rotationSpread rotation :=
  rotationSpreadAt_canonicalAxis rotation twoNonzero plane.normal
    normalNonNull perpendicular

/-- The plane displacement spread is independent of which admissible
perpendicular normal is supplied. -/
theorem spread_independent_of_perpendicular_normals [DecidableEq K]
    (rotation : Rotation K) (twoNonzero : (2 : K) ≠ 0)
    (first second : PlaneNormal K)
    (firstNonNull : first.IsNonNull) (secondNonNull : second.IsNonNull)
    (firstPerpendicular : first.normal.Perpendicular
      (canonicalRotationAxis rotation twoNonzero))
    (secondPerpendicular : second.normal.Perpendicular
      (canonicalRotationAxis rotation twoNonzero)) :
    first.spread (first.act rotation) firstNonNull
        (first.act_nonNull rotation firstNonNull) =
      second.spread (second.act rotation) secondNonNull
        (second.act_nonNull rotation secondNonNull) := by
  rw [spread_of_normal_perpendicular_canonicalAxis rotation twoNonzero first
      firstNonNull firstPerpendicular,
    spread_of_normal_perpendicular_canonicalAxis rotation twoNonzero second
      secondNonNull secondPerpendicular]

end PlaneNormal

end RationalRotations
