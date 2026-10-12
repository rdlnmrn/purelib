module

public import Purelib.Algebra.Quadratic.Ternary.Lorentz
public import Purelib.Algebra.Clifford.Ternary.Basic
public import Purelib.Geometry.Quadratic.Ternary.Spread
import Purelib.Algebra.Field.ExplicitField
public import Purelib.LinearAlgebra.Coordinates3.Antisymmetric
import Purelib.LinearAlgebra.Coordinates3.Matrix
import Purelib.LinearAlgebra.Coordinates3.Vector
import Purelib.Tactic.Ring

/-!
# Vector and anchor algebra of the time-first Lorentz form

The signed cross product and metrical anchor use the original Lorentz form
and its cached adjugate. Their identities connect the time-first coordinate
convention to the general ternary Clifford algebra.
-/

public section

namespace Purelib.Geometry.Quadratic.Ternary.Lorentz

open Purelib.Algebra.Field (ExplicitField)
open Purelib.Algebra.Quadratic.Ternary.Basic renaming TernaryForm -> Form
open Purelib.LinearAlgebra
open Purelib.LinearAlgebra.Coordinates3 (Matrix3)
open Purelib.LinearAlgebra.Coordinates3 renaming Vector -> Vector3

variable {K : Type*} [ExplicitField K] (oneNonzero : (1 : K) ≠ 0)

/-- A time-first Lorentz vector is timelike when its original quadrance is positive. -/
@[expose] def IsTimelike [LT K] (vector : Vector3 K) : Prop :=
  0 < (Form.lorentz oneNonzero).quadrance vector

/-- A time-first Lorentz vector is spacelike when its original quadrance is negative. -/
@[expose] def IsSpacelike [LT K] (vector : Vector3 K) : Prop :=
  (Form.lorentz oneNonzero).quadrance vector < 0

/-- Multiplying both spatial coordinates by an imaginary unit converts Lorentz quadrance to Euclidean quadrance.

The supplied scalar squares to negative one. The same time coordinate and
the two scaled spatial coordinates are retained explicitly, so the identity
compares the original time-first Lorentz form with the original vector quadrance.
-/
theorem quadrance_spatial_imaginary (i : K) (iSquare : i ^ 2 = -1) (vector : Vector3 K) :
    (Form.lorentz oneNonzero).quadrance ⟨vector.t, i * vector.r, i * vector.s⟩ = vector.quadrance := by
  rw [Form.quadrance_lorentz]
  calc
    vector.t ^ 2 - (i * vector.r) ^ 2 - (i * vector.s) ^ 2 =
        vector.quadrance - (i ^ 2 + 1) * (vector.r ^ 2 + vector.s ^ 2) := by
      unfold Vector3.quadrance Vector3.dot
      ring1
    _ = vector.quadrance := by rw [iSquare]; ring1

/-- Construct a time-first Lorentz vector of any prescribed quadrance.

The first two coordinates are `(value+1)/2` and `(value-1)/2`, and the
third is zero. The difference-of-squares identity proves the requested
quadrance using only the supplied nonzero-two certificate.
-/
@[expose] def quadranceWitness (twoNonzero : (2 : K) ≠ 0) (value : K) :
    Σ' vector : Vector3 K, (Form.lorentz oneNonzero).quadrance vector = value := by
  refine ⟨⟨(value + 1) / 2, (value - 1) / 2, 0⟩, ?_⟩
  rw [Form.quadrance_lorentz]
  calc
    _ = value * (2 * (2 : K)⁻¹) ^ 2 := by
      simp only [ExplicitField.div_eq_mul_inv]
      ring1
    _ = value := by rw [ExplicitField.mul_inv_cancel 2 twoNonzero]; ring1

/-- The Lorentz adjoint conjugates the transpose by the time-first metric. -/
@[expose] def adjoint (matrix : Matrix3 K) : Matrix3 K :=
  Matrix3.mul (Matrix3.mul (Form.lorentz oneNonzero).matrix (Matrix3.transpose matrix))
    (Form.lorentz oneNonzero).matrix

/-- The Lorentz adjoint preserves diagonal entries and signs the mixed time entries. -/
theorem adjoint_coordinates (matrix : Matrix3 K) :
    adjoint oneNonzero matrix =
      ⟨matrix.tt, -matrix.rt, -matrix.st, -matrix.tr, matrix.rr, matrix.sr,
        -matrix.ts, matrix.rs, matrix.ss⟩ := by
  ext <;> unfold adjoint Form.lorentz Form.ofMatrix Matrix3.mul Matrix3.transpose <;> ring1

/-- Applying the Lorentz adjoint twice recovers the matrix. -/
theorem adjoint_adjoint (matrix : Matrix3 K) :
    adjoint oneNonzero (adjoint oneNonzero matrix) = matrix := by
  rw [adjoint_coordinates, adjoint_coordinates]
  ext <;> dsimp <;> ring1

/-- The Lorentz adjoint commutes with matrix negation. -/
theorem adjoint_neg (matrix : Matrix3 K) :
    adjoint oneNonzero (Matrix3.neg matrix) = Matrix3.neg (adjoint oneNonzero matrix) := by
  rw [adjoint_coordinates, adjoint_coordinates]
  ext <;> unfold Matrix3.neg <;> ring1

/-- The Lorentz adjoint reverses matrix multiplication.

The metric is its own inverse, so the two middle metric factors cancel when
forming the product of the adjoints in reverse order.
-/
theorem adjoint_mul (left right : Matrix3 K) :
    adjoint oneNonzero (Matrix3.mul left right) =
      Matrix3.mul (adjoint oneNonzero right) (adjoint oneNonzero left) := by
  rw [adjoint_coordinates, adjoint_coordinates, adjoint_coordinates]
  ext <;> unfold Matrix3.mul <;> ring1

/-- A Lorentz anchor is a matrix whose metrical adjoint is its negative. -/
@[expose] def IsAnchor (matrix : Matrix3 K) : Prop :=
  adjoint oneNonzero matrix = Matrix3.neg matrix

/-- The Lorentz cross product is the negative of the form's adjugate cross.

This convention gives the row-action anchor its original upper-triangular
coordinates and makes the scalar triple product the negative determinant.
-/
@[expose] def cross (left right : Vector3 K) : Vector3 K :=
  Vector3.neg ((Form.lorentz oneNonzero).cliffordCross left right)

/-- The signed Lorentz cross has its three displayed coordinate differences. -/
theorem cross_coordinates (left right : Vector3 K) :
    cross oneNonzero left right =
      ⟨right.r * left.s - left.r * right.s,
        left.s * right.t - left.t * right.s, left.t * right.r - left.r * right.t⟩ := by
  unfold cross Form.cliffordCross
  rw [Form.lorentz_adjugate]
  ext <;> unfold Vector3.neg Vector3.cross Matrix3.rowMul <;> ring1

/-- Swapping the two source vectors negates their signed Lorentz cross product. -/
theorem cross_anticomm (left right : Vector3 K) :
    cross oneNonzero right left = Vector3.neg (cross oneNonzero left right) := by
  unfold cross
  rw [Form.cliffordCross_anticomm]

/-- Pairing the Lorentz cross with a third vector gives the negative determinant. -/
theorem scalar_triple_product (first second third : Vector3 K) :
    (Form.lorentz oneNonzero).bilinear (cross oneNonzero first second) third =
      -Vector3.determinant first second third := by
  unfold cross
  rw [Form.bilinear_neg_left, Form.bilinear_cliffordCross, Form.lorentz_determinant, one_mul]

/-- The Lorentz cross is perpendicular to its left input. -/
theorem cross_perpendicular_left (left right : Vector3 K) :
    (Form.lorentz oneNonzero).Perpendicular (cross oneNonzero left right) left := by
  unfold Form.Perpendicular cross
  rw [Form.bilinear_neg_left]
  have perpendicular := (Form.lorentz oneNonzero).cliffordCross_perpendicular_left left right
  change (Form.lorentz oneNonzero).bilinear
    ((Form.lorentz oneNonzero).cliffordCross left right) left = 0 at perpendicular
  rw [perpendicular]
  ring1

/-- The Lorentz cross is perpendicular to its right input. -/
theorem cross_perpendicular_right (left right : Vector3 K) :
    (Form.lorentz oneNonzero).Perpendicular (cross oneNonzero left right) right := by
  unfold Form.Perpendicular cross
  rw [Form.bilinear_neg_left]
  have perpendicular := (Form.lorentz oneNonzero).cliffordCross_perpendicular_right left right
  change (Form.lorentz oneNonzero).bilinear
    ((Form.lorentz oneNonzero).cliffordCross left right) right = 0 at perpendicular
  rw [perpendicular]
  ring1

/-- The two sign changes in a Lorentz vector triple product cancel.

The determinant-one Lorentz form specializes the general Clifford triple
product without an extra determinant coefficient.
-/
theorem vector_triple_product (first second third : Vector3 K) :
    cross oneNonzero first (cross oneNonzero second third) =
      Vector3.sub (Vector3.scale ((Form.lorentz oneNonzero).bilinear first third) second)
        (Vector3.scale ((Form.lorentz oneNonzero).bilinear first second) third) := by
  unfold cross
  rw [Form.cliffordCross_neg_right, Vector3.neg_neg, Form.cliffordCross_vector_triple,
    Form.lorentz_determinant, one_mul, one_mul]

/-- Binet–Cauchy holds for the Lorentz pairing and signed cross product. -/
theorem binet_cauchy (first second third fourth : Vector3 K) :
    (Form.lorentz oneNonzero).bilinear (cross oneNonzero first second) (cross oneNonzero third fourth) =
      (Form.lorentz oneNonzero).bilinear first third * (Form.lorentz oneNonzero).bilinear second fourth -
        (Form.lorentz oneNonzero).bilinear first fourth * (Form.lorentz oneNonzero).bilinear second third := by
  unfold cross
  rw [Form.bilinear_neg_left, Form.bilinear_neg_right, neg_neg,
    Form.bilinear_cliffordCross_pair, Form.lorentz_determinant, one_mul]

/-- Lagrange's identity computes the quadrance of a Lorentz cross product. -/
theorem lagrange (left right : Vector3 K) :
    (Form.lorentz oneNonzero).bilinear left right ^ 2 +
        (Form.lorentz oneNonzero).quadrance (cross oneNonzero left right) =
      (Form.lorentz oneNonzero).quadrance left * (Form.lorentz oneNonzero).quadrance right := by
  have identity := binet_cauchy oneNonzero left right left right
  change (Form.lorentz oneNonzero).quadrance (cross oneNonzero left right) =
    (Form.lorentz oneNonzero).quadrance left * (Form.lorentz oneNonzero).quadrance right -
      (Form.lorentz oneNonzero).bilinear left right * (Form.lorentz oneNonzero).bilinear right left at identity
  rw [(Form.lorentz oneNonzero).bilinear_comm right left] at identity
  rw [identity]
  ring1

/-- The Lorentz spread is the cross quadrance divided by the two input quadrances. -/
theorem spread_eq_cross_quadrance (left right : Vector3 K)
    (leftNonNull : (Form.lorentz oneNonzero).quadrance left ≠ 0)
    (rightNonNull : (Form.lorentz oneNonzero).quadrance right ≠ 0) :
    (Form.lorentz oneNonzero).spread left right leftNonNull rightNonNull =
      (Form.lorentz oneNonzero).quadrance (cross oneNonzero left right) /
        ((Form.lorentz oneNonzero).quadrance left * (Form.lorentz oneNonzero).quadrance right) := by
  have cancel := ExplicitField.mul_inv_cancel
    ((Form.lorentz oneNonzero).quadrance left * (Form.lorentz oneNonzero).quadrance right)
    (ExplicitField.mul_ne_zero leftNonNull rightNonNull)
  unfold Form.spread
  rw [ExplicitField.div_eq_mul_inv, ExplicitField.div_eq_mul_inv]
  calc
    1 - (Form.lorentz oneNonzero).bilinear left right ^ 2 *
        ((Form.lorentz oneNonzero).quadrance left * (Form.lorentz oneNonzero).quadrance right)⁻¹ =
      ((Form.lorentz oneNonzero).quadrance left * (Form.lorentz oneNonzero).quadrance right -
          (Form.lorentz oneNonzero).bilinear left right ^ 2) *
        ((Form.lorentz oneNonzero).quadrance left * (Form.lorentz oneNonzero).quadrance right)⁻¹ := by
      rw [sub_mul, cancel]
    _ = (Form.lorentz oneNonzero).quadrance (cross oneNonzero left right) *
        ((Form.lorentz oneNonzero).quadrance left * (Form.lorentz oneNonzero).quadrance right)⁻¹ := by
      rw [← lagrange oneNonzero left right]
      ring1

/-- The Lorentz anchor is the form-skew action of the negated vector coordinate. -/
@[expose] def anchor (vector : Vector3 K) : Matrix3 K :=
  (Form.lorentz oneNonzero).actionSkew (Vector3.neg vector)

/-- The Lorentz anchor has the literal time-first matrix entries. -/
theorem anchor_coordinates (vector : Vector3 K) :
    anchor oneNonzero vector = ⟨0, vector.s, -vector.r, vector.s, 0, vector.t, -vector.r, -vector.t, 0⟩ := by
  unfold anchor Form.actionSkew
  rw [Form.lorentz_adjugate]
  ext <;> unfold Coordinates3.Antisymmetric.anchor Matrix3.mul Vector3.neg <;> ring1

/-- The three upper entries recover a Lorentz anchor's vector. -/
@[expose] def anchorVector (matrix : Matrix3 K) : Vector3 K :=
  ⟨matrix.rs, -matrix.ts, matrix.tr⟩

/-- Reading the upper entries after anchor construction recovers the vector. -/
theorem anchorVector_anchor (vector : Vector3 K) :
    anchorVector (anchor oneNonzero vector) = vector := by
  rw [anchor_coordinates]
  ext <;> unfold anchorVector <;> ring1

/-- Reading a Lorentz anchor vector commutes with scaling the displayed matrix. -/
theorem anchorVector_scale (scalar : K) (matrix : Matrix3 K) :
    anchorVector (Matrix3.scale scalar matrix) = Vector3.scale scalar (anchorVector matrix) := by
  ext <;> unfold anchorVector Matrix3.scale Vector3.scale <;> ring1

/-- Lorentz anchors determine their vector coordinates uniquely. -/
theorem anchor_injective (left right : Vector3 K)
    (equal : anchor oneNonzero left = anchor oneNonzero right) : left = right := by
  have recovered := congrArg anchorVector equal
  rw [anchorVector_anchor, anchorVector_anchor] at recovered
  exact recovered

/-- Anchor construction preserves vector addition. -/
theorem anchor_add (left right : Vector3 K) :
    anchor oneNonzero (Vector3.add left right) =
      Matrix3.add (anchor oneNonzero left) (anchor oneNonzero right) := by
  rw [anchor_coordinates, anchor_coordinates, anchor_coordinates]
  ext <;> unfold Vector3.add Matrix3.add <;> ring1

/-- Anchor construction preserves scalar multiplication. -/
theorem anchor_scale (scalar : K) (vector : Vector3 K) :
    anchor oneNonzero (Vector3.scale scalar vector) =
      Matrix3.scale scalar (anchor oneNonzero vector) := by
  rw [anchor_coordinates, anchor_coordinates]
  ext <;> unfold Vector3.scale Matrix3.scale <;> ring1

/-- Every constructed Lorentz anchor has negative metrical adjoint. -/
theorem anchor_isAnchor (vector : Vector3 K) : IsAnchor oneNonzero (anchor oneNonzero vector) := by
  unfold IsAnchor
  rw [anchor_coordinates, adjoint_coordinates]
  ext <;> unfold Matrix3.neg <;> ring1

/-- A metrical skew matrix is recovered from its upper entries when two is nonzero.

The adjoint relation determines the lower entries. Nonzero two forces each
diagonal entry to vanish, leaving precisely the three retained vector coordinates.
-/
theorem anchor_anchorVector (matrix : Matrix3 K) (twoNonzero : (2 : K) ≠ 0)
    (skew : IsAnchor oneNonzero matrix) : anchor oneNonzero (anchorVector matrix) = matrix := by
  change adjoint oneNonzero matrix = Matrix3.neg matrix at skew
  rw [adjoint_coordinates] at skew
  have tt := congrArg Matrix3.tt skew
  have rt := congrArg Matrix3.rt skew
  have rr := congrArg Matrix3.rr skew
  have st := congrArg Matrix3.st skew
  have sr := congrArg Matrix3.sr skew
  have ss := congrArg Matrix3.ss skew
  change matrix.tt = -matrix.tt at tt
  change -matrix.tr = -matrix.rt at rt
  change matrix.rr = -matrix.rr at rr
  change -matrix.ts = -matrix.st at st
  change matrix.rs = -matrix.sr at sr
  change matrix.ss = -matrix.ss at ss
  have rtEqual := congrArg Neg.neg rt
  have stEqual := congrArg Neg.neg st
  have srEqual := congrArg Neg.neg sr
  simp only [neg_neg] at rtEqual stEqual srEqual
  have diagonalZero (value : K) (equal : value = -value) : value = 0 := by
    apply ExplicitField.eq_zero_of_mul_eq_zero_left twoNonzero
    calc
      2 * value = value + value := by ring1
      _ = value + -value := congrArg (fun entry => value + entry) equal
      _ = 0 := add_neg_cancel value
  rw [anchor_coordinates]
  apply Matrix3.ext
  · exact (diagonalZero matrix.tt tt).symm
  · rfl
  · exact neg_neg matrix.ts
  · exact rtEqual
  · exact (diagonalZero matrix.rr rr).symm
  · rfl
  · exact (neg_neg matrix.ts).trans stEqual
  · exact srEqual
  · exact (diagonalZero matrix.ss ss).symm

/-- Row multiplication by an anchor computes the Lorentz cross product. -/
theorem rowMul_anchor (axis vector : Vector3 K) :
    Matrix3.rowMul vector (anchor oneNonzero axis) = cross oneNonzero axis vector := by
  unfold anchor cross
  rw [Form.rowMul_actionSkew, Form.cliffordCross_neg_left]

/-- Every Lorentz anchor annihilates its own axis vector. -/
theorem rowMul_self_anchor (vector : Vector3 K) :
    Matrix3.rowMul vector (anchor oneNonzero vector) = Vector3.zero := by
  rw [rowMul_anchor]
  unfold cross
  rw [Form.cliffordCross_self]
  ext <;> unfold Vector3.neg Vector3.zero <;> ring1

/-- The product of Lorentz anchors is a dual outer product minus the scalar pairing.

The right vector supplies the form dual and the left vector supplies the row
of the outer product. Their pairing scales the identity matrix.
-/
theorem anchor_product (left right : Vector3 K) :
    Matrix3.mul (anchor oneNonzero left) (anchor oneNonzero right) =
      Matrix3.sub (Matrix3.outer ((Form.lorentz oneNonzero).dual right) left)
        (Matrix3.scale ((Form.lorentz oneNonzero).bilinear left right) Matrix3.identity) := by
  rw [anchor_coordinates, anchor_coordinates, Form.bilinear_lorentz]
  ext <;> unfold Form.dual Form.lorentz Form.ofMatrix Matrix3.rowMul Matrix3.mul
    Matrix3.sub Matrix3.outer Matrix3.scale Matrix3.identity <;> ring1

/-- Squaring a Lorentz anchor retains its axis outer product and quadrance. -/
theorem anchor_square (vector : Vector3 K) :
    Matrix3.mul (anchor oneNonzero vector) (anchor oneNonzero vector) =
      Matrix3.sub (Matrix3.outer ((Form.lorentz oneNonzero).dual vector) vector)
        (Matrix3.scale ((Form.lorentz oneNonzero).quadrance vector) Matrix3.identity) :=
  anchor_product oneNonzero vector vector

/-- Subtracting the two anchor products gives the reversed cross anchor. -/
theorem anchor_commutator (left right : Vector3 K) :
    Matrix3.sub (Matrix3.mul (anchor oneNonzero left) (anchor oneNonzero right))
        (Matrix3.mul (anchor oneNonzero right) (anchor oneNonzero left)) =
      anchor oneNonzero (cross oneNonzero right left) := by
  rw [cross_coordinates, anchor_coordinates, anchor_coordinates, anchor_coordinates]
  ext <;> unfold Matrix3.sub Matrix3.mul <;> ring1

/-- The anchor commutator retains the difference of its two dual outer products. -/
theorem anchor_commutator_outer (left right : Vector3 K) :
    Matrix3.sub (Matrix3.mul (anchor oneNonzero left) (anchor oneNonzero right))
        (Matrix3.mul (anchor oneNonzero right) (anchor oneNonzero left)) =
      Matrix3.sub (Matrix3.outer ((Form.lorentz oneNonzero).dual right) left)
        (Matrix3.outer ((Form.lorentz oneNonzero).dual left) right) := by
  rw [anchor_product, anchor_product, (Form.lorentz oneNonzero).bilinear_comm right left]
  ext <;> unfold Matrix3.sub <;> ring1

/-- A three-anchor sandwich is the negative pairing times its outer anchor. -/
theorem anchor_sandwich (left right : Vector3 K) :
    Matrix3.mul (Matrix3.mul (anchor oneNonzero left) (anchor oneNonzero right))
        (anchor oneNonzero left) =
      Matrix3.scale (-(Form.lorentz oneNonzero).bilinear left right) (anchor oneNonzero left) := by
  rw [anchor_coordinates, anchor_coordinates, Form.bilinear_lorentz]
  ext <;> unfold Matrix3.mul Matrix3.scale <;> ring1

/-- The trace of an anchor product is negative twice the Lorentz pairing. -/
theorem trace_anchor_product (left right : Vector3 K) :
    Matrix3.trace (Matrix3.mul (anchor oneNonzero left) (anchor oneNonzero right)) =
      -2 * (Form.lorentz oneNonzero).bilinear left right := by
  rw [anchor_coordinates, anchor_coordinates, Form.bilinear_lorentz]
  unfold Matrix3.trace Matrix3.mul
  ring1

/-- The trace pairing of Lorentz anchors agrees with their vector pairing.

The same trace form applies to Euclidean and Lorentz anchors. A nonzero-two
certificate justifies cancelling its denominator.
-/
theorem anchorForm_anchor (left right : Vector3 K) (twoNonzero : (2 : K) ≠ 0) :
    Coordinates3.Antisymmetric.anchorForm (anchor oneNonzero left) (anchor oneNonzero right) =
      (Form.lorentz oneNonzero).bilinear left right := by
  unfold Coordinates3.Antisymmetric.anchorForm
  rw [trace_anchor_product, ExplicitField.div_eq_mul_inv]
  calc
    -(-2 * (Form.lorentz oneNonzero).bilinear left right) * (2 : K)⁻¹ =
        (Form.lorentz oneNonzero).bilinear left right * (2 * (2 : K)⁻¹) := by ring1
    _ = (Form.lorentz oneNonzero).bilinear left right := by
      rw [ExplicitField.mul_inv_cancel 2 twoNonzero, mul_one]

/-- The trace quadrance of a Lorentz anchor agrees with its vector quadrance. -/
theorem anchorQuadrance_anchor (vector : Vector3 K) (twoNonzero : (2 : K) ≠ 0) :
    Coordinates3.Antisymmetric.anchorQuadrance (anchor oneNonzero vector) =
      (Form.lorentz oneNonzero).quadrance vector :=
  anchorForm_anchor oneNonzero vector vector twoNonzero

/-- Every Lorentz anchor has zero trace. -/
theorem trace_anchor (vector : Vector3 K) : Matrix3.trace (anchor oneNonzero vector) = 0 := by
  rw [anchor_coordinates]
  unfold Matrix3.trace
  ring1

/-- The sum of principal minors of a Lorentz anchor is its vector quadrance. -/
theorem principalTrace_anchor (vector : Vector3 K) :
    Matrix3.principalTrace (anchor oneNonzero vector) = (Form.lorentz oneNonzero).quadrance vector := by
  rw [anchor_coordinates, Form.quadrance_lorentz]
  unfold Matrix3.principalTrace Matrix3.trace Matrix3.adjugate
  ring1

/-- Every Lorentz anchor has zero determinant. -/
theorem determinant_anchor (vector : Vector3 K) :
    Matrix3.determinant (anchor oneNonzero vector) = 0 := by
  rw [anchor_coordinates]
  unfold Matrix3.determinant
  ring1

/-- The Lorentz anchor characteristic polynomial is `X³+Q(v)X`.

The equality holds for every scalar argument in the supplied explicit field.
It identifies the determinant polynomial without choosing roots or eigenvectors.
-/
theorem characteristicValue_anchor (vector : Vector3 K) (X : K) :
    Matrix3.characteristicValue (anchor oneNonzero vector) X =
      X ^ 3 + (Form.lorentz oneNonzero).quadrance vector * X := by
  rw [anchor_coordinates, Form.quadrance_lorentz]
  unfold Matrix3.characteristicValue Matrix3.determinant Matrix3.sub Matrix3.scale Matrix3.identity
  ring1

end Purelib.Geometry.Quadratic.Ternary.Lorentz
