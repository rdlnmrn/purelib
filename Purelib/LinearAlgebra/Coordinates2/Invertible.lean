module

public import Purelib.LinearAlgebra.Coordinates2.Matrix
import Purelib.Algebra.Field.ExplicitField
import Purelib.Tactic.Ring

/-!
# Invertible two-by-two matrices and their projective scales

An invertible representative retains its original matrix and nonzero
determinant. Multiplication, scaling and inverse use those same entries.
Projective equivalence carries an actual nonzero common scalar witness.
-/

public section

namespace Purelib.LinearAlgebra.Coordinates2.Matrix

open Purelib.Algebra.Field (ExplicitField)
open Purelib.LinearAlgebra.Coordinates2 renaming Matrix -> Matrix2

variable {K : Type*} [ExplicitField K]

/-- Scaling all four matrix entries multiplies its determinant by the scalar square. -/
theorem determinant_scalarScale (factor : K) (matrix : Matrix2 K) :
    (scalarScale factor matrix).determinant = factor ^ 2 * matrix.determinant := by
  unfold scalarScale determinant
  ring1

/-- Scaling twice multiplies the two supplied matrix coefficients. -/
theorem scalarScale_scalarScale (first second : K) (matrix : Matrix2 K) :
    scalarScale second (scalarScale first matrix) = scalarScale (second * first) matrix := by
  apply Matrix2.ext <;> unfold scalarScale <;> ring1

/-- Scaling the original matrix by one preserves all four entries. -/
theorem scalarScale_one (matrix : Matrix2 K) : scalarScale 1 matrix = matrix := by
  apply Matrix2.ext <;> exact one_mul _

/-- Multiplication of two scaled matrices scales their original product by the product coefficient. -/
theorem mul_scalarScale_both (left right : Matrix2 K) (leftScale rightScale : K) :
    mul (scalarScale leftScale left) (scalarScale rightScale right) =
      scalarScale (leftScale * rightScale) (mul left right) := by
  apply Matrix2.ext <;> unfold mul scalarScale <;> ring1

/-- The determinant-normalized adjugate has the inverse of the original nonzero determinant. -/
theorem determinant_normalized_adjugate (matrix : Matrix2 K) (nonzero : matrix.determinant ≠ 0) :
    (scalarScale matrix.determinant⁻¹ matrix.adjugate).determinant = matrix.determinant⁻¹ := by
  rw [determinant_scalarScale, determinant_adjugate]
  calc
    matrix.determinant⁻¹ ^ 2 * matrix.determinant =
        matrix.determinant⁻¹ * (matrix.determinant * matrix.determinant⁻¹) := by ring1
    _ = matrix.determinant⁻¹ := by rw [ExplicitField.mul_inv_cancel _ nonzero, mul_one]

set_option genInjectivity false in
/-- An original two-by-two matrix with its nonzero determinant certificate.

The retained matrix is the input owner for each operation. Its determinant
certificate supports the computed adjugate inverse and certifies total
multiplication in the group of invertible representatives.
-/
structure Invertible (K : Type*) [ExplicitField K] where
  /-- The original displayed matrix. -/ matrix : Matrix2 K
  /-- The determinant of that exact matrix is nonzero. -/ determinantNonzero : matrix.determinant ≠ 0

namespace Invertible

/-- Equality of the original matrix identifies the two invertible representatives. -/
theorem eq_of_matrix_eq {left right : Invertible K} (equal : left.matrix = right.matrix) : left = right := by
  cases left with
  | mk leftMatrix leftCertificate =>
    cases right with
    | mk rightMatrix rightCertificate =>
      change leftMatrix = rightMatrix at equal
      cases equal
      rfl

/-- The displayed identity is invertible when the supplied scalar unit is nonzero. -/
@[expose] def identity (oneNonzero : (1 : K) ≠ 0) : Invertible K where
  matrix := Matrix2.identity
  determinantNonzero := by
    have determinantOne : (Matrix2.identity : Matrix2 K).determinant = 1 := by
      unfold determinant Matrix2.identity
      ring1
    rw [determinantOne]
    exact oneNonzero

/-- Multiply the two retained matrices and certify the product determinant from both original certificates. -/
@[expose] def mul (left right : Invertible K) : Invertible K where
  matrix := Matrix2.mul left.matrix right.matrix
  determinantNonzero := by
    rw [determinant_mul]
    exact ExplicitField.mul_ne_zero left.determinantNonzero right.determinantNonzero

/-- Scale an invertible representative by a supplied nonzero scalar.

The original matrix entries receive that same coefficient. Its nonzero square
transports the original determinant certificate without normalization.
-/
@[expose] def scale (factor : K) (factorNonzero : factor ≠ 0) (value : Invertible K) : Invertible K where
  matrix := scalarScale factor value.matrix
  determinantNonzero := by
    rw [determinant_scalarScale]
    exact ExplicitField.mul_ne_zero (ExplicitField.square_nonzero_of_nonzero factorNonzero) value.determinantNonzero

/-- Compute an invertible matrix's inverse from its retained adjugate and inverse determinant.

The inverse determinant is evaluated once outside the entry-producing scale
operation. The nonzero output determinant is certified from the original
input determinant and the exact normalized-adjugate identity.
-/
@[expose] def inverse (value : Invertible K) : Invertible K :=
  let inverseDeterminant := value.matrix.determinant⁻¹
  let cofactors := value.matrix.adjugate
  { matrix := scalarScale inverseDeterminant cofactors
    determinantNonzero := by
      rw [determinant_normalized_adjugate _ value.determinantNonzero]
      exact ExplicitField.inv_ne_zero value.determinantNonzero }

/-- The product of an invertible matrix with its computed inverse is the displayed identity. -/
theorem mul_inverse_matrix (value : Invertible K) :
    (mul value (inverse value)).matrix = Matrix2.identity := by
  change Matrix2.mul value.matrix (scalarScale value.matrix.determinant⁻¹ value.matrix.adjugate) = _
  calc
    _ = scalarScale value.matrix.determinant⁻¹ (Matrix2.mul value.matrix value.matrix.adjugate) := by
      apply Matrix2.ext <;> unfold Matrix2.mul scalarScale <;> ring1
    _ = scalarScale value.matrix.determinant⁻¹ (scalarScale value.matrix.determinant Matrix2.identity) :=
      congrArg (scalarScale value.matrix.determinant⁻¹) (mul_adjugate value.matrix)
    _ = Matrix2.identity := by
      rw [scalarScale_scalarScale, mul_comm value.matrix.determinant⁻¹ value.matrix.determinant,
        ExplicitField.mul_inv_cancel _ value.determinantNonzero, scalarScale_one]

/-- The computed inverse times its original matrix is the displayed identity. -/
theorem inverse_mul_matrix (value : Invertible K) :
    (mul (inverse value) value).matrix = Matrix2.identity := by
  change Matrix2.mul (scalarScale value.matrix.determinant⁻¹ value.matrix.adjugate) value.matrix = _
  calc
    _ = scalarScale value.matrix.determinant⁻¹ (Matrix2.mul value.matrix.adjugate value.matrix) := by
      apply Matrix2.ext <;> unfold Matrix2.mul scalarScale <;> ring1
    _ = scalarScale value.matrix.determinant⁻¹ (scalarScale value.matrix.determinant Matrix2.identity) :=
      congrArg (scalarScale value.matrix.determinant⁻¹) (adjugate_mul value.matrix)
    _ = Matrix2.identity := by
      rw [scalarScale_scalarScale, mul_comm value.matrix.determinant⁻¹ value.matrix.determinant,
        ExplicitField.mul_inv_cancel _ value.determinantNonzero, scalarScale_one]

/-- Matrix multiplication is associative on the retained invertible representatives. -/
theorem mul_assoc (first second third : Invertible K) :
    mul (mul first second) third = mul first (mul second third) :=
  eq_of_matrix_eq (Matrix2.mul_assoc first.matrix second.matrix third.matrix)

/-- The supplied invertible identity is a left unit. -/
theorem identity_mul (oneNonzero : (1 : K) ≠ 0) (value : Invertible K) : mul (identity oneNonzero) value = value :=
  eq_of_matrix_eq (Matrix2.identity_mul value.matrix)

/-- The supplied invertible identity is a right unit. -/
theorem mul_identity (oneNonzero : (1 : K) ≠ 0) (value : Invertible K) : mul value (identity oneNonzero) = value :=
  eq_of_matrix_eq (Matrix2.mul_identity value.matrix)

/-- The computed inverse is a right inverse in the original invertible-matrix record. -/
theorem mul_inverse (oneNonzero : (1 : K) ≠ 0) (value : Invertible K) :
    mul value (inverse value) = identity oneNonzero := eq_of_matrix_eq (mul_inverse_matrix value)

/-- The computed inverse is a left inverse in the original invertible-matrix record. -/
theorem inverse_mul (oneNonzero : (1 : K) ≠ 0) (value : Invertible K) :
    mul (inverse value) value = identity oneNonzero := eq_of_matrix_eq (inverse_mul_matrix value)

/-- A displayed right inverse of the original matrix agrees with its computed inverse.

The original computed left inverse and matrix associativity transport the
given product equation. The candidate may be any displayed matrix and needs
no separately rebuilt invertibility certificate.
-/
theorem inverse_unique (value : Invertible K) (candidate : Matrix2 K)
    (rightInverse : Matrix2.mul value.matrix candidate = Matrix2.identity) :
    candidate = (inverse value).matrix := by
  calc
    candidate = Matrix2.mul Matrix2.identity candidate := (Matrix2.identity_mul candidate).symm
    _ = Matrix2.mul (Matrix2.mul (inverse value).matrix value.matrix) candidate :=
      congrArg (fun matrix => Matrix2.mul matrix candidate) (inverse_mul_matrix value).symm
    _ = Matrix2.mul (inverse value).matrix (Matrix2.mul value.matrix candidate) :=
      Matrix2.mul_assoc _ _ _
    _ = Matrix2.mul (inverse value).matrix Matrix2.identity :=
      congrArg (Matrix2.mul (inverse value).matrix) rightInverse
    _ = (inverse value).matrix := Matrix2.mul_identity _

/-- Projective invertible-matrix equivalence retains a nonzero common scalar relating the two original matrices. -/
@[expose] def Equivalent (left right : Invertible K) : Prop :=
  ∃ factor : K, factor ≠ 0 ∧ right.matrix = scalarScale factor left.matrix

/-- The supplied nonzero unit makes projective invertible-matrix equivalence reflexive. -/
theorem Equivalent.refl (oneNonzero : (1 : K) ≠ 0) (value : Invertible K) : value.Equivalent value :=
  ⟨1, oneNonzero, (scalarScale_one value.matrix).symm⟩

/-- Projective invertible-matrix equivalence is symmetric with the reciprocal of its retained scalar. -/
theorem Equivalent.symm {left right : Invertible K} (equivalent : left.Equivalent right) :
    right.Equivalent left := by
  rcases equivalent with ⟨factor, nonzero, represents⟩
  refine ⟨factor⁻¹, ExplicitField.inv_ne_zero nonzero, ?_⟩
  calc
    left.matrix = scalarScale factor⁻¹ (scalarScale factor left.matrix) := by
      rw [scalarScale_scalarScale, mul_comm factor⁻¹ factor, ExplicitField.mul_inv_cancel factor nonzero,
        scalarScale_one]
    _ = scalarScale factor⁻¹ right.matrix := congrArg (scalarScale factor⁻¹) represents.symm

/-- Projective invertible-matrix equivalence composes by multiplying its two original scalar witnesses. -/
theorem Equivalent.trans {first second third : Invertible K}
    (left : first.Equivalent second) (right : second.Equivalent third) : first.Equivalent third := by
  rcases left with ⟨leftScale, leftNonzero, leftRepresents⟩
  rcases right with ⟨rightScale, rightNonzero, rightRepresents⟩
  refine ⟨rightScale * leftScale, ExplicitField.mul_ne_zero rightNonzero leftNonzero, ?_⟩
  calc
    third.matrix = scalarScale rightScale second.matrix := rightRepresents
    _ = scalarScale rightScale (scalarScale leftScale first.matrix) :=
      congrArg (scalarScale rightScale) leftRepresents
    _ = scalarScale (rightScale * leftScale) first.matrix := scalarScale_scalarScale _ _ _

/-- Multiplication respects projective equivalence of both retained input matrices. -/
theorem mul_respects_equivalent {left right left' right' : Invertible K}
    (leftEquivalent : left.Equivalent left') (rightEquivalent : right.Equivalent right') :
    (mul left right).Equivalent (mul left' right') := by
  rcases leftEquivalent with ⟨leftScale, leftNonzero, leftRepresents⟩
  rcases rightEquivalent with ⟨rightScale, rightNonzero, rightRepresents⟩
  refine ⟨leftScale * rightScale, ExplicitField.mul_ne_zero leftNonzero rightNonzero, ?_⟩
  change Matrix2.mul left'.matrix right'.matrix = _
  calc
    Matrix2.mul left'.matrix right'.matrix = Matrix2.mul (scalarScale leftScale left.matrix) right'.matrix :=
      congrArg (fun matrix => Matrix2.mul matrix right'.matrix) leftRepresents
    _ = Matrix2.mul (scalarScale leftScale left.matrix) (scalarScale rightScale right.matrix) :=
      congrArg (Matrix2.mul (scalarScale leftScale left.matrix)) rightRepresents
    _ = scalarScale (leftScale * rightScale) (Matrix2.mul left.matrix right.matrix) :=
      mul_scalarScale_both left.matrix right.matrix leftScale rightScale

/-- Computed inversion respects projective equivalence using the reciprocal of the original scalar witness.

The scaled original inverse is a displayed right inverse of the target
matrix. Uniqueness identifies it with that target's computed inverse, without
recomputing a determinant ratio or selecting a new projective scale.
-/
theorem inverse_respects_equivalent {left right : Invertible K} (equivalent : left.Equivalent right) :
    (inverse left).Equivalent (inverse right) := by
  rcases equivalent with ⟨factor, nonzero, represents⟩
  refine ⟨factor⁻¹, ExplicitField.inv_ne_zero nonzero, ?_⟩
  apply (inverse_unique right (scalarScale factor⁻¹ (inverse left).matrix) ?_).symm
  calc
    Matrix2.mul right.matrix (scalarScale factor⁻¹ (inverse left).matrix) =
        Matrix2.mul (scalarScale factor left.matrix) (scalarScale factor⁻¹ (inverse left).matrix) :=
      congrArg (fun matrix => Matrix2.mul matrix (scalarScale factor⁻¹ (inverse left).matrix)) represents
    _ = scalarScale (factor * factor⁻¹) (Matrix2.mul left.matrix (inverse left).matrix) :=
      mul_scalarScale_both left.matrix (inverse left).matrix factor factor⁻¹
    _ = Matrix2.identity := by
      rw [ExplicitField.mul_inv_cancel factor nonzero, scalarScale_one]
      exact mul_inverse_matrix left

/-- An invertible matrix represents the projective identity exactly when it is a nonzero scalar identity matrix. -/
theorem equivalent_identity_iff_scalar (oneNonzero : (1 : K) ≠ 0) (value : Invertible K) :
    value.Equivalent (identity oneNonzero) ↔
      ∃ factor : K, factor ≠ 0 ∧ value.matrix = scalarScale factor Matrix2.identity := by
  constructor
  · intro equivalent
    exact equivalent.symm
  · intro scalar
    exact (show (identity oneNonzero).Equivalent value from scalar).symm

end Invertible

end Purelib.LinearAlgebra.Coordinates2.Matrix
