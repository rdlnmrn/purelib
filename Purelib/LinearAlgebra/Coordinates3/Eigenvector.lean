module

public import Purelib.LinearAlgebra.Coordinates3.Matrix
import Purelib.LinearAlgebra.Coordinates3.Vector
import Purelib.Algebra.Field.ExplicitField
import Purelib.Tactic.Ring

/-!
# Eigenvectors of displayed ternary matrices

A nonzero derivative at a characteristic root supplies a nonzero diagonal
cofactor. Testing the three cached diagonal cofactors therefore selects
an actual nonzero eigenvector by a finite, executable construction.
-/

public section

namespace Purelib.LinearAlgebra.Coordinates3.Matrix3

open Purelib.Algebra.Field (ExplicitField)
open Purelib.LinearAlgebra.Coordinates3

variable {K : Type*} [ExplicitField K]

set_option genInjectivity false in
/-- A retained nonzero row eigenvector of the original displayed matrix at the indexed scalar eigenvalue. -/
structure RowEigenvector (matrix : Matrix3 K) (eigenvalue : K) where
  /-- The original row vector. -/ value : Vector K
  /-- The retained row is nonzero. -/ nonzero : value ≠ Vector.zero
  /-- The original matrix acts on the row by the indexed eigenvalue. -/
  equation : rowMul value matrix = Vector.scale eigenvalue value

/-- The derivative of the displayed cubic characteristic polynomial at a supplied field point. -/
@[expose] def characteristicSlope (matrix : Matrix3 K) (point : K) : K :=
  3 * point ^ 2 - 2 * trace matrix * point + principalTrace matrix

/-- The characteristic derivative is the trace of the original characteristic matrix's adjugate. -/
theorem characteristicSlope_eq_trace_adjugate (matrix : Matrix3 K) (point : K) :
    characteristicSlope matrix point = trace (adjugate (sub (scale point identity) matrix)) := by
  unfold characteristicSlope principalTrace adjugate sub scale identity trace
  ring1

/-- The characteristic matrix annihilates a row exactly when it is an eigenvector equation for the original matrix. -/
theorem rowMul_characteristic_eq_zero_iff (matrix : Matrix3 K) (point : K) (vector : Vector K) :
    rowMul vector (sub (scale point identity) matrix) = Vector.zero ↔
      rowMul vector matrix = Vector.scale point vector := by
  rw [rowMul_sub, rowMul_scale, rowMul_identity]
  constructor
  · intro difference
    calc
      rowMul vector matrix = Vector.sub (Vector.scale point vector)
          (Vector.sub (Vector.scale point vector) (rowMul vector matrix)) := by
        ext <;> unfold Vector.sub <;> ring1
      _ = Vector.sub (Vector.scale point vector) Vector.zero := by rw [difference]
      _ = Vector.scale point vector := by ext <;> unfold Vector.sub Vector.zero <;> ring1
  · intro equation
    rw [equation]
    ext <;> unfold Vector.sub Vector.zero <;> ring1

/-- Every retained nonzero row eigenvector makes the original characteristic polynomial vanish. -/
theorem RowEigenvector.characteristicValue_eq_zero [DecidableEq K] {matrix : Matrix3 K} {point : K}
    (witness : RowEigenvector matrix point) : characteristicValue matrix point = 0 := by
  by_cases zero : characteristicValue matrix point = 0
  · exact zero
  · apply False.elim
    apply witness.nonzero
    let characteristic := sub (scale point identity) matrix
    have kernel : rowMul witness.value characteristic = Vector.zero :=
      (rowMul_characteristic_eq_zero_iff matrix point witness.value).mpr witness.equation
    have scaledZero : Vector.scale (determinant characteristic) witness.value = Vector.zero := by
      calc
        _ = rowMul witness.value (scale (determinant characteristic) identity) := by
          rw [rowMul_scale, rowMul_identity]
        _ = rowMul witness.value (mul characteristic (adjugate characteristic)) := by rw [mul_adjugate]
        _ = rowMul (rowMul witness.value characteristic) (adjugate characteristic) :=
          (rowMul_mul _ _ _).symm
        _ = Vector.zero := by
          rw [kernel]
          ext <;> unfold rowMul Vector.zero <;> ring1
    exact Vector.eq_of_scale_eq_scale zero (scaledZero.trans (Vector.scale_zero _).symm)

/-- Construct a nonzero eigenvector from a simple root of the original characteristic polynomial.

The characteristic matrix and its adjugate are cached once. The first nonzero diagonal cofactor selects the retained
adjugate row; if the first two vanish, the nonzero characteristic derivative certifies the third. -/
@[expose] def simpleRootEigenvector [DecidableEq K] (matrix : Matrix3 K) (point : K)
    (root : characteristicValue matrix point = 0) (simple : characteristicSlope matrix point ≠ 0) :
    RowEigenvector matrix point := by
  let characteristic := sub (scale point identity) matrix
  let cofactors := adjugate characteristic
  have annihilates : mul cofactors characteristic = zero := by
    change mul (adjugate characteristic) characteristic = zero
    rw [adjugate_mul]
    have determinantZero : determinant characteristic = 0 := root
    rw [determinantZero]
    ext <;> dsimp only [scale, zero] <;> exact zero_mul _
  by_cases firstZero : cofactors.tt = 0
  · by_cases secondZero : cofactors.rr = 0
    · have thirdNonzero : cofactors.ss ≠ 0 := by
        intro thirdZero
        apply simple
        rw [characteristicSlope_eq_trace_adjugate]
        change trace cofactors = 0
        unfold trace
        rw [firstZero, secondZero, thirdZero, add_zero, add_zero]
      refine ⟨rowS cofactors, ?_, ?_⟩
      · intro vectorZero
        exact thirdNonzero (congrArg Vector.s vectorZero)
      · apply (rowMul_characteristic_eq_zero_iff matrix point _).mp
        exact congrArg rowS annihilates
    · refine ⟨rowR cofactors, ?_, ?_⟩
      · intro vectorZero
        exact secondZero (congrArg Vector.r vectorZero)
      · apply (rowMul_characteristic_eq_zero_iff matrix point _).mp
        exact congrArg rowR annihilates
  · refine ⟨rowT cofactors, ?_, ?_⟩
    · intro vectorZero
      exact firstZero (congrArg Vector.t vectorZero)
    · apply (rowMul_characteristic_eq_zero_iff matrix point _).mp
      exact congrArg rowT annihilates

end Purelib.LinearAlgebra.Coordinates3.Matrix3
