module

public import Purelib.Polynomial.Recurrence.Boundary.NormalForm
public import Purelib.LinearAlgebra.Matrix.NormalForm.Coordinates
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Data.List.Reverse
import Purelib.Data.Vector.Basic
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Complete constant recurrences and their actual empty-column boundaries

A normalized nonzero degree-zero source retains its actual leading unit.
Its original empty-column boundary supplies the kernel, image and complement
coordinates directly. The same unit forces every complete finite recurrence
solution to vanish, without constructing roots or a positive-degree companion.
-/

public section

namespace Purelib.Polynomial.Recurrence.Boundary

open Purelib.Data renaming Vector → Vec
open Purelib.Data.Vector.Basic
open Purelib.Data.List
open Purelib.Algebra.FiniteSum.Fin
open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.LinearAlgebra.Matrix

variable {K : Type*} [CommRing K] [DecidableEq K]

set_option genInjectivity false in
/-- A complete constant source recurrence and its original cached empty-column boundary.

The original source is normalized, nonzero and degree zero. A retained unit
inverse of its leading coefficient proves recurrence completeness. The
source-derived horizon and actual normal form are each cached once; the
normal form's original coordinate matrices are retained unchanged.
-/
structure Constant (polynomial : DensePolynomial K) (rows : Nat) where
  /-- The actual original source coefficient table is normalized. -/
  normalized : polynomial.normalize = polynomial
  /-- The actual original source is nonzero. -/
  nonzero : polynomial.isZero = false
  /-- The same original source has natural degree zero. -/
  degreeZero : polynomial.natDegree = 0
  /-- The retained inverse of the original leading coefficient. -/
  leadingInverse : K
  /-- The same original leading coefficient multiplies that retained inverse to one. -/
  leadingUnit : polynomial.leadingCoeff * leadingInverse = 1
  /-- The once-computed source-derived finite horizon. -/
  count : Nat
  /-- The horizon retains the original requested rows and source coefficient slots. -/
  count_eq : count = rows + polynomial.coeffs.reverse.length
  /-- The actual original normal form on the empty source-coordinate word. -/
  normal : NormalForm (matrix polynomial rows (.nil : Vec (Vec K count) 0))
  /-- The complete retained normal form is the original empty-column constructor. -/
  normal_eq : normal = emptyColumns polynomial rows

constructive_injectivity Constant

namespace Constant

/-- Retain checked original horizon and normal-form caches without repeating their producers. -/
@[expose] def ofNormal (polynomial : DensePolynomial K) (rows : Nat)
    (normalized : polynomial.normalize = polynomial) (nonzero : polynomial.isZero = false)
    (degreeZero : polynomial.natDegree = 0) (leadingInverse : K)
    (leadingUnit : polynomial.leadingCoeff * leadingInverse = 1)
    (count : Nat) (countEq : count = rows + polynomial.coeffs.reverse.length)
    (normal : NormalForm (matrix polynomial rows (.nil : Vec (Vec K count) 0)))
    (normalEq : normal = emptyColumns polynomial rows) : Constant polynomial rows :=
  { normalized, nonzero, degreeZero, leadingInverse, leadingUnit, count, count_eq := countEq
    normal, normal_eq := normalEq }

/-- Prepare one source-derived horizon and the same original empty-column boundary normal form. -/
@[expose] def prepare (polynomial : DensePolynomial K) (rows : Nat)
    (normalized : polynomial.normalize = polynomial) (nonzero : polynomial.isZero = false)
    (degreeZero : polynomial.natDegree = 0) (leadingInverse : K)
    (leadingUnit : polynomial.leadingCoeff * leadingInverse = 1) : Constant polynomial rows :=
  let count := rows + polynomial.coeffs.reverse.length
  let normal := emptyColumns (horizon := count) polynomial rows
  ofNormal polynomial rows normalized nonzero degreeZero leadingInverse leadingUnit count rfl normal rfl

variable {polynomial : DensePolynomial K} {rows : Nat}

/-- The same normalized original source is exactly the constant at its retained leading coefficient. -/
theorem source_constant (retained : Constant polynomial rows) :
    polynomial = DensePolynomial.constant polynomial.leadingCoeff :=
  retained.normalized.symm.trans
    (DensePolynomial.normalize_eq_constant_leadingCoeff_of_degree_zero retained.nonzero retained.degreeZero)

/-- The original constant boundary has no independent source image coordinates. -/
theorem rank_eq (retained : Constant polynomial rows) : retained.normal.rank = 0 := by
  rewrite [retained.normal_eq]
  rfl

/-- The original constant boundary has no free source coordinates. -/
theorem kernel_dimension (retained : Constant polynomial rows) : retained.normal.kernelDimension = 0 := by
  change 0 - retained.normal.rank = 0
  rewrite [retained.rank_eq]
  rfl

/-- Every original target coordinate belongs to the actual retained complementary space. -/
theorem complement_dimension (retained : Constant polynomial rows) : retained.normal.cokernelDimension = rows := by
  change rows - retained.normal.rank = rows
  rewrite [retained.rank_eq]
  rfl

/-- The original complementary-target minus kernel dimension has the positive constant-symbol sign. -/
theorem defect_eq (retained : Constant polynomial rows) : retained.normal.defect = (rows : Int) :=
  retained.normal.defect_eq.trans (by rfl)

/-- Every original in-range coefficient recurrence row is its same leading unit times the retained value.

The actual reversed coefficient table is compared with its original singleton
using bounded scalar sum transport. No function equality or simplification
under the coefficient binder is used.
-/
theorem recurrence_at (retained : Constant polynomial rows) {count : Nat} (values : Vec K count)
    (index : Fin count) :
    sumFin (fun coefficient : Fin polynomial.coeffs.reverse.length =>
      getD polynomial.coeffs.reverse coefficient.val 0 * sample values (index.val + coefficient.val)) =
        polynomial.leadingCoeff * values index := by
  have coefficients : polynomial.coeffs.reverse = [polynomial.leadingCoeff] :=
    (congrArg (fun source : DensePolynomial K => source.coeffs.reverse) retained.source_constant).trans rfl
  have size : polynomial.coeffs.reverse.length = 1 := (congrArg List.length coefficients).trans rfl
  calc
    _ = sumFin (fun coefficient : Fin 1 =>
        polynomial.leadingCoeff * sample values (index.val + coefficient.val)) := by
      apply sumFin_congr_size size
      intro first second same
      have zero : second.val = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ second.isLt)
      have slot : getD polynomial.coeffs.reverse first.val 0 = polynomial.leadingCoeff :=
        (congrArg (fun table : List K => getD table first.val 0) coefficients).trans
          ((congrArg (fun position : Nat => getD [polynomial.leadingCoeff] position 0)
            (same.trans zero)).trans rfl)
      exact (congrArg (fun scalar => scalar * sample values (index.val + first.val)) slot).trans
        (congrArg (fun position => polynomial.leadingCoeff * sample values (index.val + position)) same)
    _ = polynomial.leadingCoeff * values index := by
      rewrite [sumFin_succ]
      change polynomial.leadingCoeff * sample values (index.val + 0) + 0 = _
      rewrite [Nat.add_zero, sample_at, add_zero]
      rfl

/-- Every supplied complete finite solution of the same constant recurrence is the original zero vector.

All original starts inside the finite horizon are required. The singleton
coefficient row vanishes there; multiplication by the retained leading unit
inverse then proves each same structural coordinate is zero.
-/
theorem solution_zero (retained : Constant polynomial rows) {count : Nat} (values : Vec K count)
    (equations : Equations polynomial count (.cons values .nil)) : values = vectorOfFn (fun _ => 0) := by
  apply vector_ext
  intro index
  rewrite [vectorOfFn_apply]
  have equation := equations index (0 : Fin 1)
  change sumFin (fun coefficient : Fin polynomial.coeffs.reverse.length =>
    getD polynomial.coeffs.reverse coefficient.val 0 * sample values (index.val + coefficient.val)) = 0 at equation
  have vanishing := (retained.recurrence_at values index).symm.trans equation
  have inverseUnit : retained.leadingInverse * polynomial.leadingCoeff = 1 :=
    (mul_comm _ _).trans retained.leadingUnit
  calc
    values index = 1 * values index := (one_mul _).symm
    _ = (retained.leadingInverse * polynomial.leadingCoeff) * values index :=
      congrArg (fun scalar => scalar * values index) inverseUnit.symm
    _ = retained.leadingInverse * (polynomial.leadingCoeff * values index) := mul_assoc _ _ _
    _ = retained.leadingInverse * 0 := congrArg (fun scalar => retained.leadingInverse * scalar) vanishing
    _ = 0 := mul_zero _

/-- Checked original caches recover the complete constant recurrence and boundary preparation. -/
theorem ofNormal_eq_prepare (polynomial : DensePolynomial K) (rows : Nat)
    (normalized : polynomial.normalize = polynomial) (nonzero : polynomial.isZero = false)
    (degreeZero : polynomial.natDegree = 0) (leadingInverse : K)
    (leadingUnit : polynomial.leadingCoeff * leadingInverse = 1)
    (count : Nat) (countEq : count = rows + polynomial.coeffs.reverse.length)
    (normal : NormalForm (matrix polynomial rows (.nil : Vec (Vec K count) 0)))
    (normalEq : normal = emptyColumns polynomial rows) :
    ofNormal polynomial rows normalized nonzero degreeZero leadingInverse leadingUnit count countEq normal normalEq =
      prepare polynomial rows normalized nonzero degreeZero leadingInverse leadingUnit := by
  cases countEq
  cases normalEq
  rfl

/-- The complete retained constant source and boundary cache restores its same original preparation. -/
theorem restore (retained : Constant polynomial rows) :
    retained = prepare polynomial rows retained.normalized retained.nonzero retained.degreeZero
      retained.leadingInverse retained.leadingUnit := by
  cases retained with
  | mk normalized nonzero degreeZero inverse unit count countEq normal normalEq =>
      exact ofNormal_eq_prepare polynomial rows normalized nonzero degreeZero inverse unit count countEq normal normalEq

end Constant
end Purelib.Polynomial.Recurrence.Boundary

end
