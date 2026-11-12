module

public import Purelib.Polynomial.Dense.Evaluation
public import Purelib.LinearAlgebra.Matrix.Multiplication
public import Purelib.LinearAlgebra.PolynomialMatrix.Pencil
import Purelib.Polynomial.Dense.Basic
import Purelib.Algebra.Field.ExplicitField
import Purelib.Algebra.FiniteSum.Fin
public import Purelib.Data.List.GetD
public import Purelib.Data.List.Reverse
import Purelib.Data.Vector.Basic
import Purelib.LinearAlgebra.Matrix.Basic
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Original coefficient polynomials and their companion matrices

Positive degree gives a nonzero original leading coefficient. One retained
ascending lower-coefficient table supplies the cached feedback vector and
companion matrix. Its action on the original power vector retains the exact
source-polynomial residual, rather than assuming an eigenvalue equation.
-/

public section

namespace Purelib.Polynomial.Dense

open Purelib
open Purelib.Algebra.Field (ExplicitField)
open Purelib.Algebra.FiniteSum
open Purelib.Data.List
open Purelib.Data.Vector.Basic (vectorOfFn vectorOfFn_apply)
open Purelib.LinearAlgebra renaming Matrix -> SquareMatrix
open Purelib.Polynomial.Dense.Basic (DensePolynomial)

variable {K : Type*} [CommRing K] [DecidableEq K]

namespace Companion

/-- The shift rows and retained feedback row of a finite companion matrix.

Each preceding row reads its actual successor column. The last row reads the
same retained feedback vector; an empty dimension has no row or column.
-/
@[expose] def matrixOfFeedback {dimension : Nat} (feedback : Data.Vector K dimension) : SquareMatrix K dimension :=
  SquareMatrix.matrixOfFn fun row column =>
    if next : row.val + 1 < dimension then
      if column = ⟨row.val + 1, next⟩ then 1 else 0
    else feedback column

end Companion

set_option genInjectivity false in
/-- A positive-degree original polynomial with its actual lower-coefficient, feedback and companion-matrix caches.

The original polynomial determines every index through its natural degree.
Normalization is retained through the exact ascending lower table and source
shape. The same feedback coefficients supply the cached matrix, and its
nonzero leading coefficient determines their original scalar normalization.
-/
structure Companion (polynomial : DensePolynomial K) where
  /-- The original polynomial has positive natural degree. -/
  positive : 0 < polynomial.natDegree
  /-- The actual original normalized lower coefficients in ascending order. -/
  coefficients : List K
  /-- The table is the reversal of the original normalized coefficient tail. -/
  coefficients_eq : coefficients = polynomial.normalize.coeffs.tail.reverse
  /-- The retained coefficient count is the original polynomial degree. -/
  count_eq : coefficients.length = polynomial.natDegree
  /-- The original normalized source keeps its leading coefficient and the same retained lower table. -/
  source_eq : polynomial.normalize.coeffs = polynomial.leadingCoeff :: coefficients.reverse
  /-- The original leading coefficient is nonzero. -/
  leading_nonzero : polynomial.leadingCoeff ≠ 0
  /-- The cached inverse of the original leading coefficient. -/
  leadingInverse : K
  /-- The original leading coefficient times its same cached inverse is one. -/
  leading_unit : polynomial.leadingCoeff * leadingInverse = 1
  /-- The actual cached feedback coefficients at the original degree. -/
  feedback : Data.Vector K polynomial.natDegree
  /-- Each feedback coefficient is the original lower coefficient divided by the original leading coefficient. -/
  feedback_eq : ∀ index, feedback index = -getD coefficients index.val 0 * leadingInverse
  /-- The actual cached companion matrix indexed by the original degree. -/
  matrix : SquareMatrix K polynomial.natDegree
  /-- The cached matrix consumes this same retained feedback vector. -/
  matrix_eq : matrix = Companion.matrixOfFeedback feedback

constructive_injectivity Companion

namespace Companion

/-- Compute the original polynomial's caches using its certified leading inverse.

The original positive degree fixes every dimension. No inverse of a lower
coefficient or root is requested.
-/
@[expose] def ofUnit (polynomial : DensePolynomial K) (positive : 0 < polynomial.natDegree)
    (inverse : K) (unit : polynomial.leadingCoeff * inverse = 1) : Companion polynomial := by
  match source : polynomial.normalize.coeffs with
  | [] =>
      have degree : polynomial.natDegree = 0 := by
        change polynomial.normalize.coeffs.length - 1 = 0
        rewrite [source]
        rfl
      exact False.elim (Nat.not_lt_zero 0 (degree ▸ positive))
  | leading :: tail =>
      have originalLeading : polynomial.leadingCoeff = leading := by
        change polynomial.normalize.coeffs.headD 0 = leading
        rewrite [source]
        rfl
      have count : tail.length = polynomial.natDegree := by
        change tail.length = polynomial.normalize.coeffs.length - 1
        rewrite [source]
        rfl
      have nonzero : polynomial.isZero = false := by
        change polynomial.normalize.coeffs.isEmpty = false
        rewrite [source]
        rfl
      let coefficients := tail.reverse
      let scale := inverse
      let feedback := vectorOfFn fun index : Fin polynomial.natDegree =>
        -getD coefficients index.val 0 * scale
      let matrix := matrixOfFeedback feedback
      exact
        { positive := positive
          coefficients := coefficients
          coefficients_eq := by rewrite [source]; rfl
          count_eq := (Reverse.length_reverse tail).trans count
          source_eq := by
            dsimp only [coefficients]
            rewrite [originalLeading, Reverse.reverse_reverse]
            exact source
          leading_nonzero := DensePolynomial.leadingCoeff_ne_zero nonzero
          leadingInverse := inverse
          leading_unit := unit
          feedback := feedback
          feedback_eq := fun index => vectorOfFn_apply _ index
          matrix := matrix
          matrix_eq := rfl }

/-- The unit-based original companion retains exactly the supplied leading inverse. -/
theorem ofUnit_leadingInverse (polynomial : DensePolynomial K) (positive : 0 < polynomial.natDegree)
    (inverse : K) (unit : polynomial.leadingCoeff * inverse = 1) :
    (ofUnit polynomial positive inverse unit).leadingInverse = inverse := by
  unfold ofUnit
  split
  · rename_i source
    have degree : polynomial.natDegree = 0 := by
      change polynomial.normalize.coeffs.length - 1 = 0
      rewrite [source]
      rfl
    exact False.elim (Nat.not_lt_zero 0 (degree ▸ positive))
  · rfl

/-- Any displayed leading unit has the same inverse as the original retained companion cache.

The original leading-unit equation and supplied candidate equation identify
the two actual scalars by finite multiplication. No cancellation, field
structure or assumption on the other polynomial coefficients is required.
-/
theorem leadingInverse_of_unit {polynomial : DensePolynomial K} (companion : Companion polynomial)
    (candidate : K) (unit : polynomial.leadingCoeff * candidate = 1) :
    companion.leadingInverse = candidate := by
  calc
    companion.leadingInverse = companion.leadingInverse * 1 := (mul_one _).symm
    _ = companion.leadingInverse * (polynomial.leadingCoeff * candidate) :=
      congrArg (fun value => companion.leadingInverse * value) unit.symm
    _ = (polynomial.leadingCoeff * companion.leadingInverse) * candidate := by
      rewrite [← mul_assoc, mul_comm companion.leadingInverse polynomial.leadingCoeff]
      rfl
    _ = candidate := by rewrite [companion.leading_unit, one_mul]; rfl

/-- Over an explicit field, the retained leading unit is the original leading coefficient's supplied inverse. -/
theorem leadingInverse_eq {L : Type*} [ExplicitField L] [DecidableEq L]
    {polynomial : DensePolynomial L} (companion : Companion polynomial) :
    companion.leadingInverse = polynomial.leadingCoeff⁻¹ :=
  companion.leadingInverse_of_unit _ (ExplicitField.mul_inv_cancel _ companion.leading_nonzero)

/-- Compute the same retained companion automatically over an explicit field. -/
@[expose] def ofPositive {L : Type*} [ExplicitField L] [DecidableEq L]
    (polynomial : DensePolynomial L) (positive : 0 < polynomial.natDegree) : Companion polynomial :=
  ofUnit polynomial positive polynomial.leadingCoeff⁻¹
    (ExplicitField.mul_inv_cancel _ (DensePolynomial.leadingCoeff_ne_zero (by
      cases source : polynomial.normalize.coeffs with
      | nil =>
          have degree : polynomial.natDegree = 0 := by
            change polynomial.normalize.coeffs.length - 1 = 0
            rw [source]
            rfl
          exact False.elim (Nat.not_lt_zero 0 (degree ▸ positive))
      | cons leading tail =>
          change polynomial.normalize.coeffs.isEmpty = false
          rw [source]
          rfl)))

/-- Materialize the original degree-sized power vector at one supplied scalar point. -/
def powers {polynomial : DensePolynomial K} (_companion : Companion polynomial) (point : K) :
    Data.Vector K polynomial.natDegree := vectorOfFn fun index => point ^ index.val

/-- Each retained power-vector component reads its actual original bounded exponent. -/
theorem powers_apply {polynomial : DensePolynomial K} (companion : Companion polynomial) (point : K)
    (index : Fin polynomial.natDegree) : companion.powers point index = point ^ index.val :=
  vectorOfFn_apply _ index

/-- The original positive degree supplies a bounded first power coordinate. -/
@[expose] def firstIndex {polynomial : DensePolynomial K} (companion : Companion polynomial) :
    Fin polynomial.natDegree := ⟨0, companion.positive⟩

/-- The original first power-vector component is one. -/
theorem powers_first {polynomial : DensePolynomial K} (companion : Companion polynomial) (point : K) :
    companion.powers point companion.firstIndex = 1 := by
  rewrite [powers_apply]
  exact pow_zero point

/-- The original source evaluation is its leading monomial plus the same retained lower-coefficient power sum. -/
theorem source_evaluation {polynomial : DensePolynomial K} (companion : Companion polynomial) (point : K) :
    polynomial.eval point = polynomial.leadingCoeff * point ^ polynomial.natDegree +
      Fin.sumFin (fun index : Fin polynomial.natDegree =>
        getD companion.coefficients index.val 0 * point ^ index.val) :=
    by
  have lower := DensePolynomial.evalCoeffs_reverse_sum point companion.coefficients
  have originalLower : DensePolynomial.evalCoeffs point companion.coefficients.reverse =
      Fin.sumFin (fun index : Fin polynomial.natDegree =>
        getD companion.coefficients index.val 0 * point ^ index.val) := companion.count_eq ▸ lower
  rewrite [← DensePolynomial.eval_normalize polynomial point]
  change DensePolynomial.evalCoeffs point polynomial.normalize.coeffs = _
  rewrite [companion.source_eq, DensePolynomial.evalCoeffs_cons_expansion,
    Reverse.length_reverse, companion.count_eq, originalLower]
  rfl

/-- The same feedback-vector power sum is the normalized negative original lower-polynomial evaluation. -/
theorem feedback_evaluation {polynomial : DensePolynomial K} (companion : Companion polynomial) (point : K) :
    Fin.sumFin (fun index : Fin polynomial.natDegree =>
        companion.feedback index * companion.powers point index) =
      -(Fin.sumFin (fun index : Fin polynomial.natDegree =>
        getD companion.coefficients index.val 0 * point ^ index.val) * companion.leadingInverse) := by
  calc
    _ = Fin.sumFin (fun index : Fin polynomial.natDegree =>
        (getD companion.coefficients index.val 0 * point ^ index.val) * -companion.leadingInverse) := by
      apply Fin.sumFin_congr
      intro index
      rewrite [companion.feedback_eq index, powers_apply]
      ring0
    _ = _ := by
      rewrite [Fin.sumFin_mul_right, mul_neg]
      rfl

/-- The normalized original polynomial residual at the actual terminal companion row. -/
@[expose] def residual {polynomial : DensePolynomial K} (companion : Companion polynomial) (point : K)
    (row : Fin polynomial.natDegree) : K :=
  if row.val + 1 = polynomial.natDegree then polynomial.eval point * companion.leadingInverse else 0

/-- The original companion action keeps the exact source-polynomial residual in its actual terminal row.

Every preceding row shifts to the next original power. The terminal feedback
row contributes the original polynomial value times its nonzero leading
inverse; no input root or approximate-eigenvalue claim is assumed.
-/
theorem action {polynomial : DensePolynomial K} (companion : Companion polynomial) (point : K)
    (row : Fin polynomial.natDegree) :
    SquareMatrix.Multiplication.matrixVector companion.matrix (companion.powers point) row =
      point * companion.powers point row -
        (if row.val + 1 = polynomial.natDegree then polynomial.eval point * companion.leadingInverse else 0) := by
  rewrite [companion.matrix_eq, SquareMatrix.Multiplication.matrixVector_apply]
  by_cases next : row.val + 1 < polynomial.natDegree
  · have different : row.val + 1 ≠ polynomial.natDegree := Nat.ne_of_lt next
    rewrite [if_neg different]
    have subtractZero : point * companion.powers point row - 0 = point * companion.powers point row := by ring0
    rewrite [subtractZero]
    let column : Fin polynomial.natDegree := ⟨row.val + 1, next⟩
    calc
      _ = Fin.sumFin (fun index : Fin polynomial.natDegree =>
          if index = column then companion.powers point index else 0) := by
        apply Fin.sumFin_congr
        intro index
        rewrite [matrixOfFeedback, SquareMatrix.matrixOfFn_apply, dif_pos next]
        change (if index = column then 1 else 0) * companion.powers point index = _
        split
        · rewrite [one_mul]; rfl
        · rewrite [zero_mul]; rfl
      _ = companion.powers point column := Fin.sumFin_ite_eq column _
      _ = _ := by
        rewrite [powers_apply, powers_apply, pow_succ]
        exact mul_comm _ _
  · have terminal : row.val + 1 = polynomial.natDegree :=
      Nat.le_antisymm (Nat.succ_le_of_lt row.isLt) (Nat.le_of_not_lt next)
    rewrite [if_pos terminal]
    have feedback : Fin.sumFin (fun index : Fin polynomial.natDegree =>
        matrixOfFeedback companion.feedback row index * companion.powers point index) =
        Fin.sumFin (fun index : Fin polynomial.natDegree =>
          companion.feedback index * companion.powers point index) := by
      apply Fin.sumFin_congr
      intro index
      rewrite [matrixOfFeedback, SquareMatrix.matrixOfFn_apply, dif_neg next]
      rfl
    rewrite [feedback, feedback_evaluation, powers_apply, source_evaluation]
    have power : point * point ^ row.val = point ^ polynomial.natDegree :=
      ((mul_comm point (point ^ row.val)).trans (pow_succ point row.val).symm).trans
        (congrArg (fun exponent => point ^ exponent) terminal)
    rewrite [power]
    have cancelled : polynomial.leadingCoeff * companion.leadingInverse = 1 :=
      companion.leading_unit
    calc
      _ = (1 - polynomial.leadingCoeff * companion.leadingInverse) * point ^ polynomial.natDegree -
          Fin.sumFin (fun index : Fin polynomial.natDegree =>
            getD companion.coefficients index.val 0 * point ^ index.val) * companion.leadingInverse := by
        rewrite [cancelled, sub_self, zero_mul, zero_sub]
        rfl
      _ = _ := by ring0

/-- An original source root makes its retained power vector an eigenvector of the same cached companion matrix. -/
theorem eigenvector {polynomial : DensePolynomial K} (companion : Companion polynomial) (point : K)
    (root : polynomial.eval point = 0) (row : Fin polynomial.natDegree) :
    SquareMatrix.Multiplication.matrixVector companion.matrix (companion.powers point) row =
      point * companion.powers point row := by
  rewrite [action, root, zero_mul]
  split <;> ring0

/-- Every original source root also zeros the polynomial from any retained pencil certificate on its cached companion.

The original source equation supplies the eigenvector law and its actual
first power coordinate supplies the unit. The pencil polynomial need not be
minimal or have the same multiplicity as the original source.
-/
theorem pencil_zero {L : Type*} [ExplicitField L] [DecidableEq L]
    {polynomial : DensePolynomial L} (companion : Companion polynomial)
    (certificate : LinearAlgebra.PolynomialMatrix.Pencil.Certificate companion.matrix) (point : L)
    (root : polynomial.eval point = 0) : certificate.polynomial.eval point = 0 :=
  certificate.eigenvalue_zero point (companion.powers point) companion.firstIndex (companion.powers_first point)
    (companion.eigenvector point root)

end Companion

end Purelib.Polynomial.Dense

end
