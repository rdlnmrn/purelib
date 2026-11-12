module

public import Purelib.LinearAlgebra.PolynomialMatrix.Leading.Triangular
public import Purelib.LinearAlgebra.PolynomialMatrix.Inverse.Scaled.Evaluation
public import Purelib.LinearAlgebra.PolynomialMatrix.Pencil.Preparation
public import Purelib.LinearAlgebra.PolynomialMatrix.Pencil.Adjugate
import Purelib.LinearAlgebra.Matrix.Inverse.Scaled.Basic
import Purelib.LinearAlgebra.Matrix.Multiplication
import Purelib.LinearAlgebra.Matrix.Basic
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.Field.ExplicitField
import Mathlib.Algebra.GroupWithZero.NeZero
import Purelib.Data.Vector.Basic
import Purelib.Data.List.DropWhile.Basic
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Leading
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Polynomial evidence from finite matrix pencils

The original finite matrix determines the pencil ZI-M. Its computed polynomial
scaled inverse has a monic nonzero scalar of a proved finite degree. A displayed
eigenvector with a retained unit component makes that same scalar vanish at
the eigenvalue. Coefficients and inverse data are cached once with their exact
original-matrix construction identities.
-/

public section

namespace Purelib.LinearAlgebra.PolynomialMatrix.Pencil

open Purelib.Algebra.Field (ExplicitField)
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr sumFin_sub sumFin_ite_eq)
open Purelib.LinearAlgebra renaming Matrix -> SquareMatrix
open Purelib.LinearAlgebra.PolynomialMatrix
open Purelib.Polynomial.Dense
open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.Data.List
open Purelib
open Purelib.Data.Vector.Basic (vectorOfFn vectorOfFn_apply vector_ext)

variable {K : Type*} [ExplicitField K] [DecidableEq K] {n : Nat}

/-- The normalized constant polynomial at the supplied original coefficient. -/
private def constant (value : K) : DensePolynomial K :=
  (DensePolynomial.constant value).normalize

/-- A normalized constant occupies at most one retained coefficient slot. -/
private theorem constant_below (value : K) : Leading.DegreeBelow (constant value) 1 where
  normalized := DensePolynomial.normalize_normalize _
  count_le := by
    rewrite [constant, DensePolynomial.degreeCount_normalize]
    exact DropWhile.length_le (fun entry : K => decide (entry = 0)) [value]

/-- The finite coefficient matrix of ZI-M for the original structural matrix M. -/
def coefficients (matrix : SquareMatrix K n) : PolynomialMatrix.Basic.Matrix K n :=
  SquareMatrix.matrixOfFn fun row column =>
    if row = column then
      DensePolynomial.shift 1 (DensePolynomial.constant 1) - constant (matrix row column)
    else -constant (matrix row column)

/-- Each pencil column has degree at most one and leading diagonal coefficient one.

Every off-diagonal coefficient is constant. The original diagonal coefficient
is the monic coordinate polynomial minus the corresponding original matrix
entry, so the leading matrix is the identity.
-/
theorem leading [Nontrivial K] (matrix : SquareMatrix K n) :
    Leading.Triangular.UpperTriangularLeading (coefficients matrix) (fun _ => 1) (fun _ => 1) := by
  have entry (row column : Fin n) :
      (coefficients matrix) row column =
        (if row = column then
          DensePolynomial.shift 1 (DensePolynomial.constant 1) - constant (matrix row column)
        else -constant (matrix row column)) :=
    SquareMatrix.matrixOfFn_apply (K := DensePolynomial K) _ row column
  constructor
  · intro row column
    by_cases same : row = column
    · have equal := (entry row column).trans (if_pos same)
      exact Eq.mpr
        (congrArg (fun polynomial : DensePolynomial K => Leading.DegreeAtMost polynomial 1) equal)
        (Leading.LeadingTerm.subBelow
          (Leading.LeadingTerm.shift 1 (Leading.LeadingTerm.constant one_ne_zero))
          (constant_below _)).atMost
    · have equal := (entry row column).trans (if_neg same)
      exact Eq.mpr
        (congrArg (fun polynomial : DensePolynomial K => Leading.DegreeAtMost polynomial 1) equal)
        (constant_below _).neg.toAtMost
  · intro row column belowDiagonal
    have different : row ≠ column := by
      intro same
      cases same
      exact Nat.lt_irrefl row.val belowDiagonal
    have equal := (entry row column).trans (if_neg different)
    exact Eq.mpr
      (congrArg (fun polynomial : DensePolynomial K => Leading.DegreeBelow polynomial 1) equal)
      (constant_below _).neg
  · intro index
    have equal := (entry index index).trans (if_pos rfl)
    exact Eq.mpr
      (congrArg (fun polynomial : DensePolynomial K => Leading.LeadingTerm polynomial 1 1) equal)
      (Leading.LeadingTerm.subBelow
        (Leading.LeadingTerm.shift 1 (Leading.LeadingTerm.constant one_ne_zero)) (constant_below _))

/-- Evaluating a pencil entry gives its original scalar diagonal-minus-matrix reading. -/
theorem eval_entry (matrix : SquareMatrix K n) (value : K) (row column : Fin n) :
    ((coefficients matrix) row column).eval value =
      (if row = column then value else 0) - matrix row column := by
  rewrite [coefficients, SquareMatrix.matrixOfFn_apply]
  split
  · rewrite [DensePolynomial.eval_sub, DensePolynomial.eval_shift, DensePolynomial.eval_constant,
      pow_one, one_mul, constant, DensePolynomial.eval_normalize, DensePolynomial.eval_constant]
    rfl
  · rewrite [DensePolynomial.eval_neg, constant, DensePolynomial.eval_normalize, DensePolynomial.eval_constant,
      zero_sub]
    rfl

/-- The original evaluated pencil acts by scalar multiplication minus the original matrix action. -/
theorem action (matrix : SquareMatrix K n) (value : K) (vector : Data.Vector K n) (row : Fin n) :
    SquareMatrix.Multiplication.matrixVector (Evaluation.evalMatrix value (coefficients matrix)) vector row =
      value * vector row - SquareMatrix.Multiplication.matrixVector matrix vector row := by
  rewrite [SquareMatrix.Multiplication.matrixVector_apply]
  calc
    _ = sumFin (fun column => (if column = row then value * vector column else 0) -
        matrix row column * vector column) := by
      apply sumFin_congr
      intro column
      rewrite [Evaluation.evalMatrix_apply, eval_entry]
      by_cases same : column = row
      · cases same
        rewrite [if_pos rfl, if_pos rfl, sub_mul]
        rfl
      · rewrite [if_neg same, if_neg (Ne.symm same), sub_mul, zero_mul]
        rfl
    _ = sumFin (fun column => if column = row then value * vector column else 0) -
        sumFin (fun column => matrix row column * vector column) := sumFin_sub _ _
    _ = _ := by
      rewrite [sumFin_ite_eq, SquareMatrix.Multiplication.matrixVector_apply]
      rfl

set_option genInjectivity false in
/-- The actual checked or original construction of retained polynomial data on the same pencil coefficients.

Checked data retains both computed coefficient products. A rejected proposal
retains its exact failure before the unchanged total original recursion is
used on the same retained coefficient matrix.
-/
inductive Construction (coefficients : PolynomialMatrix.Basic.Matrix K n) :
    Inverse.Scaled.Basic.ScaledInverseData K n → Nat → Type _ where
  /-- Retain the actual compact data and its same-input coefficient/monic/degree checks. -/
  | checked {data : Inverse.Scaled.Basic.ScaledInverseData K n}
      (certificate : Preparation.Checked coefficients data) : Construction coefficients data n
  /-- Retain the rejected proposal before the same complete original fallback data. -/
  | fallback {data : Inverse.Scaled.Basic.ScaledInverseData K n}
      (proposed : Inverse.Scaled.Basic.ScaledInverseData K n) (failure : Preparation.Invalid coefficients proposed)
      (same : data = Inverse.Scaled.Compute.scaledInverseData n coefficients) :
      Construction coefficients data (Leading.Triangular.scalarDegree n 1)

constructive_injectivity Construction

namespace Construction

/-- Read the actual retained compact coefficient certificate, preserving a rejected fallback as absence.

The returned record is the same successful construction certificate, including
both original computed products and the actual monic scalar degree. This view
runs no producer or coefficient checker and erases no fallback evidence from
the original construction record.
-/
def checked? {coefficients : PolynomialMatrix.Basic.Matrix K n}
    {data : Inverse.Scaled.Basic.ScaledInverseData K n} {degree : Nat}
    (construction : Construction coefficients data degree) : Option (Preparation.Checked coefficients data) :=
  match construction with
  | .checked certificate => some certificate
  | .fallback _ _ _ => none

end Construction

set_option genInjectivity false in
/-- The original matrix pencil with its actual retained inverse data, two-sided laws and monic scalar degree.

The original structural matrix indexes both retained caches. Their defining
coefficient equation preserves its actual pencil, and the construction retains
checked or fallback data on that same input. Both product identities and the
actual monic degree make the same cached scalar usable by existing consumers.
-/
structure Certificate (matrix : SquareMatrix K n) where
  /-- The actual retained polynomial pencil coefficient matrix. -/
  coefficients : PolynomialMatrix.Basic.Matrix K n
  /-- The retained pencil was built from the original matrix. -/
  coefficients_eq : coefficients = Pencil.coefficients matrix
  /-- The actual retained polynomial scalar and inverse-entry matrix. -/
  data : Inverse.Scaled.Basic.ScaledInverseData K n
  /-- The actual retained scalar degree, which may come from checked compact data or the original fallback. -/
  degree : Nat
  /-- The same-input construction and any actual rejected proposal are retained. -/
  construction : Construction coefficients data degree
  /-- Both original scaled products hold on this same cached data at every argument. -/
  identities : Inverse.Scaled.Coefficients.Specializations coefficients data
  /-- The actual cached scalar is normalized, nonzero and monic at its retained degree. -/
  leading : Leading.LeadingTerm data.scalar degree 1
  /-- A positive original matrix dimension yields a positive actual scalar degree. -/
  degreePositive : 0 < n → 0 < degree

constructive_injectivity Certificate

/-- Check one proposed compact inverse on the original pencil, retaining a complete total fallback on rejection.

The coefficient cache is computed from the same original matrix once. No
caller supplies successful producer evidence: the exact coefficient, scalar
and degree checks select the same actual data or retain the failed proposal.
-/
def prepareWithProposal [Nontrivial K] (matrix : SquareMatrix K n)
    (proposed : Inverse.Scaled.Basic.ScaledInverseData K n) : Certificate matrix :=
  let coefficients := Pencil.coefficients matrix
  match Preparation.check coefficients proposed with
  | .ok checked =>
      ⟨coefficients, rfl, proposed, n, .checked checked, checked.products.specializations,
        checked.leading, fun positive => positive⟩
  | .error failure =>
      let data := Inverse.Scaled.Compute.scaledInverseData n coefficients
      ⟨coefficients, rfl, data, Leading.Triangular.scalarDegree n 1, .fallback proposed failure rfl,
        fun point => Inverse.Scaled.Evaluation.scaledInverseData_spec point n coefficients,
        Leading.Triangular.scaledInverseData_scalar_leading n 1 coefficients (leading matrix),
        fun positive => Leading.Triangular.scalarDegree_pos positive (Nat.zero_lt_succ 0)⟩

/-- Compute and check a degree-generic characteristic/adjugate proposal on the same original matrix.

The finite recurrence uses the original dimension and retains all its matrix
coefficients before polynomial assembly. The exact same-input checker selects
its actual monic scalar and inverse or preserves the failed proposal with the
complete total original fallback. No successful producer hypothesis is needed.
-/
def prepare [Nontrivial K] (matrix : SquareMatrix K n) : Certificate matrix :=
  prepareWithProposal matrix (Adjugate.compute matrix)

namespace Certificate

/-- The same retained monic scalar polynomial of the checked or fallback construction. -/
@[expose] def polynomial {matrix : SquareMatrix K n} (certificate : Certificate matrix) : DensePolynomial K :=
  certificate.data.scalar

/-- The cached pencil scalar is a nonzero coefficient polynomial. -/
theorem nonzero {matrix : SquareMatrix K n} (certificate : Certificate matrix) :
    certificate.polynomial.isZero = false := certificate.leading.nonzero

/-- The actual cached scalar has the degree retained by its same-input checked or fallback construction. -/
theorem degree_eq {matrix : SquareMatrix K n} (certificate : Certificate matrix) :
    certificate.polynomial.natDegree = certificate.degree := certificate.leading.degree_eq

/-- A nonempty original matrix yields a positive-degree cached scalar polynomial. -/
theorem degree_pos {matrix : SquareMatrix K n} (certificate : Certificate matrix) (nonempty : 0 < n) :
    0 < certificate.polynomial.natDegree := by
  rewrite [certificate.degree_eq]
  exact certificate.degreePositive nonempty

/-- Evaluate the same retained inverse data with both original scaled-product identities. -/
def evaluated {matrix : SquareMatrix K n} (certificate : Certificate matrix) (value : K) :
    SquareMatrix.Inverse.Scaled.Basic.ScaledInverse (Evaluation.evalMatrix value certificate.coefficients) where
  scalar := certificate.polynomial.eval value
  inverse := Evaluation.evalMatrix value certificate.data.inverse
  left_identity := (certificate.identities value).1
  right_identity := (certificate.identities value).2

/-- The cached scalar times one original vector component equals the retained inverse action on its pencil residual.

Every residual coordinate is the displayed scalar-vector product minus that
same vector's original matrix action. The retained inverse coefficients and
scalar are evaluated together, so approximate kernel bounds can use this exact
identity without another inverse construction or scalar division.
-/
theorem residual_component {matrix : SquareMatrix K n} (certificate : Certificate matrix) (value : K)
    (vector : Data.Vector K n) (row : Fin n) :
    certificate.polynomial.eval value * vector row =
      SquareMatrix.Multiplication.matrixVector (Evaluation.evalMatrix value certificate.data.inverse)
        (vectorOfFn fun index =>
          value * vector index - SquareMatrix.Multiplication.matrixVector matrix vector index) row := by
  have originalResidual :
      SquareMatrix.Multiplication.matrixVector (Evaluation.evalMatrix value certificate.coefficients) vector =
        vectorOfFn (fun index =>
          value * vector index - SquareMatrix.Multiplication.matrixVector matrix vector index) := by
    apply vector_ext
    intro index
    rewrite [vectorOfFn_apply, certificate.coefficients_eq, action]
    rfl
  exact ((certificate.evaluated value).action_component vector row).trans
    (congrArg (fun residual => SquareMatrix.Multiplication.matrixVector
      (Evaluation.evalMatrix value certificate.data.inverse) residual row) originalResidual)

/-- An original eigenvector with a retained unit coordinate makes the cached pencil scalar vanish at its eigenvalue.

The original matrix action and displayed bounded unit index produce a kernel
vector of this same evaluated pencil. Its retained scaled inverse then forces
the original cached scalar to vanish, including singular intermediate pivots.
-/
theorem eigenvalue_zero {matrix : SquareMatrix K n} (certificate : Certificate matrix) (value : K)
    (vector : Data.Vector K n) (index : Fin n) (unit : vector index = 1)
    (eigenvector : ∀ row, SquareMatrix.Multiplication.matrixVector matrix vector row = value * vector row) :
    certificate.polynomial.eval value = 0 := by
  apply (certificate.evaluated value).scalar_zero_of_kernel_unit vector _ index unit
  intro row
  rewrite [certificate.coefficients_eq, action, eigenvector row]
  exact sub_self _

end Certificate

end Purelib.LinearAlgebra.PolynomialMatrix.Pencil

end
