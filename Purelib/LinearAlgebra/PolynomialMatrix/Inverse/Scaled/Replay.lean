module

import Purelib.LinearAlgebra.Matrix.Basic
import Purelib.LinearAlgebra.PolynomialMatrix.Basic
import Purelib.LinearAlgebra.PolynomialMatrix.Inverse.Scaled.Basic
public import Purelib.LinearAlgebra.PolynomialMatrix.Inverse.Scaled.Compute
import Purelib.Polynomial.Dense.Basic

import Purelib.Algebra.Field.ExplicitField
import Purelib.LinearAlgebra.PolynomialMatrix.Inverse.Scaled.Block
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Vector.Basic
import Purelib.Polynomial.Dense.Multiplication
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Algebra.Field

open Purelib.LinearAlgebra renaming Matrix -> SquareMatrix

open Purelib.LinearAlgebra

open Purelib.Polynomial

@[expose] public section

/-!
Checked local restoration of the polynomial inverse recursion used by axis
elimination. Saved data are untrusted. The checks retain their arithmetic
operands and prove exact structural equality, not just a scaled-inverse law.
Local polynomial arithmetic is checked again; recursive inverse construction
is absent from the executable restore path.
-/

namespace Purelib.LinearAlgebra.PolynomialMatrix.Inverse.Scaled.Replay

open Purelib.LinearAlgebra.PolynomialMatrix

variable {K : Type*} [ExplicitField K] [DecidableEq K]

/-- Entrywise equality of the two retained polynomial matrices. -/
def EntriesEqual {n : Nat} (actual expected : PolynomialMatrix.Basic.Matrix K n) : Prop :=
  ∀ row column, actual row column = expected row column

set_option genInjectivity false in
/-- A failed equality check retaining both the actual and expected polynomial data.

Each outcome carries a proof of the specific scalar or matrix-entry discrepancy. -/
inductive Invalid (K : Type*) where
  /-- Retain two scalar polynomials and a proof that their values differ. -/ | scalar (actual expected :
    PolynomialMatrix.Basic.Polynomial K) (failed : actual ≠ expected)
  /-- Retain two matrices and a proof that their entrywise equality specification fails. -/ | entries {n : Nat} (actual
    expected : PolynomialMatrix.Basic.Matrix K n)
      (failed : ¬ PolynomialMatrix.Inverse.Scaled.Replay.EntriesEqual actual expected)

constructive_injectivity Invalid

/-- Check the retained polynomial against its exact expected value.

Success returns the original polynomial with its equality certificate; failure retains both values and their inequality.
-/
def checkScalar (actual expected : PolynomialMatrix.Basic.Polynomial K) :
    Except (PolynomialMatrix.Inverse.Scaled.Replay.Invalid K) { value : PolynomialMatrix.Basic.Polynomial K // value =
      expected } :=
  if equal : actual = expected then .ok ⟨actual, equal⟩
  else .error (.scalar actual expected equal)

/-- Check entrywise equality of the retained polynomial matrix and its expected matrix.

Success preserves the original structural matrix and proves its equality; failure retains a negated entrywise
specification. -/
def checkMatrix {n : Nat} (actual expected : PolynomialMatrix.Basic.Matrix K n) :
    Except (PolynomialMatrix.Inverse.Scaled.Replay.Invalid K) { value : PolynomialMatrix.Basic.Matrix K n // value =
      expected } :=
  if equal : ∀ row column, actual row column = expected row column then
    .ok ⟨actual, SquareMatrix.matrix_ext equal⟩
  else .error (.entries actual expected equal)

/-- A saved complement is tied to this exact parent matrix. -/
abbrev Complement {n : Nat} (matrix : PolynomialMatrix.Basic.Matrix K (n + 1)) :=
  { value : PolynomialMatrix.Basic.Matrix K n // value = PolynomialMatrix.Basic.schur matrix }

open Purelib.LinearAlgebra.PolynomialMatrix.Inverse.Scaled.Replay in
/-- Check a saved matrix against the exact Schur complement of its retained parent.

The returned certificate preserves that original parent identity. -/
def checkComplement {n : Nat} (matrix : PolynomialMatrix.Basic.Matrix K (n + 1))
    (saved : PolynomialMatrix.Basic.Matrix K n) : Except (PolynomialMatrix.Inverse.Scaled.Replay.Invalid K)
      (PolynomialMatrix.Inverse.Scaled.Replay.Complement matrix) :=
  PolynomialMatrix.Inverse.Scaled.Replay.checkMatrix saved (PolynomialMatrix.Basic.schur matrix)

/-- A completed child carries the equation to the original recursion. -/
abbrev Completed {n : Nat} (matrix : PolynomialMatrix.Basic.Matrix K n) :=
  { value : PolynomialMatrix.Inverse.Scaled.Basic.ScaledInverseData K n // value =
    PolynomialMatrix.Inverse.Scaled.Compute.scaledInverseData n matrix }

/-- Retain the unit scalar and empty inverse matrix as the completed zero-dimensional recursion. -/
def base (matrix : PolynomialMatrix.Basic.Matrix K 0) : PolynomialMatrix.Inverse.Scaled.Replay.Completed matrix :=
  ⟨{ scalar := Dense.Basic.DensePolynomial.constant 1
     inverse := SquareMatrix.matrixOfFn fun index => Fin.elim0 index }, rfl⟩

/-- Local scalar and inverse equations reconstruct equality with the original recursive inverse data.

The saved complement and completed child remain tied to the same retained parent matrix. -/
theorem step_eq {n : Nat} (matrix : PolynomialMatrix.Basic.Matrix K (n + 1))
    (complement : PolynomialMatrix.Inverse.Scaled.Replay.Complement matrix) (child :
      PolynomialMatrix.Inverse.Scaled.Replay.Completed complement.val)
    (scalar : PolynomialMatrix.Basic.Polynomial K) (inverse : PolynomialMatrix.Basic.Matrix K (n + 1))
    (scalar_eq : scalar = PolynomialMatrix.Basic.head matrix * child.val.scalar)
    (inverse_eq : inverse = PolynomialMatrix.Inverse.Scaled.Block.blockInverse matrix child.val) :
    (⟨scalar, inverse⟩ : PolynomialMatrix.Inverse.Scaled.Basic.ScaledInverseData K (n + 1)) =
      PolynomialMatrix.Inverse.Scaled.Compute.scaledInverseData (n + 1) matrix := by
  rw [scalar_eq, inverse_eq, child.property, complement.property]
  rfl

open Purelib.LinearAlgebra.PolynomialMatrix.Inverse.Scaled.Replay in
/-- Rebuild the parent ownership proof from local checks and a completed
child. The original recursive producer occurs only in erased proof types. -/
def restore {n : Nat} (matrix : PolynomialMatrix.Basic.Matrix K (n + 1))
    (complement : PolynomialMatrix.Inverse.Scaled.Replay.Complement matrix) (child :
      PolynomialMatrix.Inverse.Scaled.Replay.Completed complement.val)
    (saved : PolynomialMatrix.Inverse.Scaled.Basic.ScaledInverseData K (n + 1)) : Except
      (PolynomialMatrix.Inverse.Scaled.Replay.Invalid K) (PolynomialMatrix.Inverse.Scaled.Replay.Completed matrix) := do
  let scalar ← PolynomialMatrix.Inverse.Scaled.Replay.checkScalar saved.scalar (PolynomialMatrix.Basic.head matrix *
    child.val.scalar)
  let inverse ← PolynomialMatrix.Inverse.Scaled.Replay.checkMatrix saved.inverse
    (PolynomialMatrix.Inverse.Scaled.Block.blockInverse matrix child.val)
  return ⟨⟨scalar.val, inverse.val⟩,
    PolynomialMatrix.Inverse.Scaled.Replay.step_eq matrix complement child scalar.val inverse.val scalar.property
      inverse.property⟩

end Purelib.LinearAlgebra.PolynomialMatrix.Inverse.Scaled.Replay
