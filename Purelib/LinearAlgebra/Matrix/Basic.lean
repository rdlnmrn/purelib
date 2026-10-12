module

public import Purelib.Data.Vector.Basic
import Mathlib.Tactic.Linter.Lint
import Mathlib.Tactic.TypeStar

open Purelib

section
@[expose] public section

/-!
# Fraction-free finite matrix inversion

Vectors and matrices are dimension-indexed structural `Vector` data, exposed
through entry lookup, and every sum is a fold over `List.ofFn`.  A scaled
inverse records both multiplication identities.  The block extension below
is division-free: a pivot and a scaled inverse of its Schur complement produce
a scaled inverse of the whole matrix.
-/

namespace Purelib.LinearAlgebra

universe u

/-- A square matrix is a structural vector of structural rows. -/
abbrev Matrix (K : Type*) (n : Nat) := Data.Vector
  (Data.Vector K n) n

namespace Matrix

section
open _root_.Purelib.LinearAlgebra renaming Matrix -> SquareMatrix
/-- Materialize an entry function as structural square-matrix data. -/
def matrixOfFn {K : Type*} {n : Nat}
    (entries : Fin n → Fin n → K) : SquareMatrix K n :=
  Data.Vector.Basic.vectorOfFn fun row => Data.Vector.Basic.vectorOfFn (entries row)

/-- Read a materialized matrix entry as the original entry function. -/
@[simp] theorem matrixOfFn_apply {K : Type*} {n : Nat}
    (entries : Fin n → Fin n → K) (row column : Fin n) :
    SquareMatrix.matrixOfFn entries row column = entries row column := by
  rw [SquareMatrix.matrixOfFn, Data.Vector.Basic.vectorOfFn_apply, Data.Vector.Basic.vectorOfFn_apply]

end

open _root_.Purelib.LinearAlgebra renaming Matrix -> SquareMatrix in
/-- Materialize a finite square entry function when coerced to structural matrix data. -/
instance matrixOfFnCoe {K : Type*} {n : Nat} :
    Coe (Fin n → Fin n → K) (SquareMatrix K n) where
  coe := SquareMatrix.matrixOfFn

open _root_.Purelib.LinearAlgebra renaming Matrix -> SquareMatrix
/-- Entrywise equality proves structural equality of a finite matrix. -/
theorem matrix_ext {n : Nat} {left right : SquareMatrix K
  n}
    (equal : ∀ row column, left row column = right row column) :
    left = right := by
  apply Data.Vector.Basic.vector_ext
  intro row
  apply Data.Vector.Basic.vector_ext
  exact equal row

/-- Equal structural matrices have equal entries at the supplied bounded coordinates. -/
theorem matrix_eq_at {n : Nat} {left right : SquareMatrix
  K n}
    (equal : left = right) (row column : Fin n) :
    left row column = right row column :=
  congrArg (fun matrix : SquareMatrix K n => matrix row column) equal

end Matrix

end Purelib.LinearAlgebra

end

section
@[expose] public section

/-!
# Integral unit-pivot changes of basis

The rows are executable finite data. A two-column shear has an explicit
inverse, and its congruence is computed by a quadratic entry formula rather
than by repeated matrix multiplication. No nondegeneracy is assumed for the
remaining matrix.
-/

namespace Purelib.LinearAlgebra.Matrix

variable {n : Nat}

open _root_.Purelib.LinearAlgebra renaming Matrix -> SquareMatrix in
/-- A square structural matrix with integer entries and the supplied dimension. -/
abbrev IntegralMatrix (n : Nat) := SquareMatrix Int n

end Purelib.LinearAlgebra.Matrix

end

section
@[expose] public section

/-!
# Finite bivariate coordinate polynomials and determinants

Both variables are represented by finite high-to-low coefficient lists.  The
determinant is an explicit Laplace recursion over `Fin n`; it does not use a
sparse polynomial, a generic matrix determinant, or any infinite carrier.
-/

namespace Purelib.LinearAlgebra.Matrix.Bivariate
open _root_.Purelib.LinearAlgebra renaming Matrix -> SquareMatrix in
/-- A square structural matrix over the supplied coefficient type. -/
abbrev Square (K : Type*) (n : Nat) :=
  SquareMatrix K n

end Purelib.LinearAlgebra.Matrix.Bivariate

end

section
@[expose] public section

/-!
# Finite genus-one Picard--Lefschetz action

This module evaluates the two adjacent three-strand Artin generators as
explicit integral maps on the displayed genus-one cellular homology.  The
action is folded in the path order locked by `LegendreConventions`; no braid
quotient or remembered analytic monodromy matrix is used.
-/

namespace Purelib.LinearAlgebra.Matrix.Basic

open _root_.Purelib.LinearAlgebra renaming Matrix -> SquareMatrix in
/-- A two-by-two structural matrix with integer entries. -/
abbrev IntegralMatrix := SquareMatrix Int
  2
end Purelib.LinearAlgebra.Matrix.Basic
end

section
section
@[expose] public section

/-!
# Finite-word Legendre fractional transport

This module folds convention-locked integral matrices and their precisely
indexed denominator preparations.  It keeps the unconditional homogeneous
matrix product separate from stepwise productive division, then proves that a
fully prepared fold agrees with one prepared quotient by the folded matrix.
For period transport it also reverses the generator list while transposing
each homology matrix, and proves that this finite fold is exactly the dual
`periodMatrix` action.
-/

namespace Purelib.Riemann.Integration.LegendreFractionalWords

namespace FoldPreparations
end FoldPreparations
end Purelib.Riemann.Integration.LegendreFractionalWords

end

end

section
@[expose] public section

/-!
# Retryable acquisition of Legendre fractional denominators

The generic division preflight is reused at the exact transformed denominator.
A successful retained-state search is converted to the generalized modular
preparation by carrying its based denominator, whole-ball apartness, and
operational equivalence to the original process.
-/

namespace Purelib.Riemann.Integration.LegendreDenominatorAcquisition

end Purelib.Riemann.Integration.LegendreDenominatorAcquisition

end

section
@[expose] public section

/-!
# Composition laws for finite Legendre fractional actions

The normalized Legendre action is first compared homogeneously, without any
division.  Productive composition is introduced only after the inner, outer,
and combined denominators have each been prepared at their exact dependent
names.
-/

namespace Purelib.Riemann.Integration.LegendreFractionalAction

end Purelib.Riemann.Integration.LegendreFractionalAction

end

section
@[expose] public section

/-!
# Finite Gauss--Manin continuation for the Legendre family

Finite root and homology continuation along an open parameter path produces
endpoint periods by the *dual* (transposed) homology action on actual
target-fibre programs.  It does not equate periods on different Legendre
curves.  Shrinking comparisons remain available below as a generic way to
prove that two refinement programs name the same value, without attaching
that stronger statement to changing-fibre continuation.
-/

namespace Purelib.Riemann.Integration.LegendreGaussManin

end Purelib.Riemann.Integration.LegendreGaussManin

end
