module

import Purelib.Algebra.Field.ExplicitField
public import Purelib.Data.Gaussian.Basic
import Purelib.Data.List.OfFn.Basic
import Purelib.Data.Vector.Basic
public import Purelib.LinearAlgebra.Matrix.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Arithmetic
public import Purelib.Polynomial.Dense.Multiplication

open Purelib.Algebra.Field

open Purelib

open _root_.Purelib.LinearAlgebra renaming Matrix -> SquareMatrix

open Purelib.Polynomial

section

section
@[expose] public section

/-!
# Polynomial-valued fraction-free matrix inversion

The block recursion is run symbolically over dense coordinate polynomials.
Evaluation at any coordinate commutes with every finite sum and block
operation, so the resulting scalar and matrix specialize to the constructive
scaled inverse from `Purelib.LinearAlgebra`.
-/

namespace Purelib.LinearAlgebra.PolynomialMatrix

/-- A finite dense polynomial over the supplied coefficient type. -/
abbrev Basic.Polynomial (K : Type*) := Dense.Basic.DensePolynomial K
end Purelib.LinearAlgebra.PolynomialMatrix

end

/-!
# Constructive separated-variable polynomials

For a Gaussian polynomial `p`, this module constructs the finite bivariate
pair

`p(U)` and `conj(p)(2T-U)`.

The second polynomial is maintained in low-to-high outer coefficients.  A
finite invariant shows that only its constant-in-`U` coefficient reaches the
top parameter degree.  This is precisely the triangular leading-coefficient
fact needed by the Sylvester scaled-inverse recursion.
-/

end

section

section
@[expose] public section

/-!
# Polynomial-valued fraction-free matrix inversion

The block recursion is run symbolically over dense coordinate polynomials.
Evaluation at any coordinate commutes with every finite sum and block
operation, so the resulting scalar and matrix specialize to the constructive
scaled inverse from `Purelib.LinearAlgebra`.
-/

namespace Purelib.LinearAlgebra.PolynomialMatrix
open Purelib.LinearAlgebra in
/-- A finite square structural matrix of dense coefficient polynomials. -/
abbrev Basic.Matrix (K : Type*) (n : Nat) :=
  SquareMatrix (PolynomialMatrix.Basic.Polynomial K) n

end Purelib.LinearAlgebra.PolynomialMatrix

end

/-!
# Constructive separated-variable polynomials

For a Gaussian polynomial `p`, this module constructs the finite bivariate
pair

`p(U)` and `conj(p)(2T-U)`.

The second polynomial is maintained in low-to-high outer coefficients.  A
finite invariant shows that only its constant-in-`U` coefficient reaches the
top parameter degree.  This is precisely the triangular leading-coefficient
fact needed by the Sylvester scaled-inverse recursion.
-/

end

section

section
@[expose] public section

/-!
# Polynomial-valued fraction-free matrix inversion

The block recursion is run symbolically over dense coordinate polynomials.
Evaluation at any coordinate commutes with every finite sum and block
operation, so the resulting scalar and matrix specialize to the constructive
scaled inverse from `Purelib.LinearAlgebra`.
-/

namespace Purelib.LinearAlgebra.PolynomialMatrix
open Purelib.LinearAlgebra in
/-- A structural vector of dense coefficient polynomials with retained finite length. -/
abbrev Basic.Vector (K : Type*) (n : Nat) :=
  Data.Vector (PolynomialMatrix.Basic.Polynomial K) n
end Purelib.LinearAlgebra.PolynomialMatrix

end

/-!
# Constructive separated-variable polynomials

For a Gaussian polynomial `p`, this module constructs the finite bivariate
pair

`p(U)` and `conj(p)(2T-U)`.

The second polynomial is maintained in low-to-high outer coefficients.  A
finite invariant shows that only its constant-in-`U` coefficient reaches the
top parameter degree.  This is precisely the triangular leading-coefficient
fact needed by the Sylvester scaled-inverse recursion.
-/

end

section

section

/-!
# Polynomial-valued fraction-free matrix inversion

The block recursion is run symbolically over dense coordinate polynomials.
Evaluation at any coordinate commutes with every finite sum and block
operation, so the resulting scalar and matrix specialize to the constructive
scaled inverse from `Purelib.LinearAlgebra`.
-/

section
@[expose] public section

/-!
# Constructive separated-variable polynomials

For a Gaussian polynomial `p`, this module constructs the finite bivariate
pair

`p(U)` and `conj(p)(2T-U)`.

The second polynomial is maintained in low-to-high outer coefficients.  A
finite invariant shows that only its constant-in-`U` coefficient reaches the
top parameter degree.  This is precisely the triangular leading-coefficient
fact needed by the Sylvester scaled-inverse recursion.
-/

namespace Purelib.LinearAlgebra.PolynomialMatrix.Basic

open Purelib.LinearAlgebra in
/-- A finite square matrix of dense Gaussian rational polynomials. -/
abbrev GaussianMatrix (n : Nat) :=
  Matrix Data.Gaussian.Basic.Canonical n
end Purelib.LinearAlgebra.PolynomialMatrix.Basic
end

end

section

section
@[expose] public section

/-!
# Polynomial-valued fraction-free matrix inversion

The block recursion is run symbolically over dense coordinate polynomials.
Evaluation at any coordinate commutes with every finite sum and block
operation, so the resulting scalar and matrix specialize to the constructive
scaled inverse from `Purelib.LinearAlgebra`.
-/

namespace Purelib.LinearAlgebra.PolynomialMatrix
variable {K : Type*} [ExplicitField K] [DecidableEq K]

open Purelib.LinearAlgebra in
/-- Read the polynomial in the leading entry of a nonempty square matrix. -/
def Basic.head (matrix : PolynomialMatrix.Basic.Matrix K (n + 1)) :
  PolynomialMatrix.Basic.Polynomial K := matrix 0 0
end Purelib.LinearAlgebra.PolynomialMatrix

end

/-!
# Constructive separated-variable polynomials

For a Gaussian polynomial `p`, this module constructs the finite bivariate
pair

`p(U)` and `conj(p)(2T-U)`.

The second polynomial is maintained in low-to-high outer coefficients.  A
finite invariant shows that only its constant-in-`U` coefficient reaches the
top parameter degree.  This is precisely the triangular leading-coefficient
fact needed by the Sylvester scaled-inverse recursion.
-/

end

section

section
@[expose] public section

/-!
# Polynomial-valued fraction-free matrix inversion

The block recursion is run symbolically over dense coordinate polynomials.
Evaluation at any coordinate commutes with every finite sum and block
operation, so the resulting scalar and matrix specialize to the constructive
scaled inverse from `Purelib.LinearAlgebra`.
-/

namespace Purelib.LinearAlgebra.PolynomialMatrix
variable {K : Type*} [ExplicitField K] [DecidableEq K]

open Purelib.LinearAlgebra in
/-- Materialize the first polynomial column after deleting its leading entry. -/
def Basic.leftColumn (matrix : PolynomialMatrix.Basic.Matrix K (n + 1)) :
  PolynomialMatrix.Basic.Vector K n :=
  Data.Vector.Basic.vectorOfFn fun row => matrix row.succ 0

end Purelib.LinearAlgebra.PolynomialMatrix

end

/-!
# Constructive separated-variable polynomials

For a Gaussian polynomial `p`, this module constructs the finite bivariate
pair

`p(U)` and `conj(p)(2T-U)`.

The second polynomial is maintained in low-to-high outer coefficients.  A
finite invariant shows that only its constant-in-`U` coefficient reaches the
top parameter degree.  This is precisely the triangular leading-coefficient
fact needed by the Sylvester scaled-inverse recursion.
-/

end

section

section
@[expose] public section

/-!
# Polynomial-valued fraction-free matrix inversion

The block recursion is run symbolically over dense coordinate polynomials.
Evaluation at any coordinate commutes with every finite sum and block
operation, so the resulting scalar and matrix specialize to the constructive
scaled inverse from `Purelib.LinearAlgebra`.
-/

namespace Purelib.LinearAlgebra.PolynomialMatrix
variable {K : Type*} [ExplicitField K] [DecidableEq K]
omit [ExplicitField K] [DecidableEq K] in
open Purelib.LinearAlgebra in
/-- Read a retained left-column polynomial at the corresponding successor row. -/
@[simp] theorem Basic.leftColumn_apply (matrix :
  PolynomialMatrix.Basic.Matrix K (n + 1))
    (row : Fin n) :
    PolynomialMatrix.Basic.leftColumn matrix row = matrix row.succ 0 := by
  exact Data.Vector.Basic.vectorOfFn_apply _ _
end Purelib.LinearAlgebra.PolynomialMatrix

end

/-!
# Constructive separated-variable polynomials

For a Gaussian polynomial `p`, this module constructs the finite bivariate
pair

`p(U)` and `conj(p)(2T-U)`.

The second polynomial is maintained in low-to-high outer coefficients.  A
finite invariant shows that only its constant-in-`U` coefficient reaches the
top parameter degree.  This is precisely the triangular leading-coefficient
fact needed by the Sylvester scaled-inverse recursion.
-/

end

section

section
@[expose] public section

/-!
# Polynomial-valued fraction-free matrix inversion

The block recursion is run symbolically over dense coordinate polynomials.
Evaluation at any coordinate commutes with every finite sum and block
operation, so the resulting scalar and matrix specialize to the constructive
scaled inverse from `Purelib.LinearAlgebra`.
-/

namespace Purelib.LinearAlgebra.PolynomialMatrix
variable {K : Type*} [ExplicitField K] [DecidableEq K]

open Purelib.LinearAlgebra in
/-- Construct the square identity matrix scaled by the supplied dense polynomial. -/
def Basic.scaleIdentity {n : Nat} (a : PolynomialMatrix.Basic.Polynomial
  K) : PolynomialMatrix.Basic.Matrix K n :=
  SquareMatrix.matrixOfFn fun row column =>
    if row = column then a else 0
end Purelib.LinearAlgebra.PolynomialMatrix

end

/-!
# Constructive separated-variable polynomials

For a Gaussian polynomial `p`, this module constructs the finite bivariate
pair

`p(U)` and `conj(p)(2T-U)`.

The second polynomial is maintained in low-to-high outer coefficients.  A
finite invariant shows that only its constant-in-`U` coefficient reaches the
top parameter degree.  This is precisely the triangular leading-coefficient
fact needed by the Sylvester scaled-inverse recursion.
-/

end

section

section
@[expose] public section

/-!
# Polynomial-valued fraction-free matrix inversion

The block recursion is run symbolically over dense coordinate polynomials.
Evaluation at any coordinate commutes with every finite sum and block
operation, so the resulting scalar and matrix specialize to the constructive
scaled inverse from `Purelib.LinearAlgebra`.
-/

namespace Purelib.LinearAlgebra.PolynomialMatrix
variable {K : Type*} [ExplicitField K] [DecidableEq K]

open Purelib.LinearAlgebra in
/-- Sum a finite indexed family of dense polynomials in index order.

The fold starts at the zero polynomial and uses the existing normalized addition operation. -/
def Basic.sumFin {n : Nat} (values : Fin n →
  PolynomialMatrix.Basic.Polynomial K) : PolynomialMatrix.Basic.Polynomial K :=
  (List.ofFn values).foldl (fun a b => a + b) 0
end Purelib.LinearAlgebra.PolynomialMatrix

end

/-!
# Constructive separated-variable polynomials

For a Gaussian polynomial `p`, this module constructs the finite bivariate
pair

`p(U)` and `conj(p)(2T-U)`.

The second polynomial is maintained in low-to-high outer coefficients.  A
finite invariant shows that only its constant-in-`U` coefficient reaches the
top parameter degree.  This is precisely the triangular leading-coefficient
fact needed by the Sylvester scaled-inverse recursion.
-/

end

section

section
@[expose] public section

/-!
# Polynomial-valued fraction-free matrix inversion

The block recursion is run symbolically over dense coordinate polynomials.
Evaluation at any coordinate commutes with every finite sum and block
operation, so the resulting scalar and matrix specialize to the constructive
scaled inverse from `Purelib.LinearAlgebra`.
-/

namespace Purelib.LinearAlgebra.PolynomialMatrix
variable {K : Type*} [ExplicitField K] [DecidableEq K]

open Purelib.LinearAlgebra in
/-- Sum the coordinatewise products of two retained polynomial vectors. -/
def Basic.dot {n : Nat} (left right : PolynomialMatrix.Basic.Vector K n) :
  PolynomialMatrix.Basic.Polynomial K :=
  PolynomialMatrix.Basic.sumFin (fun i => left i * right i)
end Purelib.LinearAlgebra.PolynomialMatrix

end

/-!
# Constructive separated-variable polynomials

For a Gaussian polynomial `p`, this module constructs the finite bivariate
pair

`p(U)` and `conj(p)(2T-U)`.

The second polynomial is maintained in low-to-high outer coefficients.  A
finite invariant shows that only its constant-in-`U` coefficient reaches the
top parameter degree.  This is precisely the triangular leading-coefficient
fact needed by the Sylvester scaled-inverse recursion.
-/

end

section

section
@[expose] public section

/-!
# Polynomial-valued fraction-free matrix inversion

The block recursion is run symbolically over dense coordinate polynomials.
Evaluation at any coordinate commutes with every finite sum and block
operation, so the resulting scalar and matrix specialize to the constructive
scaled inverse from `Purelib.LinearAlgebra`.
-/

namespace Purelib.LinearAlgebra.PolynomialMatrix
variable {K : Type*} [ExplicitField K] [DecidableEq K]

open Purelib.LinearAlgebra in
/-- Multiply a polynomial matrix by a structural polynomial column vector.

Each output coordinate is the finite dot product with its original matrix row. -/
def Basic.matrixVector {n : Nat} (matrix : PolynomialMatrix.Basic.Matrix K
  n) (vector : PolynomialMatrix.Basic.Vector K n) :
    PolynomialMatrix.Basic.Vector K n :=
  Data.Vector.Basic.vectorOfFn fun row => PolynomialMatrix.Basic.dot (matrix row) vector
end Purelib.LinearAlgebra.PolynomialMatrix

end

/-!
# Constructive separated-variable polynomials

For a Gaussian polynomial `p`, this module constructs the finite bivariate
pair

`p(U)` and `conj(p)(2T-U)`.

The second polynomial is maintained in low-to-high outer coefficients.  A
finite invariant shows that only its constant-in-`U` coefficient reaches the
top parameter degree.  This is precisely the triangular leading-coefficient
fact needed by the Sylvester scaled-inverse recursion.
-/

end

section

section
@[expose] public section

/-!
# Polynomial-valued fraction-free matrix inversion

The block recursion is run symbolically over dense coordinate polynomials.
Evaluation at any coordinate commutes with every finite sum and block
operation, so the resulting scalar and matrix specialize to the constructive
scaled inverse from `Purelib.LinearAlgebra`.
-/

namespace Purelib.LinearAlgebra.PolynomialMatrix
variable {K : Type*} [ExplicitField K] [DecidableEq K]

open Purelib.LinearAlgebra in
/-- Multiply two structural square polynomial matrices.

Each retained output entry is the finite dot product of an original row with an original column. -/
def Basic.mul {n : Nat} (left right : PolynomialMatrix.Basic.Matrix K n) :
  PolynomialMatrix.Basic.Matrix K n :=
  SquareMatrix.matrixOfFn fun row column =>
    PolynomialMatrix.Basic.dot (left row) (Data.Vector.Basic.vectorOfFn fun middle =>
      right middle column)
end Purelib.LinearAlgebra.PolynomialMatrix

end

/-!
# Constructive separated-variable polynomials

For a Gaussian polynomial `p`, this module constructs the finite bivariate
pair

`p(U)` and `conj(p)(2T-U)`.

The second polynomial is maintained in low-to-high outer coefficients.  A
finite invariant shows that only its constant-in-`U` coefficient reaches the
top parameter degree.  This is precisely the triangular leading-coefficient
fact needed by the Sylvester scaled-inverse recursion.
-/

end

section

section
@[expose] public section

/-!
# Polynomial-valued fraction-free matrix inversion

The block recursion is run symbolically over dense coordinate polynomials.
Evaluation at any coordinate commutes with every finite sum and block
operation, so the resulting scalar and matrix specialize to the constructive
scaled inverse from `Purelib.LinearAlgebra`.
-/

namespace Purelib.LinearAlgebra.PolynomialMatrix
variable {K : Type*} [ExplicitField K] [DecidableEq K]

open Purelib.LinearAlgebra in
/-- Pointwise equal polynomial families have equal finite sums. -/
theorem Basic.sumFin_congr {n : Nat} {left right : Fin n →
  PolynomialMatrix.Basic.Polynomial K}
    (equal : ∀ index, left index = right index) :
    PolynomialMatrix.Basic.sumFin left = PolynomialMatrix.Basic.sumFin right := by
  unfold PolynomialMatrix.Basic.sumFin
  rw [Data.List.OfFn.Basic.ofFn_congr equal]
end Purelib.LinearAlgebra.PolynomialMatrix

end

/-!
# Constructive separated-variable polynomials

For a Gaussian polynomial `p`, this module constructs the finite bivariate
pair

`p(U)` and `conj(p)(2T-U)`.

The second polynomial is maintained in low-to-high outer coefficients.  A
finite invariant shows that only its constant-in-`U` coefficient reaches the
top parameter degree.  This is precisely the triangular leading-coefficient
fact needed by the Sylvester scaled-inverse recursion.
-/

end

section

section
@[expose] public section

/-!
# Polynomial-valued fraction-free matrix inversion

The block recursion is run symbolically over dense coordinate polynomials.
Evaluation at any coordinate commutes with every finite sum and block
operation, so the resulting scalar and matrix specialize to the constructive
scaled inverse from `Purelib.LinearAlgebra`.
-/

namespace Purelib.LinearAlgebra.PolynomialMatrix
variable {K : Type*} [ExplicitField K] [DecidableEq K]

open Purelib.LinearAlgebra in
/-- Delete the leading row and column of a polynomial matrix. -/
def Basic.tail (matrix : PolynomialMatrix.Basic.Matrix K (n + 1)) :
  PolynomialMatrix.Basic.Matrix K n :=
  SquareMatrix.matrixOfFn fun row column =>
    matrix row.succ column.succ

end Purelib.LinearAlgebra.PolynomialMatrix

end

/-!
# Constructive separated-variable polynomials

For a Gaussian polynomial `p`, this module constructs the finite bivariate
pair

`p(U)` and `conj(p)(2T-U)`.

The second polynomial is maintained in low-to-high outer coefficients.  A
finite invariant shows that only its constant-in-`U` coefficient reaches the
top parameter degree.  This is precisely the triangular leading-coefficient
fact needed by the Sylvester scaled-inverse recursion.
-/

end

section

section
@[expose] public section

/-!
# Polynomial-valued fraction-free matrix inversion

The block recursion is run symbolically over dense coordinate polynomials.
Evaluation at any coordinate commutes with every finite sum and block
operation, so the resulting scalar and matrix specialize to the constructive
scaled inverse from `Purelib.LinearAlgebra`.
-/

namespace Purelib.LinearAlgebra.PolynomialMatrix
variable {K : Type*} [ExplicitField K] [DecidableEq K]
omit [ExplicitField K] [DecidableEq K] in
open Purelib.LinearAlgebra in
/-- Read a tail polynomial at its original successor row and column. -/
@[simp] theorem Basic.tail_apply (matrix : PolynomialMatrix.Basic.Matrix K
  (n + 1))
    (row column : Fin n) :
    PolynomialMatrix.Basic.tail matrix row column = matrix row.succ column.succ := by
  exact SquareMatrix.matrixOfFn_apply _ _ _
end Purelib.LinearAlgebra.PolynomialMatrix

end

/-!
# Constructive separated-variable polynomials

For a Gaussian polynomial `p`, this module constructs the finite bivariate
pair

`p(U)` and `conj(p)(2T-U)`.

The second polynomial is maintained in low-to-high outer coefficients.  A
finite invariant shows that only its constant-in-`U` coefficient reaches the
top parameter degree.  This is precisely the triangular leading-coefficient
fact needed by the Sylvester scaled-inverse recursion.
-/

end

section

section
@[expose] public section

/-!
# Polynomial-valued fraction-free matrix inversion

The block recursion is run symbolically over dense coordinate polynomials.
Evaluation at any coordinate commutes with every finite sum and block
operation, so the resulting scalar and matrix specialize to the constructive
scaled inverse from `Purelib.LinearAlgebra`.
-/

namespace Purelib.LinearAlgebra.PolynomialMatrix
variable {K : Type*} [ExplicitField K] [DecidableEq K]

open Purelib.LinearAlgebra in
/-- Materialize the first polynomial row after deleting its leading entry. -/
def Basic.topRow (matrix : PolynomialMatrix.Basic.Matrix K (n + 1)) :
  PolynomialMatrix.Basic.Vector K n :=
  Data.Vector.Basic.vectorOfFn fun column =>
    matrix 0 column.succ
end Purelib.LinearAlgebra.PolynomialMatrix

end

/-!
# Constructive separated-variable polynomials

For a Gaussian polynomial `p`, this module constructs the finite bivariate
pair

`p(U)` and `conj(p)(2T-U)`.

The second polynomial is maintained in low-to-high outer coefficients.  A
finite invariant shows that only its constant-in-`U` coefficient reaches the
top parameter degree.  This is precisely the triangular leading-coefficient
fact needed by the Sylvester scaled-inverse recursion.
-/

end

section

section
@[expose] public section

/-!
# Polynomial-valued fraction-free matrix inversion

The block recursion is run symbolically over dense coordinate polynomials.
Evaluation at any coordinate commutes with every finite sum and block
operation, so the resulting scalar and matrix specialize to the constructive
scaled inverse from `Purelib.LinearAlgebra`.
-/

namespace Purelib.LinearAlgebra.PolynomialMatrix
variable {K : Type*} [ExplicitField K] [DecidableEq K]

open Purelib.LinearAlgebra in
/-- Compute the fraction-free Schur complement over dense polynomials.

Each tail entry is multiplied by the leading pivot and corrected by its left-column and top-row product. -/
def Basic.schur (matrix : PolynomialMatrix.Basic.Matrix K (n + 1)) :
  PolynomialMatrix.Basic.Matrix K n :=
  SquareMatrix.matrixOfFn fun row column =>
    PolynomialMatrix.Basic.head matrix * PolynomialMatrix.Basic.tail matrix row column -
      PolynomialMatrix.Basic.leftColumn matrix row * PolynomialMatrix.Basic.topRow matrix column
end Purelib.LinearAlgebra.PolynomialMatrix

end

/-!
# Constructive separated-variable polynomials

For a Gaussian polynomial `p`, this module constructs the finite bivariate
pair

`p(U)` and `conj(p)(2T-U)`.

The second polynomial is maintained in low-to-high outer coefficients.  A
finite invariant shows that only its constant-in-`U` coefficient reaches the
top parameter degree.  This is precisely the triangular leading-coefficient
fact needed by the Sylvester scaled-inverse recursion.
-/

end

section

section
@[expose] public section

/-!
# Polynomial-valued fraction-free matrix inversion

The block recursion is run symbolically over dense coordinate polynomials.
Evaluation at any coordinate commutes with every finite sum and block
operation, so the resulting scalar and matrix specialize to the constructive
scaled inverse from `Purelib.LinearAlgebra`.
-/

namespace Purelib.LinearAlgebra.PolynomialMatrix
variable {K : Type*} [ExplicitField K] [DecidableEq K]

open Purelib.LinearAlgebra in
/-- Read one polynomial Schur-complement entry by the explicit pivot correction formula. -/
theorem Basic.schur_apply (matrix : PolynomialMatrix.Basic.Matrix K (n +
  1))
    (row column : Fin n) :
    PolynomialMatrix.Basic.schur matrix row column =
      PolynomialMatrix.Basic.head matrix * PolynomialMatrix.Basic.tail matrix row column -
        PolynomialMatrix.Basic.leftColumn matrix row * PolynomialMatrix.Basic.topRow matrix column := by
  unfold PolynomialMatrix.Basic.schur
  rw [SquareMatrix.matrixOfFn_apply]
end Purelib.LinearAlgebra.PolynomialMatrix

end

/-!
# Constructive separated-variable polynomials

For a Gaussian polynomial `p`, this module constructs the finite bivariate
pair

`p(U)` and `conj(p)(2T-U)`.

The second polynomial is maintained in low-to-high outer coefficients.  A
finite invariant shows that only its constant-in-`U` coefficient reaches the
top parameter degree.  This is precisely the triangular leading-coefficient
fact needed by the Sylvester scaled-inverse recursion.
-/

end

section

section
@[expose] public section

/-!
# Polynomial-valued fraction-free matrix inversion

The block recursion is run symbolically over dense coordinate polynomials.
Evaluation at any coordinate commutes with every finite sum and block
operation, so the resulting scalar and matrix specialize to the constructive
scaled inverse from `Purelib.LinearAlgebra`.
-/

namespace Purelib.LinearAlgebra.PolynomialMatrix
variable {K : Type*} [ExplicitField K] [DecidableEq K]
omit [ExplicitField K] [DecidableEq K] in
open Purelib.LinearAlgebra in
/-- Read a retained top-row polynomial at the corresponding successor column. -/
@[simp] theorem Basic.topRow_apply (matrix : PolynomialMatrix.Basic.Matrix
  K (n + 1))
    (column : Fin n) :
    PolynomialMatrix.Basic.topRow matrix column = matrix 0 column.succ := by
  exact Data.Vector.Basic.vectorOfFn_apply _ _

end Purelib.LinearAlgebra.PolynomialMatrix

end

/-!
# Constructive separated-variable polynomials

For a Gaussian polynomial `p`, this module constructs the finite bivariate
pair

`p(U)` and `conj(p)(2T-U)`.

The second polynomial is maintained in low-to-high outer coefficients.  A
finite invariant shows that only its constant-in-`U` coefficient reaches the
top parameter degree.  This is precisely the triangular leading-coefficient
fact needed by the Sylvester scaled-inverse recursion.
-/

end

section

section
@[expose] public section

/-!
# Polynomial-valued fraction-free matrix inversion

The block recursion is run symbolically over dense coordinate polynomials.
Evaluation at any coordinate commutes with every finite sum and block
operation, so the resulting scalar and matrix specialize to the constructive
scaled inverse from `Purelib.LinearAlgebra`.
-/

namespace Purelib.LinearAlgebra.PolynomialMatrix
variable {K : Type*} [ExplicitField K] [DecidableEq K]

open Purelib.LinearAlgebra in
/-- Multiply a structural polynomial row vector by a square polynomial matrix.

Each output coordinate is the finite dot product with the corresponding retained matrix column. -/
def Basic.vectorMatrix {n : Nat} (vector : PolynomialMatrix.Basic.Vector K
  n) (matrix : PolynomialMatrix.Basic.Matrix K n) :
    PolynomialMatrix.Basic.Vector K n :=
  Data.Vector.Basic.vectorOfFn fun column =>
    PolynomialMatrix.Basic.dot vector (Data.Vector.Basic.vectorOfFn fun row =>
      matrix row column)
end Purelib.LinearAlgebra.PolynomialMatrix

end

/-!
# Constructive separated-variable polynomials

For a Gaussian polynomial `p`, this module constructs the finite bivariate
pair

`p(U)` and `conj(p)(2T-U)`.

The second polynomial is maintained in low-to-high outer coefficients.  A
finite invariant shows that only its constant-in-`U` coefficient reaches the
top parameter degree.  This is precisely the triangular leading-coefficient
fact needed by the Sylvester scaled-inverse recursion.
-/

end

section
@[expose] public section

/-!
# Normalized separated-Sylvester eliminants

The separated-variable preparation and fraction-free Schur data use the
established implementations directly on the same canonical Gaussian scalar.  Thus every persistent Gaussian-rational
coefficient in this
execution is canonical while the paper-facing algebraic API remains stable.
-/

namespace Purelib.LinearAlgebra.PolynomialMatrix.Basic
open Purelib.LinearAlgebra in
/-- A finite square matrix of dense Gaussian rational polynomials. -/
abbrev GaussianNumberMatrix (n : Nat) :=
  Matrix Data.Gaussian.Basic.Number n
end Purelib.LinearAlgebra.PolynomialMatrix.Basic
end
