module
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Data.Fin
public import Purelib.LinearAlgebra.Matrix.Basic
import Purelib.Data.Vector.Basic

open Purelib.Algebra.Field

open Purelib

open Purelib.LinearAlgebra.Matrix.Bivariate renaming Square -> BivariateMatrix

open Purelib.LinearAlgebra renaming Matrix -> SquareMatrix

section
@[expose] public section

/-!
# Finite bivariate coordinate polynomials and determinants

Both variables are represented by finite high-to-low coefficient lists.  The
determinant is an explicit Laplace recursion over `Fin n`; it does not use a
sparse polynomial, a generic matrix determinant, or any infinite carrier.
-/

namespace Purelib.LinearAlgebra.Matrix.Minor
variable {K : Type*} [ExplicitField K] [DecidableEq K]

/-- Delete the supplied row and the first column of a finite square matrix.

The smaller structural matrix reads original rows through the retained skip-index map and columns through successor
indices. -/
def scalarFirstColumnMinor {n : Nat}
    (matrix : BivariateMatrix K (n + 1))
    (row : Fin (n + 1)) : BivariateMatrix K n :=
  SquareMatrix.matrixOfFn fun minorRow column =>
    matrix (Data.Fin.skipIndex row minorRow) column.succ
end Purelib.LinearAlgebra.Matrix.Minor

end
