module
import Purelib.Data.Gaussian.Cast
import Purelib.Polynomial.Elimination.Axis.Certificate
import Purelib.Data.Gaussian.Basic
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Gaussian.Ascending
import Purelib.Polynomial.Dense.Gaussian.Components.Selection
import Purelib.Polynomial.Elimination.Axis.Separated
import Purelib.Polynomial.Elimination.Separated.Bezout
public import Purelib.Polynomial.Elimination.Separated.Scalar
import Purelib.Polynomial.Elimination.Separated.Sylvester

public import Purelib.LinearAlgebra.PolynomialMatrix.Inverse.Scaled.Replay
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Vector.Basic
import Purelib.LinearAlgebra.PolynomialMatrix.Basic
import Purelib.LinearAlgebra.PolynomialMatrix.Inverse.Scaled.Basic
import Purelib.LinearAlgebra.PolynomialMatrix.Inverse.Scaled.Compute
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation

open Purelib.Data

open Purelib.Data.Rat

open Purelib.LinearAlgebra

open Purelib.Polynomial

section
@[expose] public section

/-!
Restore the original axis certificate from checked separated-Sylvester data.
Both the scalar polynomials and the executable Bézout callbacks consume those
data. The degree bound is read from the restored polynomials as well.
These are the existing finite constructors, with their recursive inverse
inputs supplied by exact replay; no alternate eliminant is introduced.
-/

namespace Purelib.Polynomial.Elimination.Separated.Bezout.Replay

open Purelib.Polynomial.Elimination.SylvesterBezout
open Purelib.Polynomial.Dense.Basic.DensePolynomial

/-- Completed replay data for the exact separated Sylvester matrix of the source polynomial. -/
abbrev Saved (p : (Dense.Basic.DensePolynomial
  Gaussian.Basic.Canonical)) :=
  PolynomialMatrix.Inverse.Scaled.Replay.Completed (Elimination.Separated.Sylvester.separatedSylvester p)

variable {p : (Dense.Basic.DensePolynomial Gaussian.Basic.Canonical)}

/-- Read the left Bézout cofactor from the first half of the saved inverse column.

Evaluate its polynomial entries at the supplied Gaussian parameter and retain their low-to-high coefficient order. -/
def left (saved :
  Saved p) (positive : 0 < p.natDegree) (parameter : Gaussian.Basic.Canonical) :
  (Dense.Basic.DensePolynomial Gaussian.Basic.Canonical) :=
  Dense.Gaussian.Ascending.polynomialFromLow p.natDegree fun index =>
    (saved.val.inverse (Fin.castAdd p.natDegree index) (Elimination.Separated.Bezout.firstColumnIndex p positive)).eval
      parameter

/-- Read the right Bézout cofactor from the second half of the saved inverse column.

Evaluate the retained polynomial entries at the supplied Gaussian parameter. -/
def right (saved :
  Saved p) (positive : 0 < p.natDegree) (parameter : Gaussian.Basic.Canonical) :
  (Dense.Basic.DensePolynomial Gaussian.Basic.Canonical) :=
  Dense.Gaussian.Ascending.polynomialFromLow p.natDegree fun index =>
    (saved.val.inverse (Fin.natAdd p.natDegree index) (Elimination.Separated.Bezout.firstColumnIndex p positive)).eval
      parameter

/-- Scale the replayed left cofactor by the inverse of the saved scalar value at a rational parameter. -/
def normalizedLeft (saved :
  Saved p) (positive : 0 < p.natDegree) (parameter : Fraction.Rational) :
  (Dense.Basic.DensePolynomial Gaussian.Basic.Canonical) :=
  Dense.Basic.DensePolynomial.scale (saved.val.scalar.eval (Gaussian.Cast.Path.ofCoordinate parameter))⁻¹
    (left saved positive (Gaussian.Cast.Path.ofCoordinate parameter))

/-- Scale the replayed right cofactor by the inverse of the saved scalar value at a rational parameter. -/
def normalizedRight (saved :
  Saved p) (positive : 0 < p.natDegree) (parameter : Fraction.Rational) :
  (Dense.Basic.DensePolynomial Gaussian.Basic.Canonical) :=
  Dense.Basic.DensePolynomial.scale (saved.val.scalar.eval (Gaussian.Cast.Path.ofCoordinate parameter))⁻¹
    (right saved positive (Gaussian.Cast.Path.ofCoordinate parameter))

/-- Read the selected rational coordinate polynomial of the saved scalar eliminant. -/
def eliminant (saved :
  Saved p) : (Dense.Basic.DensePolynomial Fraction.Rational) :=
  Dense.Gaussian.Components.Selection.selectedCoordinate saved.val.scalar

/-- The replayed eliminant equals the original separated scalar eliminant. -/
theorem eliminant_eq (saved :
  Saved p) : eliminant saved =
  Elimination.Separated.Scalar.scalarEliminant p := by
  unfold eliminant
  rw [saved.property]
  rfl
end Purelib.Polynomial.Elimination.Separated.Bezout.Replay

end
