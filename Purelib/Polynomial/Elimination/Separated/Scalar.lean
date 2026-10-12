module

import Purelib.Data.Gaussian.Cast
import Purelib.Data.Rat.Fraction
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Components
public import Purelib.Polynomial.Dense.Gaussian.Components.Selection
public import Purelib.Polynomial.Elimination.Separated.Bezout
import Purelib.Polynomial.Elimination.Separated.Sylvester
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.LinearAlgebra.PolynomialMatrix.Inverse.Scaled.Basic
import Purelib.Polynomial.Dense.Evaluation

open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Polynomial

section
section
@[expose] public section

/-!
# Finite Bézout extraction from the separated Sylvester inverse

This module turns the first column of the fraction-free scaled inverse into
two explicit dense cofactors.  The only summation identity involved is a
finite shifted coefficient-list calculation.
-/

namespace Purelib.Polynomial.Elimination.Separated.Scalar

/-- Select a rational coordinate polynomial from the retained separated Sylvester scalar. -/
def scalarEliminant (p :
  CoefficientPolynomial) : (Dense.Basic.DensePolynomial Fraction.Rational) :=
  Dense.Gaussian.Components.Selection.selectedCoordinate (Elimination.Separated.Bezout.separatedData p).scalar
end Purelib.Polynomial.Elimination.Separated.Scalar

end

end

section
section
@[expose] public section

/-!
# Finite Bézout extraction from the separated Sylvester inverse

This module turns the first column of the fraction-free scaled inverse into
two explicit dense cofactors.  The only summation identity involved is a
finite shifted coefficient-list calculation.
-/

namespace Purelib.Polynomial.Elimination.Separated.Scalar

/-- The selected rational scalar eliminant is nonzero whenever the original Gaussian polynomial is nonzero. -/
theorem scalarEliminant_nonzero (p :
  CoefficientPolynomial)
    (nonzero : p.isZero = false) :
    (scalarEliminant p).isZero = false :=
  Dense.Gaussian.Components.Selection.selectedCoordinate_nonzero _
    (Elimination.Separated.Sylvester.separatedScalar_nonzero p nonzero)
end Purelib.Polynomial.Elimination.Separated.Scalar

end

end

section
section
@[expose] public section

/-!
# Finite Bézout extraction from the separated Sylvester inverse

This module turns the first column of the fraction-free scaled inverse into
two explicit dense cofactors.  The only summation identity involved is a
finite shifted coefficient-list calculation.
-/

namespace Purelib.Polynomial.Elimination.Separated.Scalar

/-- Nonvanishing of the selected rational eliminant forces the Gaussian Sylvester scalar to be nonzero at the same
embedded parameter. -/
theorem scalar_ne_zero_of_eliminant_eval_ne_zero
    (p : CoefficientPolynomial) (parameter : Fraction.Rational)
    (nonzeroEvaluation : (scalarEliminant p).eval parameter ≠ 0) :
    (Elimination.Separated.Bezout.separatedData p).scalar.eval
      (Gaussian.Cast.Path.ofCoordinate parameter) ≠ 0 := by
  intro scalarZero
  apply nonzeroEvaluation
  rw [scalarEliminant, Dense.Gaussian.Components.Selection.eval_selectedCoordinate]
  rw [scalarZero]
  split <;> rfl
end Purelib.Polynomial.Elimination.Separated.Scalar

end

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

namespace Purelib.Polynomial.Elimination.Separated.Scalar

/-- Read the Gaussian scalar polynomial from the original separated scaled-inverse data. -/
def normalizedScalar (polynomial :
  CoefficientPolynomial) : (Dense.Basic.DensePolynomial
    Gaussian.Basic.Canonical)
  :=
  (Elimination.Separated.Bezout.separatedData (id polynomial)).scalar
end Purelib.Polynomial.Elimination.Separated.Scalar

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

namespace Purelib.Polynomial.Elimination.Separated.Scalar

/-- Read the real or imaginary coordinate of the retained normalized scalar.

Use the imaginary coordinate when its leading coefficient has zero real part, and otherwise use the real coordinate. -/
def normalizedEliminant (polynomial :
  CoefficientPolynomial) :
    (Dense.Basic.DensePolynomial Fraction.Rational) :=
  if (Dense.Basic.DensePolynomial.leadingCoeff
      (Elimination.Separated.Bezout.separatedData polynomial).scalar).re =
      0 then
    Dense.Gaussian.Components.imagPart (normalizedScalar polynomial)
  else Dense.Gaussian.Components.realPart (normalizedScalar polynomial)
end Purelib.Polynomial.Elimination.Separated.Scalar

end
