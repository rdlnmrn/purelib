module

import Purelib.Data.Rat.Fraction.Resource.Model
import Purelib.Polynomial.Dense.Rational.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Substitution.QuarterTurn
import Purelib.Polynomial.Dense.Resource
public import Purelib.Polynomial.Elimination.Axis.Separated.Eliminant
import Purelib.Polynomial.Elimination.Separated.CanonicalCorrespondence
public import Purelib.Polynomial.Elimination.Separated.Resource.Scalar
import Purelib.Polynomial.Elimination.Separated.Scalar
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Basic
import Purelib.Data.Rat.Fraction.Field

open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)

open Purelib.Data.Rat

open Purelib.Polynomial

section
@[expose] public section

/-!
# Normalized separated-Sylvester eliminants

The separated-variable preparation and fraction-free Schur data use the
established implementations directly on the same canonical Gaussian scalar.  Thus every persistent Gaussian-rational
coefficient in this
execution is canonical while the paper-facing algebraic API remains stable.
-/

namespace Purelib.Polynomial.Elimination.Axis.Separated.Resource

/-- Compute the horizontal eliminant with canonical rational coefficients.

Apply the normalized separated eliminant to the quarter-turn of the original Gaussian polynomial. -/
def normalizedHorizontalEliminant (polynomial :
  CoefficientPolynomial) :
    Dense.Rational.NormalizedPolynomial :=
  Elimination.Separated.Scalar.normalizedEliminant
    (Dense.Gaussian.Substitution.QuarterTurn.quarterTurn polynomial)
end Purelib.Polynomial.Elimination.Axis.Separated.Resource

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

namespace Purelib.Polynomial.Elimination.Axis.Separated.Resource

/-- The normalized horizontal eliminant is exactly the existing horizontal eliminant. -/
theorem erase_normalizedHorizontalEliminant (polynomial :
  CoefficientPolynomial) :
    id (normalizedHorizontalEliminant polynomial) =
      Elimination.Axis.Separated.Eliminant.horizontalEliminant polynomial := by
  exact Elimination.Separated.CanonicalCorrespondence.erase_normalizedEliminant
    (Dense.Gaussian.Substitution.QuarterTurn.quarterTurn polynomial)
end Purelib.Polynomial.Elimination.Axis.Separated.Resource

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

namespace Purelib.Polynomial.Elimination.Axis.Separated.Resource

/-- The horizontal eliminant coefficients satisfy the magnitude envelope of the quarter-turned polynomial. -/
theorem normalizedHorizontalEliminant_within
    (polynomial : CoefficientPolynomial) :
    Dense.Resource.PolynomialWithin Fraction.Resource.Model.rationalModel
      (normalizedHorizontalEliminant polynomial)
      (Elimination.Separated.Resource.Scalar.eliminantMagnitudeEnvelope
        (Dense.Gaussian.Substitution.QuarterTurn.quarterTurn polynomial)) :=
  Elimination.Separated.Resource.Scalar.normalizedEliminant_within
    (Dense.Gaussian.Substitution.QuarterTurn.quarterTurn polynomial)

end Purelib.Polynomial.Elimination.Axis.Separated.Resource

end
