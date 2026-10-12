module

public import Purelib.LinearAlgebra.PolynomialMatrix.Inverse.Scaled.Resource.Gaussian.Operation
import Purelib.LinearAlgebra.PolynomialMatrix.Resource.Gaussian.Slots
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Elimination.Separated.Sylvester
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.LinearAlgebra.PolynomialMatrix.Basic
import Purelib.Polynomial.Dense.Basic

open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)

open Purelib.LinearAlgebra

open Purelib.Polynomial

section
@[expose] public section

/-!
# RFAP-I calculation-size certificate

This module composes the normalized eliminant/Bézout, Sturm endpoint,
safe-cut, winding, coefficient-clearing, and repeated-subdivision envelopes.
The resulting `T` and `B` are finite recurrences in displayed input data.
-/

namespace Purelib.Polynomial.Elimination.Separated.Normalized.Resource.Operation

/-- Compute the scaled-inverse advancement budget for the separated Sylvester matrix.

The budget uses the actual matrix slot bound and the doubled polynomial degree. -/
def eliminantAdvanceBudget (polynomial :
  CoefficientPolynomial) : Nat :=
  let working := id polynomial
  let matrix := Elimination.Separated.Sylvester.separatedSylvester working
  PolynomialMatrix.Inverse.Scaled.Resource.Gaussian.Operation.dataEnvelopeAdvanceBudget
    ((id working).natDegree +
      (id working).natDegree)
    (PolynomialMatrix.Resource.Gaussian.Slots.matrixSlotBound matrix)
end Purelib.Polynomial.Elimination.Separated.Normalized.Resource.Operation

end

section
@[expose] public section

/-!
# RFAP-I calculation-size certificate

This module composes the normalized eliminant/Bézout, Sturm endpoint,
safe-cut, winding, coefficient-clearing, and repeated-subdivision envelopes.
The resulting `T` and `B` are finite recurrences in displayed input data.
-/

namespace Purelib.Polynomial.Elimination.Separated.Normalized.Resource.Operation

/-- Coarse clause count for lifting and reflecting the displayed coefficient
list and filling the finite separated-Sylvester matrix. -/
def eliminantPreparationBudget (polynomial
  : CoefficientPolynomial) : Nat :=
  let degree := polynomial.natDegree
  let matrixSide := degree + degree
  8 * polynomial.normalize.coeffs.length + matrixSide * matrixSide
end Purelib.Polynomial.Elimination.Separated.Normalized.Resource.Operation

end

section
@[expose] public section

/-!
# RFAP-I calculation-size certificate

This module composes the normalized eliminant/Bézout, Sturm endpoint,
safe-cut, winding, coefficient-clearing, and repeated-subdivision envelopes.
The resulting `T` and `B` are finite recurrences in displayed input data.
-/

namespace Purelib.Polynomial.Elimination.Separated.Normalized.Resource.Operation

/-- Combine preparation and advancement budgets for the separated eliminant.

Both terms are computed from the same displayed Gaussian-rational polynomial. -/
def eliminantOperationBudget (polynomial :
  CoefficientPolynomial) : Nat :=
  eliminantPreparationBudget polynomial +
    eliminantAdvanceBudget polynomial
end Purelib.Polynomial.Elimination.Separated.Normalized.Resource.Operation

end
