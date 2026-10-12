module

import Purelib.Algebra.Field.Resource.Magnitude
import Purelib.Data.Gaussian.Resource.Model
public import Purelib.LinearAlgebra.PolynomialMatrix.Inverse.Scaled.Resource.Gaussian.Data
import Purelib.LinearAlgebra.PolynomialMatrix.Resource.Gaussian.Slots
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Elimination.Separated.Bezout
public import Purelib.Polynomial.Elimination.Separated.Resource.Reflection
import Purelib.Polynomial.Elimination.Separated.Sylvester
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.LinearAlgebra.PolynomialMatrix.Basic

open Purelib.LinearAlgebra

open Purelib.Polynomial

section
@[expose] public section

/-!
# Resource bounds for displayed fraction-free Bézout cofactors

The separated-Sylvester scalar is only one component of the certificate.
This module also bounds the coefficient slots of every polynomial in the
scaled inverse.  The recurrence is source-only: a Schur round doubles the
matrix slot bound, and unwinding a block adds twice the current bound.
-/

namespace Purelib.Polynomial.Elimination.Separated.Resource.Data

/-- Complete source recurrence for the normalized separated-Sylvester scalar
and every displayed inverse/cofactor polynomial. -/
def separatedDataMagnitudeEnvelope
    (polynomial : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) : Nat :=
  let working := id polynomial
  let count := (id working).natDegree +
    (id working).natDegree
  let matrix := Elimination.Separated.Sylvester.separatedSylvester working
  PolynomialMatrix.Inverse.Scaled.Resource.Gaussian.Data.dataMagnitudeEnvelope count
    (PolynomialMatrix.Resource.Gaussian.Slots.matrixSlotBound matrix)
    (Elimination.Separated.Resource.Reflection.separatedMatrixMagnitudeEnvelope working)
end Purelib.Polynomial.Elimination.Separated.Resource.Data

end

section
@[expose] public section

/-!
# Resource bounds for displayed fraction-free Bézout cofactors

The separated-Sylvester scalar is only one component of the certificate.
This module also bounds the coefficient slots of every polynomial in the
scaled inverse.  The recurrence is source-only: a Schur round doubles the
matrix slot bound, and unwinding a block adds twice the current bound.
-/

namespace Purelib.Polynomial.Elimination.Separated.Resource.Data

/-- The separated scaled-inverse data satisfy their source-computed magnitude envelope.

The bound applies to the exact scalar and inverse polynomial data produced by the original finite Sylvester
construction. -/
theorem normalizedSeparatedData_within
    (polynomial : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) :
    PolynomialMatrix.Inverse.Scaled.Resource.Gaussian.Data.DataWithin
      (Elimination.Separated.Bezout.separatedData
        (id polynomial))
      (separatedDataMagnitudeEnvelope polynomial) := open Purelib in open
        Purelib.Data in by
  let working := id polynomial
  let matrix := Elimination.Separated.Sylvester.separatedSylvester working
  apply PolynomialMatrix.Inverse.Scaled.Resource.Gaussian.Data.scaledInverseData_within
  · exact (Elimination.Separated.Resource.Reflection.source_zero_within working).trans
      (Algebra.Field.Resource.Magnitude.bound_le_grow Purelib.Data.Gaussian.Resource.Model.gaussianModel _ _)
  · exact (Elimination.Separated.Resource.Reflection.source_one_within working).trans
      (Algebra.Field.Resource.Magnitude.bound_le_grow Purelib.Data.Gaussian.Resource.Model.gaussianModel _ _)
  · exact PolynomialMatrix.Resource.Gaussian.Slots.matrixSlot_le matrix
  · exact Elimination.Separated.Resource.Reflection.separatedSylvester_within working

end Purelib.Polynomial.Elimination.Separated.Resource.Data

end
