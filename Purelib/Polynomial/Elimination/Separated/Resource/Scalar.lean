module

import Purelib.Algebra.Field.Resource.Magnitude
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Resource
import all Purelib.Data.Gaussian.Resource.List

import Purelib.Data.Gaussian.Resource.Model
import Purelib.Data.List.Map
import Purelib.Data.Nat.Order
public import Purelib.Data.Rat.Fraction.Resource.Model
public import Purelib.LinearAlgebra.PolynomialMatrix.Inverse.Scaled.Resource.Gaussian.Scalar
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Components
import Purelib.Polynomial.Dense.Resource
public import Purelib.Polynomial.Elimination.Separated.Resource.Reflection
public import Purelib.Polynomial.Elimination.Separated.Scalar
import Purelib.Polynomial.Elimination.Separated.Sylvester
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Basic
import Purelib.Data.Rat.Fraction.Field

open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)

open Purelib.Data

open Purelib.Data.Rat

open Purelib.LinearAlgebra

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

namespace Purelib.Polynomial.Elimination.Separated.Resource.Scalar

/-- Compute the separated scalar's coefficient-magnitude envelope from the original polynomial.

The finite scaled-inverse recurrence uses twice the polynomial degree and the source-computed separated-matrix magnitude
bound. -/
def eliminantMagnitudeEnvelope (polynomial :
  CoefficientPolynomial) : Nat :=
  let working := id polynomial
  PolynomialMatrix.Inverse.Scaled.Resource.Gaussian.Scalar.scaledScalarMagnitudeEnvelope
    ((id working).natDegree + (id working).natDegree)
    (Elimination.Separated.Sylvester.separatedSylvester working)
      (Elimination.Separated.Resource.Reflection.separatedMatrixMagnitudeEnvelope working)
end Purelib.Polynomial.Elimination.Separated.Resource.Scalar

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

namespace Purelib.Polynomial.Elimination.Separated.Resource.Scalar

/-- Every coefficient of the retained Gaussian scalar lies within the source-computed magnitude envelope. -/
theorem normalizedScalar_within (polynomial :
  CoefficientPolynomial) :
    Dense.Resource.PolynomialWithin Purelib.Data.Gaussian.Resource.Model.gaussianModel
      (Elimination.Separated.Scalar.normalizedScalar polynomial)
      (eliminantMagnitudeEnvelope polynomial) := open Purelib in by
  let working := id polynomial
  unfold Elimination.Separated.Scalar.normalizedScalar eliminantMagnitudeEnvelope
  apply PolynomialMatrix.Inverse.Scaled.Resource.Gaussian.Scalar.scaledInverseScalar_within
  · exact (Elimination.Separated.Resource.Reflection.source_zero_within working).trans
      (Algebra.Field.Resource.Magnitude.bound_le_grow Purelib.Data.Gaussian.Resource.Model.gaussianModel _ _)
  · have oneWithin : Purelib.Data.Gaussian.Resource.Model.gaussianModel.magnitude (1 : Gaussian.Basic.Number) ≤
        Elimination.Separated.Resource.Reflection.coefficientMagnitude working :=
      ((Data.Nat.Order.le_max_right _ _).trans (Data.Nat.Order.le_max_right _ _)).trans
        (Purelib.Data.Gaussian.Resource.List.foldl_componentMagnitude_max_initial_le working.coeffs _)
    exact oneWithin.trans (Algebra.Field.Resource.Magnitude.bound_le_grow
      Purelib.Data.Gaussian.Resource.Model.gaussianModel _ _)
  · exact Elimination.Separated.Resource.Reflection.separatedSylvester_within working
end Purelib.Polynomial.Elimination.Separated.Resource.Scalar

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

namespace Purelib.Polynomial.Elimination.Separated.Resource.Scalar

/-- Every coefficient of the selected rational eliminant lies within the same source-computed magnitude envelope. -/
theorem normalizedEliminant_within (polynomial :
  CoefficientPolynomial) :
    Dense.Resource.PolynomialWithin Fraction.Resource.Model.rationalModel
      (Elimination.Separated.Scalar.normalizedEliminant polynomial)
      (eliminantMagnitudeEnvelope polynomial) := open Purelib in by
  have scalarWithin := normalizedScalar_within polynomial
  unfold Elimination.Separated.Scalar.normalizedEliminant
  split
  · intro candidate member
    unfold Dense.Gaussian.Components.imagPart at member
    rcases Data.List.Map.mem_map.mp member with ⟨source, sourceMember, rfl⟩
    exact (Gaussian.Resource.imaginaryMagnitude_le source).trans
      (scalarWithin source sourceMember)
  · intro candidate member
    unfold Dense.Gaussian.Components.realPart at member
    rcases Data.List.Map.mem_map.mp member with ⟨source, sourceMember, rfl⟩
    exact (Gaussian.Resource.realMagnitude_le source).trans
      (scalarWithin source sourceMember)
end Purelib.Polynomial.Elimination.Separated.Resource.Scalar

end
