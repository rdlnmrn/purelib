module

import Purelib.Data.List.Map

import Purelib.LinearAlgebra.Matrix.Basic
import all Purelib.LinearAlgebra.PolynomialMatrix.Inverse.Scaled.Gaussian.Normalization

public import Purelib.LinearAlgebra.PolynomialMatrix.Map
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Bivariate.Gaussian.Lift
import Purelib.Polynomial.Dense.Bivariate.Gaussian.Reflection.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Components.Selection
public import Purelib.Polynomial.Dense.Gaussian.Map.Identity
import Purelib.Polynomial.Elimination.Separated.Bezout
public import Purelib.Polynomial.Elimination.Separated.Scalar
import Purelib.Polynomial.Elimination.Separated.Sylvester
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.LinearAlgebra.PolynomialMatrix.Basic
import Purelib.LinearAlgebra.PolynomialMatrix.Inverse.Scaled.Basic

open Purelib.Polynomial.Dense.Gaussian (NormalizedPolynomial)

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

namespace Purelib.Polynomial.Elimination.Separated.CanonicalCorrespondence

/-- Identity erasure preserves the finite lifted coefficient list. -/
theorem erase_liftedCoefficients (polynomial :
  NormalizedPolynomial) :
    (Dense.Bivariate.Gaussian.Lift.SeparatedVariables.liftedCoefficients polynomial).map id =
      Dense.Bivariate.Gaussian.Lift.SeparatedVariables.liftedCoefficients
        (id polynomial) := open Purelib in by
  exact Data.List.Map.map_id _
end Purelib.Polynomial.Elimination.Separated.CanonicalCorrespondence

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

namespace Purelib.Polynomial.Elimination.Separated.CanonicalCorrespondence

/-- The normalized rational eliminant is exactly the original selected scalar coordinate polynomial. -/
theorem erase_normalizedEliminant (polynomial :
  Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) :
    id (Elimination.Separated.Scalar.normalizedEliminant polynomial) =
      Elimination.Separated.Scalar.scalarEliminant polynomial := by
  have normalized :=
    Purelib.LinearAlgebra.PolynomialMatrix.Inverse.Scaled.Gaussian.Normalization.scaledInverseScalar_normalized
    (polynomial.natDegree + polynomial.natDegree)
    (Elimination.Separated.Sylvester.separatedSylvester polynomial)
  change (Elimination.Separated.Bezout.separatedData polynomial).scalar.normalize =
    (Elimination.Separated.Bezout.separatedData polynomial).scalar at normalized
  unfold Elimination.Separated.Scalar.normalizedEliminant Elimination.Separated.Scalar.normalizedScalar
    Elimination.Separated.Scalar.scalarEliminant
    Dense.Gaussian.Components.Selection.selectedCoordinate
  rw [normalized]
  rfl
end Purelib.Polynomial.Elimination.Separated.CanonicalCorrespondence

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

namespace Purelib.Polynomial.Elimination.Separated.CanonicalCorrespondence

/-- The complete reduced-record Schur recursion erases to the scalar used by
the existing separated-Sylvester Bézout development. -/
theorem erase_normalizedScalar (polynomial :
  Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) :
    id (Elimination.Separated.Scalar.normalizedScalar polynomial) =
      (Elimination.Separated.Bezout.separatedData polynomial).scalar := by
  rfl

end Purelib.Polynomial.Elimination.Separated.CanonicalCorrespondence

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

namespace Purelib.Polynomial.Elimination.Separated.CanonicalCorrespondence

/-! ## Erasure of separated-variable preparation -/

/-- Identity erasure preserves the finite reflected coefficient list. -/
theorem erase_reflectedCoefficients (polynomial
  : NormalizedPolynomial) :
    (Dense.Bivariate.Gaussian.Reflection.Basic.SeparatedVariables.reflectedCoefficients polynomial).map id =
      Dense.Bivariate.Gaussian.Reflection.Basic.SeparatedVariables.reflectedCoefficients
        (id polynomial) := open Purelib in by
  exact Data.List.Map.map_id _
end Purelib.Polynomial.Elimination.Separated.CanonicalCorrespondence

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

namespace Purelib.Polynomial.Elimination.Separated.CanonicalCorrespondence

/-- Identity erasure preserves the scalar returned by the separated scaled-inverse construction. -/
theorem erase_separatedScalar (polynomial :
  NormalizedPolynomial) :
    id (Elimination.Separated.Bezout.separatedData polynomial).scalar =
      (Elimination.Separated.Bezout.separatedData
        (id polynomial)).scalar := by
  rfl
end Purelib.Polynomial.Elimination.Separated.CanonicalCorrespondence

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

namespace Purelib.Polynomial.Elimination.Separated.CanonicalCorrespondence

/-- Mapping identity erasure over the separated Sylvester matrix preserves every retained polynomial entry. -/
theorem erase_separatedSylvester (polynomial :
  NormalizedPolynomial) :
    PolynomialMatrix.Map.mapMatrix Dense.Gaussian.Map.Identity.eraseEmbedding
        (Elimination.Separated.Sylvester.separatedSylvester polynomial) =
      Elimination.Separated.Sylvester.separatedSylvester
        (id polynomial) := open Purelib in open Purelib.LinearAlgebra renaming Matrix ->
          SquareMatrix in by
  apply SquareMatrix.matrix_ext
  intro row column
  rw [PolynomialMatrix.Map.mapMatrix_apply]
  apply Dense.Basic.DensePolynomial.ext
  change ((Elimination.Separated.Sylvester.separatedSylvester polynomial row column).coeffs.map id) =
    (Elimination.Separated.Sylvester.separatedSylvester polynomial row column).coeffs
  exact Data.List.Map.map_id _
end Purelib.Polynomial.Elimination.Separated.CanonicalCorrespondence

end
