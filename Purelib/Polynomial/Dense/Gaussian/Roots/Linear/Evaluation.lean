module

public import Purelib.Polynomial.Dense.Gaussian.Roots.Linear
public import Purelib.Polynomial.Dense.Gaussian.Factorization.Identity
public import Purelib.Polynomial.Dense.Gaussian.Linear.Translated
public import Purelib.Polynomial.Dense.Gaussian.Constants
import Purelib.Data.Gaussian.Field

/-! # Evaluation and displacement at an original exact linear root -/

public section

namespace Purelib.Polynomial.Dense.Gaussian.Roots.Linear.RootData

open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)

/-- The original polynomial evaluates as its retained leading coefficient times displacement from its exact root.

The normalized two-entry table and the original polynomial's normalization
readback identify the same affine expression at every displayed point.
-/
theorem eval_eq {polynomial : CoefficientPolynomial} (data : RootData polynomial) (point : Canonical) :
    polynomial.eval point = data.leading * (point - data.point) := by
  have original : polynomial.eval point = data.leading * point + data.trailing := by
    rewrite [← DensePolynomial.eval_normalize polynomial point]
    change DensePolynomial.evalCoeffs point polynomial.normalize.coeffs = _
    rewrite [data.normalizedCoeffs]
    simp only [DensePolynomial.evalCoeffs, List.foldl_cons, List.foldl_nil, zero_mul, zero_add,
      -eq_self, -iff_self]
    rfl
  have cancel : data.leading * (data.trailing * data.leading⁻¹) = data.trailing :=
    (Basic.mul_assoc _ _ _).symm.trans
      ((congrArg (fun value => value * data.leading⁻¹) (Basic.mul_comm _ _)).trans
        ((Basic.mul_assoc _ _ _).trans
          ((congrArg (fun value => data.trailing * value)
            (Canonical.mul_inv_cancel data.leading data.leadingNonzero)).trans (Basic.mul_one _))))
  rewrite [data.point_eq, Basic.sub_eq_add_neg, neg_neg, mul_add, cancel]
  exact original

/-- The original affine polynomial is its retained leading constant times displacement from its retained root.

The same original coefficient table and cached exact point certify the
ordered product identity, without selecting or isolating another root.
-/
theorem factorization {polynomial : CoefficientPolynomial} (data : RootData polynomial) :
    Factorization.Identity.ProductIdentity polynomial
      (Constants.gaussianConstant data.leading) (Linear.Translated.translatedCoordinate data.point) := by
  apply Factorization.Identity.factorizationOfCandidateEvals
  intro point _
  rewrite [Constants.gaussianConstant_eval, Linear.Translated.translatedCoordinate_eval]
  exact data.eval_eq point

/-- Multiplication by the retained inverse slope recovers the exact displacement from the original polynomial value. -/
theorem displacement_eq {polynomial : CoefficientPolynomial} (data : RootData polynomial) (point : Canonical) :
    point - data.point = data.leading⁻¹ * polynomial.eval point := by
  rewrite [data.eval_eq point, ← Basic.mul_assoc,
    Canonical.inv_mul_cancel data.leading data.leadingNonzero, Basic.one_mul]
  rfl

/-- Every exact zero of the original linear polynomial is its retained exact root.

The inverse-slope displacement identity converts the original zero value
to zero displacement, without changing the original polynomial owner.
-/
theorem point_eq_of_root {polynomial : CoefficientPolynomial} (data : RootData polynomial)
    (point : Canonical) (root : polynomial.eval point = 0) : point = data.point := by
  have displacement := data.displacement_eq point
  rewrite [root, Basic.mul_zero] at displacement
  have recovered : point = (point - data.point) + data.point := by
    rewrite [Basic.sub_eq_add_neg, Basic.add_assoc, Canonical.neg_add_cancel, Basic.add_zero]
    rfl
  exact recovered.trans ((congrArg (fun value : Canonical => value + data.point) displacement).trans
    (Canonical.zero_add data.point))

end Purelib.Polynomial.Dense.Gaussian.Roots.Linear.RootData

end
