module
public import Purelib.Curves.Hyperelliptic.Basic
public import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Power
import Purelib.Algebra.Semiring.Normalization
import Purelib.Data.Nat.Multiplication
import Purelib.Polynomial.Ascending.Gaussian.Basic
public import Purelib.Polynomial.Ascending.Gaussian.Evaluation
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Basic

public import Purelib.Riemann.Branches.SquareRootSheets
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega

open Purelib

open Purelib.Curves

open Purelib.Curves.Hyperelliptic

open Purelib.Data.Gaussian

open Purelib.Polynomial

open Purelib.Polynomial.Ascending.Gaussian

open Purelib.Polynomial.Dense.Basic
open _root_.Purelib.Polynomial.Dense.Basic renaming CoefficientPolynomial -> Dense

open Purelib.Riemann.Branches

@[expose] public section

/-!
# The finite odd-degree chart at infinity

For an odd-degree hyperelliptic equation `y^2 = f(x)`, put

`x = t⁻²` and `Y = t^degree * y`.

Then `Y^2` is the finite even polynomial

`F(t) = t^(2 * degree) * f(t⁻²)`.

This file constructs `F` directly from the normalized finite coefficient
list.  In particular, `F(0)` is the leading coefficient of `f`, so the
apparent endpoint at infinity becomes an ordinary nonzero square-root
problem.  The evaluation identity is proved by induction over that finite
list; no completed projective curve or limiting point is used.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Infinity

open Purelib.Riemann.Curves.AlgebraicDifferentials

/-- Exact Gaussian rational chart coordinates. -/
abbrev Gaussian := Data.Gaussian.Basic.Canonical
/-- The dense affine polynomial defining the hyperelliptic equation. -/
abbrev GaussianPolynomial :=
  Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial
/-- The ascending-coefficient Gaussian polynomial used for the finite infinity chart. -/
abbrev ChartPolynomial := Polynomial.Ascending.Gaussian.CoefficientPolynomial

/-- Insert one zero after every coefficient. Since the source list is high-to-low and the chart polynomial is
low-to-high, this sends `[a_d, ..., a_0]` to the coefficients of `a_d + a_(d-1)t^2 + ... + a_0 t^(2d)` (with one
harmless final zero). -/
def evenCoefficients : List Gaussian -> List
  Gaussian
  | [] => []
  | coefficient :: remaining =>
      coefficient :: 0 :: evenCoefficients remaining

/-- Direct finite Horner evaluation in the squared chart parameter. -/
def evenHorner (squareParameter : Gaussian) : List
  Gaussian -> Gaussian
  | [] => 0
  | coefficient :: remaining =>
      coefficient + squareParameter * evenHorner squareParameter remaining

/-- The even Horner evaluator sends an empty coefficient list to zero. -/
@[simp] theorem evenHorner_nil (squareParameter : Gaussian) :
    evenHorner squareParameter [] = 0 := rfl

/-- The even Horner evaluator adds the leading coefficient to the squared-parameter-scaled tail. -/
@[simp] theorem evenHorner_cons (squareParameter coefficient : Gaussian)
    (remaining : List Gaussian) :
    evenHorner squareParameter (coefficient :: remaining) =
      coefficient + squareParameter *
        evenHorner squareParameter remaining := rfl

/-- The low-to-high polynomial evaluator computes exactly the displayed finite even Horner recursion. -/
theorem evalCoeffs_evenCoefficients (parameter : Gaussian) :
    forall coefficients : List Gaussian,
      Evaluation.evalCoeffs
          (evenCoefficients coefficients) parameter =
        evenHorner (parameter ^ 2) coefficients
  | [] => rfl
  | coefficient :: remaining => by
      simp only [evenCoefficients, Evaluation.evalCoeffs,
        List.foldr_cons]
      change coefficient + parameter *
          (0 + parameter *
            Evaluation.evalCoeffs
              (evenCoefficients remaining) parameter) =
        coefficient + parameter ^ 2 *
          evenHorner (parameter ^ 2) remaining
      rw [evalCoeffs_evenCoefficients parameter remaining]
      ring1

/-- The executable chart radicand obtained from the normalized affine coefficient list. -/
def chartPolynomial (polynomial : GaussianPolynomial) : ChartPolynomial :=
  ⟨evenCoefficients polynomial.normalize.coeffs⟩

/-- The constructed chart polynomial evaluates by the finite even Horner recursion on normalized coefficients. -/
theorem chartPolynomial_eval (polynomial : GaussianPolynomial)
    (parameter : Gaussian) :
    Evaluation.eval (chartPolynomial polynomial) parameter =
      evenHorner (parameter ^ 2) polynomial.normalize.coeffs := by
  exact evalCoeffs_evenCoefficients parameter polynomial.normalize.coeffs

/-- At the chart origin the transformed radicand is the affine leading coefficient. -/
theorem evenHorner_zero : forall coefficients : List Gaussian,
    evenHorner 0 coefficients = coefficients.headD 0
  | [] => rfl
  | coefficient :: remaining => by
      simp only [evenHorner, List.headD_cons, zero_mul, add_zero,
        -eq_self, -iff_self]
      rfl

/-- The chart polynomial at zero equals the original polynomial leading coefficient. -/
theorem chartPolynomial_eval_zero (polynomial : GaussianPolynomial) :
    Evaluation.eval (chartPolynomial polynomial) 0 =
      polynomial.leadingCoeff := by
  rw [chartPolynomial_eval]
  change evenHorner 0 polynomial.normalize.coeffs = _
  rw [evenHorner_zero]
  rfl

/-- A nonzero affine polynomial gives a nonzero chart radicand at the origin. -/
theorem chartPolynomial_eval_zero_ne {polynomial : GaussianPolynomial}
    (nonzero : polynomial.isZero = false) :
    Evaluation.eval (chartPolynomial polynomial) 0 ≠ 0 := by
  rw [chartPolynomial_eval_zero]
  exact DensePolynomial.leadingCoeff_ne_zero nonzero

/-- The chart radicand attached to a hyperelliptic curve. -/
def curveRadicand {genus : Nat} (curve : Hyperelliptic.Basic.HyperellipticCurve genus) :
    ChartPolynomial :=
  chartPolynomial curve.polynomial

/-- The curve radicand at the chart origin is the defining polynomial leading coefficient. -/
theorem curveRadicand_origin {genus : Nat}
    (curve : Hyperelliptic.Basic.HyperellipticCurve genus) :
    Evaluation.eval (curveRadicand curve) 0 =
      curve.polynomial.leadingCoeff :=
  chartPolynomial_eval_zero curve.polynomial

/-- The retained nonzero defining polynomial makes the curve radicand nonzero at the chart origin. -/
theorem curveRadicand_origin_ne {genus : Nat}
    (curve : Hyperelliptic.Basic.HyperellipticCurve genus) :
    Evaluation.eval (curveRadicand curve) 0 ≠ 0 :=
  chartPolynomial_eval_zero_ne curve.nonzero

/-- Either square-root sheet of the transformed nonzero radicand at the chart origin is immediately available to the
finite root machinery. -/
def originSquareRoot {genus : Nat} (curve : Hyperelliptic.Basic.HyperellipticCurve genus)
    (sheet : Fin 2) : SquareRootSheets.Sheet
      (Evaluation.eval (curveRadicand curve) 0) :=
  SquareRootSheets.sheet
    (curveRadicand_origin_ne curve) sheet

/-- Homogenized finite-list identity. The hypothesis `affine * chart = 1` is the only reciprocal fact needed by the
induction. Keeping it explicit also makes the theorem useful independently of the particular substitution `affine =
(t^2)⁻¹`. -/
theorem homogenized_evalCoeffs (affine chart : Gaussian)
    (cancel : affine * chart = 1) :
    forall coefficients : List Gaussian,
      chart ^ coefficients.length *
          DensePolynomial.evalCoeffs
            affine coefficients =
        chart * evenHorner chart coefficients
  | [] => by
      simp only [List.length_nil, pow_zero,
        Purelib.Polynomial.Dense.Basic.DensePolynomial.evalCoeffs_nil,
        evenHorner_nil, mul_zero, -eq_self, -iff_self]
      rfl
  | coefficient :: remaining => by
      rw [DensePolynomial.evalCoeffs_cons_expansion]
      simp only [List.length_cons, pow_succ, evenHorner_cons]
      rw [mul_add]
      have poweredCancel :
          affine ^ remaining.length * chart ^ remaining.length = 1 := by
        rw [← Algebra.Semiring.Normalization.product_pow, cancel, one_pow]
      have leadingTerm :
          (chart ^ remaining.length * chart) *
              (coefficient * affine ^ remaining.length) =
            chart * coefficient := by
        calc
          (chart ^ remaining.length * chart) *
                (coefficient * affine ^ remaining.length) =
              chart * coefficient *
                (affine ^ remaining.length * chart ^ remaining.length) := by
                  ring1
          _ = chart * coefficient := by rw [poweredCancel, mul_one]
      rw [leadingTerm]
      have inductionIdentity :=
        homogenized_evalCoeffs affine chart cancel remaining
      calc
        chart * coefficient +
              chart ^ remaining.length * chart *
                DensePolynomial.evalCoeffs
                  affine remaining =
            chart * coefficient + chart *
              (chart ^ remaining.length *
                DensePolynomial.evalCoeffs
                  affine remaining) := by ring1
        _ = chart * coefficient + chart *
              (chart * evenHorner chart remaining) := by
                rw [inductionIdentity]
        _ = chart *
              (coefficient + chart * evenHorner chart remaining) := by
                ring1

/-- Exact affine-to-chart equation away from the chart origin. -/
theorem chartPolynomial_affine_identity {polynomial : GaussianPolynomial}
    (nonzero : polynomial.isZero = false)
    (parameter : Gaussian) (parameterNonzero : parameter ≠ 0) :
    Evaluation.eval (chartPolynomial polynomial) parameter =
      (parameter ^ 2) ^ polynomial.natDegree *
        polynomial.eval ((parameter ^ 2)⁻¹) := by
  let chart := parameter ^ 2
  have chartNonzero : chart ≠ 0 :=
    Power.pow_ne_zero_direct
      parameter parameterNonzero 2
  have cancel : chart⁻¹ * chart = 1 :=
    Data.Gaussian.Basic.Canonical.inv_mul_cancel chart chartNonzero
  have homogenized := homogenized_evalCoeffs chart⁻¹ chart cancel
    polynomial.normalize.coeffs
  have normalizedEval :
      DensePolynomial.evalCoeffs chart⁻¹
          polynomial.normalize.coeffs = polynomial.eval chart⁻¹ := by
    change polynomial.normalize.eval chart⁻¹ = polynomial.eval chart⁻¹
    exact DensePolynomial.eval_normalize
      polynomial chart⁻¹
  have chartValue :
      Evaluation.eval (chartPolynomial polynomial)
          parameter = evenHorner chart polynomial.normalize.coeffs := by
    change Evaluation.eval (chartPolynomial polynomial)
        parameter = evenHorner (parameter ^ 2) polynomial.normalize.coeffs
    exact chartPolynomial_eval polynomial parameter
  have coefficientCount :
      polynomial.normalize.coeffs.length = polynomial.natDegree + 1 := by
    exact
      (DensePolynomial.natDegree_add_one_eq_degreeCount
        nonzero).symm
  rw [chartValue, ← normalizedEval]
  apply Data.Gaussian.Field.mul_right_cancel_of_ne chartNonzero
  calc
    evenHorner chart polynomial.normalize.coeffs * chart =
        chart * evenHorner chart polynomial.normalize.coeffs := by ring1
    _ = chart ^ polynomial.normalize.coeffs.length *
          DensePolynomial.evalCoeffs
            chart⁻¹ polynomial.normalize.coeffs := homogenized.symm
    _ = (chart ^ polynomial.natDegree *
          DensePolynomial.evalCoeffs
            chart⁻¹ polynomial.normalize.coeffs) * chart := by
      rw [coefficientCount, pow_succ]
      ring1

/-- In the odd-degree case the exponent in the affine identity is exactly the displayed degree `2g+1`. -/
theorem curveRadicand_affine_identity {genus : Nat}
    (curve : Hyperelliptic.Basic.HyperellipticCurve genus)
    (oddDegree : curve.polynomial.natDegree = 2 * genus + 1)
    (parameter : Gaussian) (parameterNonzero : parameter ≠ 0) :
    Evaluation.eval (curveRadicand curve) parameter =
      (parameter ^ 2) ^ (2 * genus + 1) *
        curve.polynomial.eval ((parameter ^ 2)⁻¹) := by
  rw [curveRadicand,
    chartPolynomial_affine_identity curve.nonzero
    parameter parameterNonzero, oddDegree]

/-- Exact transformed curve equation. If `(x,y)` satisfies the affine equation at `x=t⁻²`, then `Y=t^(2g+1)y` satisfies
the finite chart equation. -/
theorem scaled_curve_equation {genus : Nat}
    (curve : Hyperelliptic.Basic.HyperellipticCurve genus)
    (oddDegree : curve.polynomial.natDegree = 2 * genus + 1)
    (parameter y : Gaussian) (parameterNonzero : parameter ≠ 0)
    (affineEquation : y ^ 2 =
      curve.polynomial.eval ((parameter ^ 2)⁻¹)) :
    (parameter ^ (2 * genus + 1) * y) ^ 2 =
      Evaluation.eval (curveRadicand curve) parameter := by
  rw [curveRadicand_affine_identity curve oddDegree parameter
    parameterNonzero, Algebra.Semiring.Normalization.product_pow, affineEquation]
  congr 1
  rw [← pow_mul, ← pow_mul]
  congr 1
  omega0

/-- The nonnegative exponent of the regularized odd-degree differential `-2 t^(2g-2k-2) dt/Y`, for the zero-based basis
index `k < g`. -/
def differentialExponent {genus : Nat}
    (differential : Differentials.Basic.Differential genus) : Nat :=
  2 * (genus - differential.index.val - 1)

/-- The regularized differential exponent equals twice the genus minus twice its index minus two. -/
theorem differentialExponent_eq {genus : Nat}
    (differential : Differentials.Basic.Differential genus) :
    differentialExponent differential =
      2 * genus - 2 * differential.index.val - 2 := by
  unfold Charts.Infinity.differentialExponent
  rewrite [Data.Nat.Multiplication.left_sub_distrib,
    Data.Nat.Multiplication.left_sub_distrib]
  rfl

end Purelib.Curves.Hyperelliptic.Charts.Infinity
