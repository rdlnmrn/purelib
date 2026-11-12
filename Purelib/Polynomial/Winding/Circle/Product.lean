module

public import Purelib.Polynomial.Clearance.Circle
public import Purelib.Polynomial.Winding.Circle
import Purelib.Polynomial.Dense.Rational.CauchyIndex.Comparison.Basic
import Purelib.Polynomial.Dense.Rational.CauchyIndex.Product.Assembly
import Purelib.Polynomial.Dense.Rational.Pair.Product
import Purelib.Polynomial.Clearance.Pair.Product
import Purelib.Data.Gaussian.Power
import Purelib.Tactic.Ring

/-!
# Multiplication of the original independent circle winding

The original coordinate-product formula is compared with the actual cleared
substitution of the polynomial product. Their positive real denominator
payments may differ. A positive conjugate dot product preserves the complete
index, including the exact corrections at both circle joins.
-/

namespace Purelib.Polynomial.Winding.Circle

open Purelib.Data
open Purelib.RationalFunctions.Curve
open Canonical.Circle
open Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Dense.Rational.CauchyIndex
open Rat.Fraction (Rational)
open Rat.Fraction.Order
open Gaussian.Basic (Canonical)
open Gaussian.Sign
open Dense.Rational.Pair
open Purelib.Polynomial.Clearance.Circle (Certificate)

/-- Two positive real payments on the same nonzero value have positive conjugate dot product. -/
private theorem scaled_dot_positive (value : Canonical) (left right : Rational)
    (leftPositive : 0 < left) (rightPositive : 0 < right) (nonzero : value ≠ 0) :
    0 < ((⟨left, 0⟩ : Canonical) * value).re * ((⟨right, 0⟩ : Canonical) * value).re +
      ((⟨left, 0⟩ : Canonical) * value).im * ((⟨right, 0⟩ : Canonical) * value).im := by
  have identity :
      ((⟨left, 0⟩ : Canonical) * value).re * ((⟨right, 0⟩ : Canonical) * value).re +
        ((⟨left, 0⟩ : Canonical) * value).im * ((⟨right, 0⟩ : Canonical) * value).im =
      (left * right) * Gaussian.Norm.Basic.normSq value := by
    change (left * value.re - 0 * value.im) * (right * value.re - 0 * value.im) +
      (left * value.im + 0 * value.re) * (right * value.im + 0 * value.re) =
        (left * right) * (value.re ^ 2 + value.im ^ 2)
    ring1
  rewrite [identity]
  exact Arithmetic.mul_pos_direct (Arithmetic.mul_pos_direct leftPositive rightPositive)
    (Gaussian.Norm.Basic.normSq_pos nonzero)

/-- The actual cleared product and the product of cleared inputs have positive conjugate dot product. -/
private theorem chart_product_positive {left right : CoefficientPolynomial} {curve : RationalCurve}
    (leftPath : Substitution.Retained left curve) (rightPath : Substitution.Retained right curve)
    (productPath : Substitution.Retained (left * right) curve)
    (parameter divisor : Rational) (divisorPositive : 0 < divisor)
    (denominator : curve.denominatorAt parameter = ⟨divisor, 0⟩)
    (chartNonzero : curve.denominatorAt parameter ≠ 0)
    (leftNonzero : left.eval (curve.point parameter) ≠ 0)
    (rightNonzero : right.eval (curve.point parameter) ≠ 0) :
    0 < (Product.productReal leftPath.real leftPath.imaginary rightPath.real rightPath.imaginary).eval parameter *
        productPath.real.eval parameter +
      (Product.productImag leftPath.real leftPath.imaginary rightPath.real rightPath.imaginary).eval parameter *
        productPath.imaginary.eval parameter := by
  let value := left.eval (curve.point parameter) * right.eval (curve.point parameter)
  have sourceValue :
      (⟨(Product.productReal leftPath.real leftPath.imaginary rightPath.real rightPath.imaginary).eval parameter,
        (Product.productImag leftPath.real leftPath.imaginary rightPath.real rightPath.imaginary).eval parameter⟩ :
          Canonical) =
      (⟨divisor ^ left.coeffs.length * divisor ^ right.coeffs.length, 0⟩ : Canonical) * value := by
    rw [Product.eval_productReal, Product.eval_productImag]
    change (⟨leftPath.real.eval parameter, leftPath.imaginary.eval parameter⟩ : Canonical) *
        ⟨rightPath.real.eval parameter, rightPath.imaginary.eval parameter⟩ = _
    rw [leftPath.coordinates, rightPath.coordinates, leftPath.state_value, rightPath.state_value,
      eval_clearedEval left curve parameter chartNonzero, eval_clearedEval right curve parameter chartNonzero,
      eval_denominatorPower, eval_denominatorPower, denominator,
      Gaussian.Power.realAxis_pow, Gaussian.Power.realAxis_pow]
    apply Gaussian.Basic.ext <;>
      dsimp only [value] <;> simp only [Gaussian.Basic.mul_re, Gaussian.Basic.mul_im] <;> ring1
  have targetValue : (⟨productPath.real.eval parameter, productPath.imaginary.eval parameter⟩ : Canonical) =
      (⟨divisor ^ (left * right).coeffs.length, 0⟩ : Canonical) * value := by
    rw [productPath.coordinates, productPath.state_value,
      eval_clearedEval (left * right) curve parameter chartNonzero,
      eval_denominatorPower, denominator, Gaussian.Power.realAxis_pow, Dense.Basic.DensePolynomial.eval_mul]
  have sourceReal := congrArg Canonical.re sourceValue
  have sourceImaginary := congrArg Canonical.im sourceValue
  have targetReal := congrArg Canonical.re targetValue
  have targetImaginary := congrArg Canonical.im targetValue
  change (Product.productReal leftPath.real leftPath.imaginary
    rightPath.real rightPath.imaginary).eval parameter = _ at sourceReal
  change (Product.productImag leftPath.real leftPath.imaginary
    rightPath.real rightPath.imaginary).eval parameter = _ at sourceImaginary
  change productPath.real.eval parameter = _ at targetReal
  change productPath.imaginary.eval parameter = _ at targetImaginary
  rw [sourceReal, sourceImaginary, targetReal, targetImaginary]
  exact scaled_dot_positive value _ _
    (Arithmetic.mul_pos_direct (Arithmetic.pow_pos_direct divisorPositive _)
      (Arithmetic.pow_pos_direct divisorPositive _))
    (Arithmetic.pow_pos_direct divisorPositive _)
    (Purelib.Algebra.Field.ExplicitField.mul_ne_zero leftNonzero rightNonzero)

/-- Independent whole-circle raw winding is additive for the actual dense polynomial product.

The two original whole-circle margins supply all finite coordinate clearances.
The actual product substitution remains an input, and every product and
comparison endpoint correction cancels at the same two exact joins.
-/
public theorem raw_mul {left right : CoefficientPolynomial}
    (leftMargin : Certificate left) (rightMargin : Certificate right)
    (leftPaths : Boundary.Substitutions left) (rightPaths : Boundary.Substitutions right)
    (productPaths : Boundary.Substitutions (left * right)) :
    raw productPaths = raw leftPaths + raw rightPaths := by
  let leftClearance := leftMargin.onBoundary leftPaths
  let rightClearance := rightMargin.onBoundary rightPaths
  let productClearance := (leftMargin.product rightMargin).onBoundary productPaths
  let E := Product.productReal leftPaths.primary.real leftPaths.primary.imaginary
    rightPaths.primary.real rightPaths.primary.imaginary
  let H := Product.productImag leftPaths.primary.real leftPaths.primary.imaginary
    rightPaths.primary.real rightPaths.primary.imaginary
  let F := Product.productReal leftPaths.reciprocal.real leftPaths.reciprocal.imaginary
    rightPaths.reciprocal.real rightPaths.reciprocal.imaginary
  let J := Product.productImag leftPaths.reciprocal.real leftPaths.reciprocal.imaginary
    rightPaths.reciprocal.real rightPaths.reciprocal.imaginary
  let primaryClearance := leftClearance.primary.complexProduct rightClearance.primary
    (Product.eval_productReal _ _ _ _) (Product.eval_productImag _ _ _ _)
  let reciprocalClearance := leftClearance.reciprocal.complexProduct rightClearance.reciprocal
    (Product.eval_productReal _ _ _ _) (Product.eval_productImag _ _ _ _)
  have primaryComparison := Comparison.Basic.LineData.of_positiveDot primaryClearance productClearance.primary
    (by decide) (fun parameter _ => chart_product_positive leftPaths.primary rightPaths.primary
      productPaths.primary parameter (parameter ^ 2 + 1)
      (Arithmetic.add_pos_of_nonneg_of_pos_direct (Arithmetic.sq_nonneg_direct _) (by decide))
      (circle_denominatorAt 1 parameter) (circle_denominator_ne 1 parameter)
      (leftMargin.eval_ne ((normSq_circle_point 1 parameter).trans Canonical.normSq_one))
      (rightMargin.eval_ne ((normSq_circle_point 1 parameter).trans Canonical.normSq_one)))
  have reciprocalComparison := Comparison.Basic.LineData.of_positiveDot reciprocalClearance productClearance.reciprocal
    (by decide) (fun parameter _ => chart_product_positive leftPaths.reciprocal rightPaths.reciprocal
      productPaths.reciprocal parameter (parameter ^ 2 + 1)
      (Arithmetic.add_pos_of_nonneg_of_pos_direct (Arithmetic.sq_nonneg_direct _) (by decide))
      (reciprocalCircle_denominatorAt 1 parameter) (reciprocalCircle_denominator_ne 1 parameter)
      (leftMargin.eval_ne ((normSq_reciprocalCircle_point 1 parameter).trans Canonical.normSq_one))
      (rightMargin.eval_ne ((normSq_reciprocalCircle_point 1 parameter).trans Canonical.normSq_one)))
  have primaryIndex := primaryComparison.index_eq
    (primaryClearance.eval_ne_zero (x := -1) (by decide))
    (primaryClearance.eval_ne_zero (x := 1) (by decide))
  have reciprocalIndex := reciprocalComparison.index_eq
    (reciprocalClearance.eval_ne_zero (x := -1) (by decide))
    (reciprocalClearance.eval_ne_zero (x := 1) (by decide))
  have primaryProduct := Product.Assembly.auxiliaryProductFormula_of_clearances (by decide)
    leftClearance.primary rightClearance.primary
    (Product.eval_productReal _ _ _ _) (Product.eval_productImag _ _ _ _)
  have reciprocalProduct := Product.Assembly.auxiliaryProductFormula_of_clearances (by decide)
    leftClearance.reciprocal rightClearance.reciprocal
    (Product.eval_productReal _ _ _ _) (Product.eval_productImag _ _ _ _)
  have realJoin (parameter : Rational) (endpoint : parameter = -1 ∨ parameter = 1) :
      E.eval parameter = F.eval parameter := by
    dsimp only [E, F]
    rw [Product.eval_productReal, Product.eval_productReal,
      leftPaths.endpoint_real_eq parameter endpoint, leftPaths.endpoint_imaginary_eq parameter endpoint,
      rightPaths.endpoint_real_eq parameter endpoint, rightPaths.endpoint_imaginary_eq parameter endpoint]
  have imagJoin (parameter : Rational) (endpoint : parameter = -1 ∨ parameter = 1) :
      H.eval parameter = J.eval parameter := by
    dsimp only [H, J]
    rw [Product.eval_productImag, Product.eval_productImag,
      leftPaths.endpoint_real_eq parameter endpoint, leftPaths.endpoint_imaginary_eq parameter endpoint,
      rightPaths.endpoint_real_eq parameter endpoint, rightPaths.endpoint_imaginary_eq parameter endpoint]
  have comparisonJoin (parameter : Rational) (endpoint : parameter = -1 ∨ parameter = 1) :
      CauchyComparison.vertexHomotopyCorrection2
        ⟨E.eval parameter, H.eval parameter⟩
        ⟨productPaths.primary.real.eval parameter, productPaths.primary.imaginary.eval parameter⟩ =
      CauchyComparison.vertexHomotopyCorrection2
        ⟨F.eval parameter, J.eval parameter⟩
        ⟨productPaths.reciprocal.real.eval parameter, productPaths.reciprocal.imaginary.eval parameter⟩ := by
    rw [realJoin parameter endpoint, imagJoin parameter endpoint,
      productPaths.endpoint_real_eq parameter endpoint, productPaths.endpoint_imaginary_eq parameter endpoint]
  have productJoin (parameter : Rational) (endpoint : parameter = -1 ∨ parameter = 1) :
      Product.Basic.auxiliaryEndpointCorrection2 leftPaths.primary.imaginary rightPaths.primary.imaginary H parameter =
      Product.Basic.auxiliaryEndpointCorrection2 leftPaths.reciprocal.imaginary
        rightPaths.reciprocal.imaginary J parameter := by
    unfold Product.Basic.auxiliaryEndpointCorrection2
    rw [imagJoin parameter endpoint, leftPaths.endpoint_imaginary_eq parameter endpoint,
      rightPaths.endpoint_imaginary_eq parameter endpoint]
  change Basic.Sturm.cauchyIndex2 productPaths.primary.real
    productPaths.primary.imaginary (-1) 1 = _ at primaryIndex
  change Basic.Sturm.cauchyIndex2 productPaths.reciprocal.real
    productPaths.reciprocal.imaginary (-1) 1 = _ at reciprocalIndex
  change Product.Basic.AuxiliaryProductFormula _ _ _ _ E H (-1) 1 at primaryProduct
  change Product.Basic.AuxiliaryProductFormula _ _ _ _ F J (-1) 1 at reciprocalProduct
  unfold Product.Basic.AuxiliaryProductFormula at primaryProduct reciprocalProduct
  dsimp only [Boundary.parameters] at primaryIndex reciprocalIndex
  change _ = Basic.Sturm.cauchyIndex2 E H (-1) 1 +
    CauchyComparison.vertexHomotopyCorrection2 ⟨E.eval (-1), H.eval (-1)⟩
      ⟨productPaths.primary.real.eval (-1), productPaths.primary.imaginary.eval (-1)⟩ -
    CauchyComparison.vertexHomotopyCorrection2 ⟨E.eval 1, H.eval 1⟩
      ⟨productPaths.primary.real.eval 1, productPaths.primary.imaginary.eval 1⟩ at primaryIndex
  change _ = Basic.Sturm.cauchyIndex2 F J (-1) 1 +
    CauchyComparison.vertexHomotopyCorrection2 ⟨F.eval (-1), J.eval (-1)⟩
      ⟨productPaths.reciprocal.real.eval (-1), productPaths.reciprocal.imaginary.eval (-1)⟩ -
    CauchyComparison.vertexHomotopyCorrection2 ⟨F.eval 1, J.eval 1⟩
      ⟨productPaths.reciprocal.real.eval 1, productPaths.reciprocal.imaginary.eval 1⟩ at reciprocalIndex
  unfold raw
  rw [primaryIndex, reciprocalIndex, primaryProduct, reciprocalProduct,
    comparisonJoin (-1) (Or.inl rfl), comparisonJoin 1 (Or.inr rfl),
    productJoin (-1) (Or.inl rfl), productJoin 1 (Or.inr rfl)]
  ring1

end Purelib.Polynomial.Winding.Circle
