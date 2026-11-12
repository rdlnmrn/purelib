module

public import Purelib.Polynomial.Winding.Circle
public import Purelib.Polynomial.Dense.Rational.Pair.Product
public import Purelib.Polynomial.Clearance.Pair.Operations
public import Purelib.Polynomial.Clearance.Pair.Product
import Purelib.Polynomial.Dense.Rational.CauchyIndex.Product.Assembly
import Purelib.Polynomial.Dense.Rational.CauchyIndex.Product.Basic
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Data.Gaussian.Power
import Purelib.Data.Int.Arithmetic
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Independent quotient winding on the whole rational unit circle

The actual coordinate pairs represent the retained numerator times the
conjugate denominator on both original circle charts. The original phase
procedure resolves these pairs independently; product endpoint corrections
cancel at the same two exact joins.
-/

namespace Purelib.RationalFunctions.Winding.Circle

open Purelib.Data
open Purelib.Polynomial
open Purelib.RationalFunctions.Curve.Canonical.Circle
open Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Dense.Rational.Basic (CoordinatePolynomial)
open Dense.Rational
open Dense.Rational.CauchyIndex
open Rat.Fraction (Rational)
open Dense.Basic (DensePolynomial)
open Purelib.Algebra.Field
open Purelib.RationalFunctions.Curve
open Rat.Fraction.Order

/-- Clearing two real-denominator values multiplies their quotient direction by its exact real norm payment. -/
private theorem scalar_product_direction (numerator denominator : Gaussian.Basic.Canonical)
    (left right : Rational) (denominatorNonzero : denominator ≠ 0) :
    ((⟨left, 0⟩ : Gaussian.Basic.Canonical) * numerator) *
        Gaussian.Basic.conj ((⟨right, 0⟩ : Gaussian.Basic.Canonical) * denominator) =
      (⟨left * right * denominator.normSq, 0⟩ : Gaussian.Basic.Canonical) * (numerator / denominator) := by
  have conjugateScalar : Gaussian.Basic.conj (⟨right, 0⟩ : Gaussian.Basic.Canonical) = ⟨right, 0⟩ := by
    apply Gaussian.Basic.ext
    · rfl
    · exact (by decide : -(0 : Rational) = 0)
  have quotient : (numerator / denominator) * (⟨denominator.normSq, 0⟩ : Gaussian.Basic.Canonical) =
      numerator * Gaussian.Basic.conj denominator := by
    rw [← Gaussian.Basic.Canonical.mul_conj denominator, ← Gaussian.Basic.mul_assoc,
      ExplicitField.div_mul_cancel numerator denominatorNonzero]
    rw [Gaussian.Basic.conj_eq_canonical]
  have scalars : ((⟨left, 0⟩ : Gaussian.Basic.Canonical) * ⟨right, 0⟩) * ⟨denominator.normSq, 0⟩ =
      ⟨left * right * denominator.normSq, 0⟩ := by
    apply Gaussian.Basic.ext
    · change (left * right - (0 : Rational) * 0) * denominator.normSq - (left * 0 + 0 * right) * 0 = _
      ring1
    · change (left * right - (0 : Rational) * 0) * 0 + (left * 0 + 0 * right) * denominator.normSq = 0
      ring1
  rw [Gaussian.Basic.conj_mul, conjugateScalar]
  calc
    _ = ((⟨left, 0⟩ : Gaussian.Basic.Canonical) * ⟨right, 0⟩) *
        (numerator * Gaussian.Basic.conj denominator) := by ring1
    _ = ((⟨left, 0⟩ : Gaussian.Basic.Canonical) * ⟨right, 0⟩) *
        ((numerator / denominator) * ⟨denominator.normSq, 0⟩) := congrArg _ quotient.symm
    _ = (((⟨left, 0⟩ : Gaussian.Basic.Canonical) * ⟨right, 0⟩) * ⟨denominator.normSq, 0⟩) *
        (numerator / denominator) := by ring1
    _ = _ := congrArg (fun scalar : Gaussian.Basic.Canonical => scalar * (numerator / denominator)) scalars

/-- Original cleared substitution values retain the exact original quotient direction on a real-denominator chart. -/
private theorem cleared_direction (numerator denominator : CoefficientPolynomial) (curve : RationalCurve)
    (parameter divisor : Rational) (denominator_eq : curve.denominatorAt parameter = ⟨divisor, 0⟩)
    (chartNonzero : curve.denominatorAt parameter ≠ 0)
    (denominatorNonzero : denominator.eval (curve.point parameter) ≠ 0) :
    (clearedEval numerator curve).eval (Gaussian.Cast.Path.ofCoordinate parameter) *
        Gaussian.Basic.conj ((clearedEval denominator curve).eval (Gaussian.Cast.Path.ofCoordinate parameter)) =
      (⟨divisor ^ numerator.coeffs.length * divisor ^ denominator.coeffs.length *
          (denominator.eval (curve.point parameter)).normSq, 0⟩ : Gaussian.Basic.Canonical) *
        (numerator.eval (curve.point parameter) / denominator.eval (curve.point parameter)) := by
  rw [eval_clearedEval numerator curve parameter chartNonzero,
    eval_clearedEval denominator curve parameter chartNonzero, eval_denominatorPower, eval_denominatorPower,
    denominator_eq, Gaussian.Power.realAxis_pow, Gaussian.Power.realAxis_pow]
  exact scalar_product_direction _ _ _ _ denominatorNonzero

set_option genInjectivity false in
/-- Cached quotient-direction coordinate tables from both same original polynomial chart substitutions.

Both parents remain indices. Conjugating only the denominator's coordinate
table preserves the actual parameterized operation, rather than introducing
a polynomial conjugation in the Gaussian variable.
-/
public structure Paths {numerator denominator : CoefficientPolynomial}
    (numeratorPaths : Boundary.Substitutions numerator) (denominatorPaths : Boundary.Substitutions denominator) where
  /-- The once-negated primary denominator imaginary table. -/
  primaryConjugate : CoordinatePolynomial
  /-- The conjugate consumes the same original denominator table. -/
  primaryConjugate_eq : primaryConjugate = -denominatorPaths.primary.imaginary
  /-- The once-negated reciprocal denominator imaginary table. -/
  reciprocalConjugate : CoordinatePolynomial
  /-- The conjugate consumes the same original reciprocal denominator table. -/
  reciprocalConjugate_eq : reciprocalConjugate = -denominatorPaths.reciprocal.imaginary
  /-- The retained primary real product table. -/
  primaryReal : CoordinatePolynomial
  /-- The table is the original dense coordinate product. -/
  primaryReal_eq : primaryReal = Pair.Product.productReal numeratorPaths.primary.real numeratorPaths.primary.imaginary
    denominatorPaths.primary.real primaryConjugate
  /-- The retained primary imaginary product table. -/
  primaryImaginary : CoordinatePolynomial
  /-- The table uses the same stored primary conjugate. -/
  primaryImaginary_eq : primaryImaginary =
    Pair.Product.productImag numeratorPaths.primary.real numeratorPaths.primary.imaginary
      denominatorPaths.primary.real primaryConjugate
  /-- The retained reciprocal real product table. -/
  reciprocalReal : CoordinatePolynomial
  /-- The table is the original dense reciprocal product. -/
  reciprocalReal_eq : reciprocalReal =
    Pair.Product.productReal numeratorPaths.reciprocal.real numeratorPaths.reciprocal.imaginary
      denominatorPaths.reciprocal.real reciprocalConjugate
  /-- The retained reciprocal imaginary product table. -/
  reciprocalImaginary : CoordinatePolynomial
  /-- The table uses the same stored reciprocal conjugate. -/
  reciprocalImaginary_eq : reciprocalImaginary =
    Pair.Product.productImag numeratorPaths.reciprocal.real numeratorPaths.reciprocal.imaginary
      denominatorPaths.reciprocal.real reciprocalConjugate

constructive_injectivity Paths

namespace Paths

/-- Form the quotient-direction tables once from the same retained numerator and denominator charts. -/
@[expose] public def prepare {numerator denominator : CoefficientPolynomial}
    (numeratorPaths : Boundary.Substitutions numerator) (denominatorPaths : Boundary.Substitutions denominator) :
    Paths numeratorPaths denominatorPaths :=
  let primaryConjugate := -denominatorPaths.primary.imaginary
  let reciprocalConjugate := -denominatorPaths.reciprocal.imaginary
  { primaryConjugate, primaryConjugate_eq := rfl, reciprocalConjugate, reciprocalConjugate_eq := rfl
    primaryReal := Pair.Product.productReal numeratorPaths.primary.real numeratorPaths.primary.imaginary
      denominatorPaths.primary.real primaryConjugate, primaryReal_eq := rfl
    primaryImaginary := Pair.Product.productImag numeratorPaths.primary.real numeratorPaths.primary.imaginary
      denominatorPaths.primary.real primaryConjugate, primaryImaginary_eq := rfl
    reciprocalReal := Pair.Product.productReal numeratorPaths.reciprocal.real numeratorPaths.reciprocal.imaginary
      denominatorPaths.reciprocal.real reciprocalConjugate, reciprocalReal_eq := rfl
    reciprocalImaginary := Pair.Product.productImag numeratorPaths.reciprocal.real numeratorPaths.reciprocal.imaginary
      denominatorPaths.reciprocal.real reciprocalConjugate, reciprocalImaginary_eq := rfl }

/-- Read the original primary real product coordinate at the displayed parameter. -/
public theorem primary_real {numerator denominator : CoefficientPolynomial}
    {numeratorPaths : Boundary.Substitutions numerator} {denominatorPaths : Boundary.Substitutions denominator}
    (paths : Paths numeratorPaths denominatorPaths) (parameter : Rational) :
    paths.primaryReal.eval parameter = numeratorPaths.primary.real.eval parameter *
      denominatorPaths.primary.real.eval parameter + numeratorPaths.primary.imaginary.eval parameter *
        denominatorPaths.primary.imaginary.eval parameter := by
  rw [paths.primaryReal_eq, Pair.Product.eval_productReal, paths.primaryConjugate_eq, DensePolynomial.eval_neg]
  ring1

/-- Read the original primary imaginary product coordinate at the displayed parameter. -/
public theorem primary_imaginary {numerator denominator : CoefficientPolynomial}
    {numeratorPaths : Boundary.Substitutions numerator} {denominatorPaths : Boundary.Substitutions denominator}
    (paths : Paths numeratorPaths denominatorPaths) (parameter : Rational) :
    paths.primaryImaginary.eval parameter = numeratorPaths.primary.imaginary.eval parameter *
      denominatorPaths.primary.real.eval parameter - numeratorPaths.primary.real.eval parameter *
        denominatorPaths.primary.imaginary.eval parameter := by
  rw [paths.primaryImaginary_eq, Pair.Product.eval_productImag, paths.primaryConjugate_eq, DensePolynomial.eval_neg]
  ring1

/-- Read the original reciprocal real product coordinate at the displayed parameter. -/
public theorem reciprocal_real {numerator denominator : CoefficientPolynomial}
    {numeratorPaths : Boundary.Substitutions numerator} {denominatorPaths : Boundary.Substitutions denominator}
    (paths : Paths numeratorPaths denominatorPaths) (parameter : Rational) :
    paths.reciprocalReal.eval parameter = numeratorPaths.reciprocal.real.eval parameter *
      denominatorPaths.reciprocal.real.eval parameter + numeratorPaths.reciprocal.imaginary.eval parameter *
        denominatorPaths.reciprocal.imaginary.eval parameter := by
  rw [paths.reciprocalReal_eq, Pair.Product.eval_productReal, paths.reciprocalConjugate_eq, DensePolynomial.eval_neg]
  ring1

/-- Read the original reciprocal imaginary product coordinate at the displayed parameter. -/
public theorem reciprocal_imaginary {numerator denominator : CoefficientPolynomial}
    {numeratorPaths : Boundary.Substitutions numerator} {denominatorPaths : Boundary.Substitutions denominator}
    (paths : Paths numeratorPaths denominatorPaths) (parameter : Rational) :
    paths.reciprocalImaginary.eval parameter = numeratorPaths.reciprocal.imaginary.eval parameter *
      denominatorPaths.reciprocal.real.eval parameter - numeratorPaths.reciprocal.real.eval parameter *
        denominatorPaths.reciprocal.imaginary.eval parameter := by
  rw [paths.reciprocalImaginary_eq, Pair.Product.eval_productImag,
    paths.reciprocalConjugate_eq, DensePolynomial.eval_neg]
  ring1

/-- The quotient-direction real tables agree at both exact original chart joins. -/
public theorem endpoint_real_eq {numerator denominator : CoefficientPolynomial}
    {numeratorPaths : Boundary.Substitutions numerator} {denominatorPaths : Boundary.Substitutions denominator}
    (paths : Paths numeratorPaths denominatorPaths) (parameter : Rational)
    (endpoint : parameter = -1 ∨ parameter = 1) :
    paths.primaryReal.eval parameter = paths.reciprocalReal.eval parameter := by
  rw [paths.primary_real, paths.reciprocal_real, numeratorPaths.endpoint_real_eq parameter endpoint,
    numeratorPaths.endpoint_imaginary_eq parameter endpoint, denominatorPaths.endpoint_real_eq parameter endpoint,
    denominatorPaths.endpoint_imaginary_eq parameter endpoint]

/-- The quotient-direction imaginary tables agree at both exact original chart joins. -/
public theorem endpoint_imaginary_eq {numerator denominator : CoefficientPolynomial}
    {numeratorPaths : Boundary.Substitutions numerator} {denominatorPaths : Boundary.Substitutions denominator}
    (paths : Paths numeratorPaths denominatorPaths) (parameter : Rational)
    (endpoint : parameter = -1 ∨ parameter = 1) :
    paths.primaryImaginary.eval parameter = paths.reciprocalImaginary.eval parameter := by
  rw [paths.primary_imaginary, paths.reciprocal_imaginary, numeratorPaths.endpoint_real_eq parameter endpoint,
    numeratorPaths.endpoint_imaginary_eq parameter endpoint, denominatorPaths.endpoint_real_eq parameter endpoint,
    denominatorPaths.endpoint_imaginary_eq parameter endpoint]

/-- The exact primary product clearance reuses the same original input margins and cached tables. -/
@[expose] public def primaryClearance {numerator denominator : CoefficientPolynomial}
    {numeratorPaths : Boundary.Substitutions numerator} {denominatorPaths : Boundary.Substitutions denominator}
    (paths : Paths numeratorPaths denominatorPaths) (numeratorClearance : Boundary.Clearance numeratorPaths)
    (denominatorClearance : Boundary.Clearance denominatorPaths) :
    Clearance.Pair.Basic.Certificate paths.primaryReal paths.primaryImaginary Boundary.parameters := by
  refine numeratorClearance.primary.complexProduct denominatorClearance.primary.negSecond ?_ ?_
  · intro parameter
    rw [paths.primaryReal_eq, Pair.Product.eval_productReal, paths.primaryConjugate_eq]
  · intro parameter
    rw [paths.primaryImaginary_eq, Pair.Product.eval_productImag, paths.primaryConjugate_eq]

/-- The reciprocal product clearance reuses the same original input margins and cached tables. -/
@[expose] public def reciprocalClearance {numerator denominator : CoefficientPolynomial}
    {numeratorPaths : Boundary.Substitutions numerator} {denominatorPaths : Boundary.Substitutions denominator}
    (paths : Paths numeratorPaths denominatorPaths) (numeratorClearance : Boundary.Clearance numeratorPaths)
    (denominatorClearance : Boundary.Clearance denominatorPaths) :
    Clearance.Pair.Basic.Certificate paths.reciprocalReal paths.reciprocalImaginary Boundary.parameters := by
  refine numeratorClearance.reciprocal.complexProduct denominatorClearance.reciprocal.negSecond ?_ ?_
  · intro parameter
    rw [paths.reciprocalReal_eq, Pair.Product.eval_productReal, paths.reciprocalConjugate_eq]
  · intro parameter
    rw [paths.reciprocalImaginary_eq, Pair.Product.eval_productImag, paths.reciprocalConjugate_eq]

/-- The actual primary coordinate value is the corresponding product of the same retained cleared values. -/
public theorem primary_value {numerator denominator : CoefficientPolynomial}
    {numeratorPaths : Boundary.Substitutions numerator} {denominatorPaths : Boundary.Substitutions denominator}
    (paths : Paths numeratorPaths denominatorPaths) (parameter : Rational) :
    (⟨paths.primaryReal.eval parameter, paths.primaryImaginary.eval parameter⟩ : Gaussian.Basic.Canonical) =
      numeratorPaths.primary.state.value.eval (Gaussian.Cast.Path.ofCoordinate parameter) *
        Gaussian.Basic.conj
          (denominatorPaths.primary.state.value.eval (Gaussian.Cast.Path.ofCoordinate parameter)) := by
  rw [← numeratorPaths.primary.coordinates parameter, ← denominatorPaths.primary.coordinates parameter]
  apply Gaussian.Basic.ext
  · change paths.primaryReal.eval parameter = numeratorPaths.primary.real.eval parameter *
        denominatorPaths.primary.real.eval parameter - numeratorPaths.primary.imaginary.eval parameter *
          (-denominatorPaths.primary.imaginary.eval parameter)
    rw [paths.primary_real]
    ring1
  · change paths.primaryImaginary.eval parameter = numeratorPaths.primary.real.eval parameter *
        (-denominatorPaths.primary.imaginary.eval parameter) + numeratorPaths.primary.imaginary.eval parameter *
          denominatorPaths.primary.real.eval parameter
    rw [paths.primary_imaginary]
    ring1

/-- The actual reciprocal coordinate value is the corresponding product of the same retained cleared values. -/
public theorem reciprocal_value {numerator denominator : CoefficientPolynomial}
    {numeratorPaths : Boundary.Substitutions numerator} {denominatorPaths : Boundary.Substitutions denominator}
    (paths : Paths numeratorPaths denominatorPaths) (parameter : Rational) :
    (⟨paths.reciprocalReal.eval parameter, paths.reciprocalImaginary.eval parameter⟩ : Gaussian.Basic.Canonical) =
      numeratorPaths.reciprocal.state.value.eval (Gaussian.Cast.Path.ofCoordinate parameter) *
        Gaussian.Basic.conj
          (denominatorPaths.reciprocal.state.value.eval (Gaussian.Cast.Path.ofCoordinate parameter)) := by
  rw [← numeratorPaths.reciprocal.coordinates parameter, ← denominatorPaths.reciprocal.coordinates parameter]
  apply Gaussian.Basic.ext
  · change paths.reciprocalReal.eval parameter = numeratorPaths.reciprocal.real.eval parameter *
        denominatorPaths.reciprocal.real.eval parameter - numeratorPaths.reciprocal.imaginary.eval parameter *
          (-denominatorPaths.reciprocal.imaginary.eval parameter)
    rw [paths.reciprocal_real]
    ring1
  · change paths.reciprocalImaginary.eval parameter = numeratorPaths.reciprocal.real.eval parameter *
        (-denominatorPaths.reciprocal.imaginary.eval parameter) + numeratorPaths.reciprocal.imaginary.eval parameter *
          denominatorPaths.reciprocal.real.eval parameter
    rw [paths.reciprocal_imaginary]
    ring1

/-- The primary cleared coordinates are an explicitly scaled value of the original quotient. -/
public theorem primary_direction {numerator denominator : CoefficientPolynomial}
    {numeratorPaths : Boundary.Substitutions numerator} {denominatorPaths : Boundary.Substitutions denominator}
    (paths : Paths numeratorPaths denominatorPaths) (denominatorClearance : Boundary.Clearance denominatorPaths)
    (parameter : Rational) :
    (⟨paths.primaryReal.eval parameter, paths.primaryImaginary.eval parameter⟩ : Gaussian.Basic.Canonical) =
      (⟨(parameter ^ 2 + 1) ^ numerator.coeffs.length * (parameter ^ 2 + 1) ^ denominator.coeffs.length *
          (denominator.eval ((circle 1).point parameter)).normSq, 0⟩ : Gaussian.Basic.Canonical) *
        (numerator.eval ((circle 1).point parameter) / denominator.eval ((circle 1).point parameter)) := by
  rw [paths.primary_value, numeratorPaths.primary.state_value, denominatorPaths.primary.state_value]
  apply cleared_direction _ _ _ _ _ (circle_denominatorAt 1 parameter) (circle_denominator_ne 1 parameter)
  apply denominatorClearance.nonzero
  exact (normSq_circle_point 1 parameter).trans Gaussian.Basic.Canonical.normSq_one

/-- The reciprocal cleared coordinates are an explicitly scaled value of the original quotient. -/
public theorem reciprocal_direction {numerator denominator : CoefficientPolynomial}
    {numeratorPaths : Boundary.Substitutions numerator} {denominatorPaths : Boundary.Substitutions denominator}
    (paths : Paths numeratorPaths denominatorPaths) (denominatorClearance : Boundary.Clearance denominatorPaths)
    (parameter : Rational) :
    (⟨paths.reciprocalReal.eval parameter, paths.reciprocalImaginary.eval parameter⟩ : Gaussian.Basic.Canonical) =
      (⟨(parameter ^ 2 + 1) ^ numerator.coeffs.length * (parameter ^ 2 + 1) ^ denominator.coeffs.length *
          (denominator.eval ((reciprocalCircle 1).point parameter)).normSq, 0⟩ : Gaussian.Basic.Canonical) *
        (numerator.eval ((reciprocalCircle 1).point parameter) /
          denominator.eval ((reciprocalCircle 1).point parameter)) := by
  rw [paths.reciprocal_value, numeratorPaths.reciprocal.state_value, denominatorPaths.reciprocal.state_value]
  apply cleared_direction _ _ _ _ _ (reciprocalCircle_denominatorAt 1 parameter)
    (reciprocalCircle_denominator_ne 1 parameter)
  apply denominatorClearance.nonzero
  exact (normSq_reciprocalCircle_point 1 parameter).trans Gaussian.Basic.Canonical.normSq_one

/-- The exact primary quotient-direction multiplier is strictly positive on the whole original chart. -/
public theorem primary_scale_positive {numerator denominator : CoefficientPolynomial}
    {numeratorPaths : Boundary.Substitutions numerator} {denominatorPaths : Boundary.Substitutions denominator}
    (_paths : Paths numeratorPaths denominatorPaths) (denominatorClearance : Boundary.Clearance denominatorPaths)
    (parameter : Rational) :
    0 < (parameter ^ 2 + 1) ^ numerator.coeffs.length * (parameter ^ 2 + 1) ^ denominator.coeffs.length *
      (denominator.eval ((circle 1).point parameter)).normSq := by
  have divisorPositive : 0 < parameter ^ 2 + 1 :=
    Arithmetic.add_pos_of_nonneg_of_pos_direct (Arithmetic.sq_nonneg_direct _) (by decide)
  have nonzero := denominatorClearance.nonzero ((circle 1).point parameter)
    ((normSq_circle_point 1 parameter).trans Gaussian.Basic.Canonical.normSq_one)
  have normPositive := Gaussian.Norm.Basic.normSq_pos nonzero
  rw [Gaussian.Norm.Basic.normSq_eq_canonical] at normPositive
  exact Arithmetic.mul_pos_direct
    (Arithmetic.mul_pos_direct (Arithmetic.pow_pos_direct divisorPositive _)
      (Arithmetic.pow_pos_direct divisorPositive _))
    normPositive

/-- The exact reciprocal quotient-direction multiplier is strictly positive on the whole original chart. -/
public theorem reciprocal_scale_positive {numerator denominator : CoefficientPolynomial}
    {numeratorPaths : Boundary.Substitutions numerator} {denominatorPaths : Boundary.Substitutions denominator}
    (_paths : Paths numeratorPaths denominatorPaths) (denominatorClearance : Boundary.Clearance denominatorPaths)
    (parameter : Rational) :
    0 < (parameter ^ 2 + 1) ^ numerator.coeffs.length * (parameter ^ 2 + 1) ^ denominator.coeffs.length *
      (denominator.eval ((reciprocalCircle 1).point parameter)).normSq := by
  have divisorPositive : 0 < parameter ^ 2 + 1 :=
    Arithmetic.add_pos_of_nonneg_of_pos_direct (Arithmetic.sq_nonneg_direct _) (by decide)
  have nonzero := denominatorClearance.nonzero ((reciprocalCircle 1).point parameter)
    ((normSq_reciprocalCircle_point 1 parameter).trans Gaussian.Basic.Canonical.normSq_one)
  have normPositive := Gaussian.Norm.Basic.normSq_pos nonzero
  rw [Gaussian.Norm.Basic.normSq_eq_canonical] at normPositive
  exact Arithmetic.mul_pos_direct
    (Arithmetic.mul_pos_direct (Arithmetic.pow_pos_direct divisorPositive _)
      (Arithmetic.pow_pos_direct divisorPositive _))
    normPositive

end Paths

/-- The independently executable oriented raw quotient-direction index on both complete charts. -/
@[expose] public def raw {numerator denominator : CoefficientPolynomial}
    {numeratorPaths : Boundary.Substitutions numerator} {denominatorPaths : Boundary.Substitutions denominator}
    (paths : Paths numeratorPaths denominatorPaths) : Int :=
  Basic.Sturm.cauchyIndex2 paths.primaryReal paths.primaryImaginary (-1) 1 -
    Basic.Sturm.cauchyIndex2 paths.reciprocalReal paths.reciprocalImaginary (-1) 1

/-- The independently computed quotient-direction raw index is the difference of the same original polynomial indices.

The original product theorem applies to the actual retained coordinate
products. Denominator conjugation reverses its two chart indices, and the
two exact joins cancel every product endpoint correction.
-/
public theorem raw_eq_sub {numerator denominator : CoefficientPolynomial}
    {numeratorPaths : Boundary.Substitutions numerator} {denominatorPaths : Boundary.Substitutions denominator}
    (paths : Paths numeratorPaths denominatorPaths) (numeratorClearance : Boundary.Clearance numeratorPaths)
    (denominatorClearance : Boundary.Clearance denominatorPaths) :
    raw paths = Polynomial.Winding.Circle.raw numeratorPaths - Polynomial.Winding.Circle.raw denominatorPaths := by
  have primary := Product.Assembly.auxiliaryProductFormula_of_clearances
    (E := paths.primaryReal) (H := paths.primaryImaginary) (by decide : Boundary.parameters.lower <
      Boundary.parameters.upper) numeratorClearance.primary denominatorClearance.primary.negSecond
    (by
      intro parameter
      rw [paths.primaryReal_eq, Pair.Product.eval_productReal, paths.primaryConjugate_eq])
    (by
      intro parameter
      rw [paths.primaryImaginary_eq, Pair.Product.eval_productImag, paths.primaryConjugate_eq])
  have reciprocal := Product.Assembly.auxiliaryProductFormula_of_clearances
    (E := paths.reciprocalReal) (H := paths.reciprocalImaginary) (by decide : Boundary.parameters.lower <
      Boundary.parameters.upper) numeratorClearance.reciprocal denominatorClearance.reciprocal.negSecond
    (by
      intro parameter
      rw [paths.reciprocalReal_eq, Pair.Product.eval_productReal, paths.reciprocalConjugate_eq])
    (by
      intro parameter
      rw [paths.reciprocalImaginary_eq, Pair.Product.eval_productImag, paths.reciprocalConjugate_eq])
  have primaryConjugate := Basic.cauchyIndex2_neg_denominator
    (denominatorClearance.primary.eval_ne_zero (x := -1) ⟨le_rfl, by decide⟩)
    (denominatorClearance.primary.eval_ne_zero (x := 1) ⟨by decide, le_rfl⟩)
  have reciprocalConjugate := Basic.cauchyIndex2_neg_denominator
    (denominatorClearance.reciprocal.eval_ne_zero (x := -1) ⟨le_rfl, by decide⟩)
    (denominatorClearance.reciprocal.eval_ne_zero (x := 1) ⟨by decide, le_rfl⟩)
  have correction (parameter : Rational) (endpoint : parameter = -1 ∨ parameter = 1) :
      Product.Basic.auxiliaryEndpointCorrection2 numeratorPaths.primary.imaginary
          (-denominatorPaths.primary.imaginary) paths.primaryImaginary parameter =
        Product.Basic.auxiliaryEndpointCorrection2 numeratorPaths.reciprocal.imaginary
          (-denominatorPaths.reciprocal.imaginary) paths.reciprocalImaginary parameter := by
    unfold Product.Basic.auxiliaryEndpointCorrection2
    rw [DensePolynomial.eval_neg, DensePolynomial.eval_neg, paths.endpoint_imaginary_eq parameter endpoint,
      numeratorPaths.endpoint_imaginary_eq parameter endpoint,
      denominatorPaths.endpoint_imaginary_eq parameter endpoint]
  unfold Product.Basic.AuxiliaryProductFormula at primary reciprocal
  dsimp only [Boundary.parameters] at primary reciprocal
  rw [primaryConjugate] at primary
  rw [reciprocalConjugate] at reciprocal
  unfold raw Polynomial.Winding.Circle.raw
  rw [primary, reciprocal, correction (-1) (Or.inl rfl), correction 1 (Or.inr rfl)]
  ring1

set_option genInjectivity false in
/-- An independent whole-circle quotient-direction phase computation retaining the same original inputs.

Both original phase calls consume the actual cached product coordinates and
their transferred clearances. Exact chart-join cancellation certifies the
ordinary signed integer without using any polynomial root count.
-/
public structure Reading {numerator denominator : CoefficientPolynomial}
    {numeratorPaths : Boundary.Substitutions numerator} {denominatorPaths : Boundary.Substitutions denominator}
    (paths : Paths numeratorPaths denominatorPaths) (numeratorClearance : Boundary.Clearance numeratorPaths)
    (denominatorClearance : Boundary.Clearance denominatorPaths) where
  /-- The same cached primary product clearance. -/
  primaryClearance : Clearance.Pair.Basic.Certificate paths.primaryReal paths.primaryImaginary Boundary.parameters
  /-- The primary clearance is transferred from the same retained original margins. -/
  primaryClearance_eq : primaryClearance = paths.primaryClearance numeratorClearance denominatorClearance
  /-- The same cached reciprocal product clearance. -/
  reciprocalClearance :
    Clearance.Pair.Basic.Certificate paths.reciprocalReal paths.reciprocalImaginary Boundary.parameters
  /-- The reciprocal clearance is transferred from the same retained original margins. -/
  reciprocalClearance_eq : reciprocalClearance = paths.reciprocalClearance numeratorClearance denominatorClearance
  /-- The actual original primary product phase result. -/
  primary : Phase.Basic.PhaseFormula paths.primaryReal paths.primaryImaginary (-1) 1
  /-- The primary formula is computed by the original sufficient finite phase procedure. -/
  primary_eq : primary = Phase.Resolution.phaseFormulaOfClearance primaryClearance (by decide)
  /-- The actual original reciprocal product phase result. -/
  reciprocal : Phase.Basic.PhaseFormula paths.reciprocalReal paths.reciprocalImaginary (-1) 1
  /-- The reciprocal formula uses its same retained clearance. -/
  reciprocal_eq : reciprocal = Phase.Resolution.phaseFormulaOfClearance reciprocalClearance (by decide)
  /-- The signed ordinary quotient-direction winding. -/
  winding : Int
  /-- The winding is the difference of these actual retained chart corrections. -/
  winding_eq : winding = primary.turns - reciprocal.turns
  /-- The actual oriented raw index is exactly four times the returned winding. -/
  raw_eq : raw paths = 4 * winding

constructive_injectivity Reading

namespace Reading

/-- Compute the original phase formulas on the cached quotient-direction tables and normalize their raw index. -/
@[expose] public def prepare {numerator denominator : CoefficientPolynomial}
    {numeratorPaths : Boundary.Substitutions numerator} {denominatorPaths : Boundary.Substitutions denominator}
    (paths : Paths numeratorPaths denominatorPaths) (numeratorClearance : Boundary.Clearance numeratorPaths)
    (denominatorClearance : Boundary.Clearance denominatorPaths) :
    Reading paths numeratorClearance denominatorClearance :=
  let primaryClearance := paths.primaryClearance numeratorClearance denominatorClearance
  let reciprocalClearance := paths.reciprocalClearance numeratorClearance denominatorClearance
  let primary := Phase.Resolution.phaseFormulaOfClearance primaryClearance (by decide)
  let reciprocal := Phase.Resolution.phaseFormulaOfClearance reciprocalClearance (by decide)
  { primaryClearance, primaryClearance_eq := rfl, reciprocalClearance, reciprocalClearance_eq := rfl
    primary, primary_eq := rfl, reciprocal, reciprocal_eq := rfl
    winding := primary.turns - reciprocal.turns, winding_eq := rfl
    raw_eq := by
      unfold raw
      apply primary.closedDifference reciprocal
      · change Phase.Basic.endpointQuarterPhase paths.primaryReal paths.primaryImaginary (-1) =
          Phase.Basic.endpointQuarterPhase paths.reciprocalReal paths.reciprocalImaginary (-1)
        unfold Phase.Basic.endpointQuarterPhase
        rw [paths.endpoint_real_eq (-1) (Or.inl rfl), paths.endpoint_imaginary_eq (-1) (Or.inl rfl)]
      · change Phase.Basic.endpointQuarterPhase paths.primaryReal paths.primaryImaginary 1 =
          Phase.Basic.endpointQuarterPhase paths.reciprocalReal paths.reciprocalImaginary 1
        unfold Phase.Basic.endpointQuarterPhase
        rw [paths.endpoint_real_eq 1 (Or.inr rfl), paths.endpoint_imaginary_eq 1 (Or.inr rfl)] }

/-- The independent quotient phase reading equals the difference of the same retained polynomial phase readings. -/
public theorem winding_eq_sub {numerator denominator : CoefficientPolynomial}
    {numeratorPaths : Boundary.Substitutions numerator} {denominatorPaths : Boundary.Substitutions denominator}
    {paths : Paths numeratorPaths denominatorPaths} {numeratorClearance : Boundary.Clearance numeratorPaths}
    {denominatorClearance : Boundary.Clearance denominatorPaths}
    (reading : Reading paths numeratorClearance denominatorClearance)
    (numeratorReading : Polynomial.Winding.Circle.Reading numeratorPaths numeratorClearance)
    (denominatorReading : Polynomial.Winding.Circle.Reading denominatorPaths denominatorClearance) :
    reading.winding = numeratorReading.winding - denominatorReading.winding := by
  have equal := (reading.raw_eq.symm.trans (raw_eq_sub paths numeratorClearance denominatorClearance)).trans
    (congrArg₂ (fun left right : Int => left - right) numeratorReading.raw_eq denominatorReading.raw_eq)
  have cancelled : 4 * reading.winding = 4 * (numeratorReading.winding - denominatorReading.winding) :=
    equal.trans (by ring1)
  exact Purelib.Data.Int.Arithmetic.eq_of_mul_eq_mul_left (by decide : (4 : Int) ≠ 0) cancelled

end Reading
end Purelib.RationalFunctions.Winding.Circle
