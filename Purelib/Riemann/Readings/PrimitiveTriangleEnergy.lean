module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.Algebra.Field.ExplicitField
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Integration.Energy.AffineTriangle
import Purelib.Integration.Energy.Polygon
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Geometry.EvaluationLower

public import Purelib.Riemann.Integration.PrimitiveBasis
public import Purelib.Riemann.Topology.PreparedSurfaceCoercivity
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Polynomial.Dense.Evaluation
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

@[expose] public section

/-!
# Homogeneous energy budgets for actual shared primitive triangles

The geometry and primitive basis determine the error budgets before a
coefficient vector is supplied.  Every final budget is multiplied by its
squared coefficient norm.  There is no positive error floor at the zero
vector and no division by the coefficient norm.
-/

namespace Purelib.Riemann.Readings.PrimitiveTriangleEnergy

open Purelib.Data.Rat in
/-- The rational coordinate carrier of the retained primitive-energy estimates. -/
private abbrev Coordinate := Fraction.Rational
open Purelib.Data.Gaussian in
/-- The canonical Gaussian rational carrier of the retained primitive values. -/
private abbrev Gaussian := Basic.Canonical
open Purelib.Polynomial.Dense.Gaussian in
/-- The dense Gaussian polynomial carrier of the original inverse-root model. -/
private abbrev Polynomial := Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial
/-- The rational rectangle carrier of the original primitive neighborhood. -/
private abbrev Box := Purelib.Geometry.Rational.Box
open Purelib.Riemann.Readings.PreparedObservationCoercivity (coefficientNormSq)
open _root_.Purelib.Riemann.Integration (PrimitiveBasis)
open _root_.Purelib.Riemann.Integration.PrimitiveBasis (PrimitiveBasisPreflight Coefficients)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)

open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian Polynomial Box half correction
  residualStep correction_residual residualStep_contracts Model)

open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Riemann.Topology.PreparedSurfaceCoercivity

open Purelib.Data.Rat in
set_option genInjectivity false in
/-- Three nonnegative budgets for the two affine-error products and their mixed product.

Each squared budget bounds one quarter of its exact product of original affine or increment-error allowances, retaining
the two edge directions separately. -/
structure TriangleProductBudget (firstAffine secondAffine firstError secondError : Fraction.Rational) where
  /-- The retained budget for first-edge error times second-edge affine magnitude. -/ first : Fraction.Rational
  /-- The retained budget for first-edge affine magnitude times second-edge error. -/ second : Fraction.Rational
  /-- The retained budget for the product of the two original edge errors. -/ mixed : Fraction.Rational
  /-- The first retained product budget is nonnegative. -/ first_nonnegative : 0 ≤ first
  /-- The second retained product budget is nonnegative. -/ second_nonnegative : 0 ≤ second
  /-- The retained mixed-product budget is nonnegative. -/ mixed_nonnegative : 0 ≤ mixed
  /-- The first quarter-product is bounded by the exact first budget squared. -/ first_bound : firstError * secondAffine
    / 4 ≤ first ^ 2
  /-- The second quarter-product is bounded by the exact second budget squared. -/ second_bound : firstAffine *
    secondError / 4 ≤ second ^ 2
  /-- The mixed quarter-product is bounded by the exact mixed budget squared. -/ mixed_bound : firstError * secondError
    / 4 ≤ mixed ^ 2

constructive_injectivity TriangleProductBudget

namespace TriangleProductBudget

section
open Purelib.Data.Rat
/-- The uniform affine-error quarter-product is bounded by its squared cross budget.

A nonnegative coefficient bounds the product of the uniform increment-error
and affine allowances by `(epsilon * distance * (coefficient + 1))²`.
No sign condition is required on epsilon or distance. -/
theorem uniform_cross {coefficient epsilon distance : Fraction.Rational} (coefficientNonnegative : 0 ≤ coefficient) :
    (2 * epsilon ^ 2 * distance) * (coefficient * distance) / 4 ≤ (epsilon * distance * (coefficient + 1)) ^ 2 := by
  apply (Fraction.Order.Field.div_le_iff_pos (by decide)).mpr
  apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
  have identity : (epsilon * distance * (coefficient + 1)) ^ 2 * 4 -
      (2 * epsilon ^ 2 * distance) * (coefficient * distance) =
        (epsilon ^ 2 * distance ^ 2) * (4 * coefficient ^ 2 + 6 * coefficient + 4) := by ring1
  rw [identity]
  exact Fraction.Order.Arithmetic.mul_nonneg_direct
    (Fraction.Order.Arithmetic.mul_nonneg_direct
      (Fraction.Order.Arithmetic.sq_nonneg_direct _) (Fraction.Order.Arithmetic.sq_nonneg_direct _))
    (add_nonneg (add_nonneg
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) (Fraction.Order.Arithmetic.sq_nonneg_direct _))
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) coefficientNonnegative)) (by decide))

/-- Construct the three original product budgets with an explicit positive rational radius.

Nonnegative affine and increment-error allowances feed the exact square-error budget operation; the returned record
retains its three nonnegativity and squared-product certificates. -/
def build {firstAffine secondAffine firstError secondError : Fraction.Rational}
    (firstAffineNonnegative : 0 ≤ firstAffine) (secondAffineNonnegative : 0 ≤ secondAffine)
    (firstErrorNonnegative : 0 ≤ firstError) (secondErrorNonnegative : 0 ≤ secondError)
    (radius : Fraction.Rational) (positive : 0 < radius) :
    TriangleProductBudget firstAffine secondAffine firstError secondError := by
  have firstNonnegative := Fraction.Order.Field.div_nonneg_direct
    (Fraction.Order.Arithmetic.mul_nonneg_direct firstErrorNonnegative secondAffineNonnegative) (by
        decide : (0 : Fraction.Rational) ≤ 4)
  have secondNonnegative := Fraction.Order.Field.div_nonneg_direct
    (Fraction.Order.Arithmetic.mul_nonneg_direct firstAffineNonnegative secondErrorNonnegative) (by
        decide : (0 : Fraction.Rational) ≤ 4)
  have mixedNonnegative := Fraction.Order.Field.div_nonneg_direct
    (Fraction.Order.Arithmetic.mul_nonneg_direct firstErrorNonnegative secondErrorNonnegative) (by
        decide : (0 : Fraction.Rational) ≤ 4)
  exact
    { first := squareErrorBudget (firstError * secondAffine / 4) radius
      second := squareErrorBudget (firstAffine * secondError / 4) radius
      mixed := squareErrorBudget (firstError * secondError / 4) radius
      first_nonnegative := squareErrorBudget_nonnegative firstNonnegative positive
      second_nonnegative := squareErrorBudget_nonnegative secondNonnegative positive
      mixed_nonnegative := squareErrorBudget_nonnegative mixedNonnegative positive
      first_bound := squared_le_squareErrorBudget_sq firstNonnegative positive
      second_bound := squared_le_squareErrorBudget_sq secondNonnegative positive
      mixed_bound := squared_le_squareErrorBudget_sq mixedNonnegative positive }

end

open Purelib.Algebra in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- Scale an original quarter-product bound by a common squared coefficient factor. -/
public theorem scaled_product {first second : Basic.Canonical} {scale firstBound secondBound budget :
  Fraction.Rational}
    (firstLe : normSq first ≤ scale * firstBound) (secondLe : normSq second ≤ scale * secondBound)
    (paid : firstBound * secondBound / 4 ≤ budget ^ 2) :
    normSq first * normSq second / 4 ≤ (scale * budget) ^ 2 := by
  have product := (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct firstLe (Basic.Canonical.normSq_nonneg
    second)).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct secondLe ((Basic.Canonical.normSq_nonneg first).trans
      firstLe))
  have divided := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct product
    (by decide : (0 : Fraction.Rational) ≤ (4 : Fraction.Rational)⁻¹)
  calc
    _ ≤ (scale * firstBound) * (scale * secondBound) / 4 := by
      simpa only [Field.ExplicitField.div_eq_mul_inv] using divided
    _ = scale ^ 2 * (firstBound * secondBound / 4) := by
      simp only [Field.ExplicitField.div_eq_mul_inv]; ring1
    _ ≤ scale ^ 2 * budget ^ 2 := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct paid
      (Fraction.Order.Arithmetic.sq_nonneg_direct scale)
    _ = _ := by ring1

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Integration.Energy in
/-- Scale the retained product budgets into an exact affine triangle error certificate.

The supplied affine and increment-error bounds refer to the same coefficient, three points and three primitive values;
each original budget is multiplied by the nonnegative common scale. -/
def certificate {firstAffine secondAffine firstError secondError : Fraction.Rational}
    (budget : TriangleProductBudget firstAffine secondAffine firstError secondError)
    (scale : Fraction.Rational) (nonnegative : 0 ≤ scale)
    (coefficient firstPoint secondPoint thirdPoint firstValue secondValue thirdValue : Basic.Canonical)
    (firstAffineLe : normSq (AffineTriangle.affinePrimitiveIncrement coefficient firstPoint secondPoint) ≤ scale *
      firstAffine)
    (secondAffineLe : normSq (AffineTriangle.affinePrimitiveIncrement coefficient firstPoint thirdPoint) ≤ scale *
      secondAffine)
    (firstErrorLe : normSq (AffineTriangle.affinePrimitiveIncrementError coefficient firstPoint secondPoint firstValue
      secondValue) ≤ scale * firstError)
    (secondErrorLe : normSq (AffineTriangle.affinePrimitiveIncrementError coefficient firstPoint thirdPoint firstValue
      thirdValue) ≤ scale * secondError) :
    AffineTriangle.AffineTriangleErrorCertificate coefficient firstPoint secondPoint thirdPoint firstValue secondValue
      thirdValue where
  firstBudget := scale * budget.first
  secondBudget := scale * budget.second
  mixedBudget := scale * budget.mixed
  firstBudget_nonnegative := Fraction.Order.Arithmetic.mul_nonneg_direct nonnegative budget.first_nonnegative
  secondBudget_nonnegative := Fraction.Order.Arithmetic.mul_nonneg_direct nonnegative budget.second_nonnegative
  mixedBudget_nonnegative := Fraction.Order.Arithmetic.mul_nonneg_direct nonnegative budget.mixed_nonnegative
  firstProductBound := by
    simpa only [Norm.Basic.normSq_eq_canonical] using scaled_product firstErrorLe secondAffineLe
      budget.first_bound
  secondProductBound := by
    simpa only [Norm.Basic.normSq_eq_canonical] using scaled_product firstAffineLe secondErrorLe
      budget.second_bound
  mixedProductBound := by
    simpa only [Norm.Basic.normSq_eq_canonical] using scaled_product firstErrorLe secondErrorLe
      budget.mixed_bound

end TriangleProductBudget

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Polynomial.Dense.Gaussian in
set_option genInjectivity false in
/-- Cached affine and increment-error budgets for one original primitive-basis triangle.

The record keeps exact equations to both original edge increments, their separate product allowances and the sum of the
three retained product budgets. -/
structure PrimitiveTriangleBudget {polynomial :
  Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {siteCount index count : Nat}
    {patch : ContinuedNeighborhood polynomial siteCount} (basis : PrimitiveBasis patch index count)
    (first second third : Basic.Canonical) where
  /-- The cached affine magnitude scale along the original first-to-second edge. -/ firstAffine : Fraction.Rational
  /-- The first affine scale equals the original coefficient scale times its exact edge norm squared. -/ firstAffine_eq
    : firstAffine = basis.coefficientScale * normSq (second - first)
  /-- The cached affine magnitude scale along the original first-to-third edge. -/ secondAffine : Fraction.Rational
  /-- The second affine scale equals the original coefficient scale times its exact edge norm squared. -/
    secondAffine_eq : secondAffine = basis.coefficientScale * normSq (third - first)
  /-- The cached original first-to-second increment-error scale. -/ firstError : Fraction.Rational
  /-- The first error scale equals the exact original basis increment bound. -/ firstError_eq : firstError =
    basis.incrementScale first second
  /-- The cached original first-to-third increment-error scale. -/ secondError : Fraction.Rational
  /-- The second error scale equals the exact original basis increment bound. -/ secondError_eq : secondError =
    basis.incrementScale first third
  /-- The three certified product budgets indexed by these exact retained edge scales. -/ products :
    TriangleProductBudget firstAffine secondAffine firstError secondError
  /-- The cached sum of the retained three product budgets. -/ total : Fraction.Rational
  /-- The total is exactly the first, second and mixed budget sum. -/ total_eq : total = products.first +
    products.second + products.mixed

constructive_injectivity PrimitiveTriangleBudget

namespace PrimitiveTriangleBudget

variable {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {siteCount index
  count : Nat}
  {patch : ContinuedNeighborhood polynomial siteCount} {basis : PrimitiveBasis patch index count}
  {first second third : Purelib.Data.Gaussian.Basic.Canonical}

open Purelib.Data.Gaussian in
open Purelib.Integration.Energy in
/-- The affine primitive increment error is the value difference minus the coefficient times the point difference. -/
public theorem affine_error_eq (coefficient start finish startValue finishValue : Basic.Canonical) :
    AffineTriangle.affinePrimitiveIncrementError coefficient start finish startValue finishValue =
      finishValue - startValue - coefficient * (finish - start) := by
  unfold AffineTriangle.affinePrimitiveIncrementError AffineTriangle.affinePrimitiveIncrement
  ring1

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- Cache the original primitive basis's two edge bounds and their three product budgets.

The exact first-to-second and first-to-third increments determine separate affine and error scales. The positive
supplied radius is retained through their explicit budget construction. -/
def build (basis : PrimitiveBasis patch index count) (first second third : Basic.Canonical)
    (radius : Fraction.Rational) (positive : 0 < radius) : PrimitiveTriangleBudget basis first second third :=
  let firstAffine := basis.coefficientScale * normSq (second - first)
  let secondAffine := basis.coefficientScale * normSq (third - first)
  let firstError := basis.incrementScale first second
  let secondError := basis.incrementScale first third
  let products := TriangleProductBudget.build
    (Fraction.Order.Arithmetic.mul_nonneg_direct basis.coefficientScale_nonnegative (Basic.Canonical.normSq_nonneg _))
    (Fraction.Order.Arithmetic.mul_nonneg_direct basis.coefficientScale_nonnegative (Basic.Canonical.normSq_nonneg _))
    (basis.incrementScale_nonnegative first second) (basis.incrementScale_nonnegative first third) radius positive
  { firstAffine := firstAffine
    firstAffine_eq := rfl
    secondAffine := secondAffine
    secondAffine_eq := rfl
    firstError := firstError
    firstError_eq := rfl
    secondError := secondError
    secondError_eq := rfl
    products := products
    total := products.first + products.second + products.mixed
    total_eq := rfl }

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Integration.Energy in
open Purelib.Polynomial in
/-- Certify the original primitive triangle against an explicitly possible retained root reading.

The three points remain inside the same continued patch, and operational coefficient and increment bounds scale the
cached product budgets by the same coefficient squared norm. -/
def certificate (budget : PrimitiveTriangleBudget basis first second third) (coefficients : Coefficients count)
    (firstInside : patch.box.Contains first) (secondInside : patch.box.Contains second) (thirdInside :
      patch.box.Contains third)
    (sample : ContinuedNeighborhood.Point patch first) {root : Basic.Canonical}
    (possible : sample.certificate.value.name.process.Possible (sample.readingState index) root) :
    AffineTriangle.AffineTriangleErrorCertificate ((Geometry.EvaluationLower.coefficientPolynomial coefficients).eval
      first / root)
      first second third (basis.value coefficients first) (basis.value coefficients second) (basis.value coefficients
        third) := by
  have coefficientLe := basis.operational_coefficient_bound coefficients firstInside sample (sample.readingState index)
    possible
  have affineLe (point : Basic.Canonical) :
      normSq (AffineTriangle.affinePrimitiveIncrement ((Geometry.EvaluationLower.coefficientPolynomial
        coefficients).eval first / root) first point) ≤
        coefficientNormSq coefficients * (basis.coefficientScale * normSq (point - first)) := by
    unfold AffineTriangle.affinePrimitiveIncrement
    rw [← mul_sub, Basic.Canonical.normSq_mul]
    exact (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct coefficientLe (Basic.Canonical.normSq_nonneg
      _)).trans_eq (by ring1)
  refine budget.products.certificate (coefficientNormSq coefficients) (PrimitiveBasis.coefficientNorm_nonnegative
    coefficients)
    _ first second third _ _ _ ?_ ?_ ?_ ?_
  · rw [budget.firstAffine_eq]; exact affineLe second
  · rw [budget.secondAffine_eq]; exact affineLe third
  · rw [budget.firstError_eq, affine_error_eq]
    exact basis.operational_increment_bound coefficients firstInside secondInside sample possible
  · rw [budget.secondError_eq, affine_error_eq]
    exact basis.operational_increment_bound coefficients firstInside thirdInside sample possible

open Purelib.Data.Gaussian in
/-- The retained triangle certificate's total is the coefficient squared norm times its original total budget. -/
theorem certificate_total (budget : PrimitiveTriangleBudget basis first second third) (coefficients : Coefficients
  count)
    (firstInside : patch.box.Contains first) (secondInside : patch.box.Contains second) (thirdInside :
      patch.box.Contains third)
    (sample : ContinuedNeighborhood.Point patch first) {root : Basic.Canonical}
    (possible : sample.certificate.value.name.process.Possible (sample.readingState index) root) :
    (budget.certificate coefficients firstInside secondInside thirdInside sample possible).totalBudget =
      coefficientNormSq coefficients * budget.total := by
  change coefficientNormSq coefficients * budget.products.first + coefficientNormSq coefficients *
    budget.products.second +
    coefficientNormSq coefficients * budget.products.mixed = _
  rw [budget.total_eq]
  ring1

open Purelib.Data.Gaussian in
open Purelib.Integration.Energy in
open Purelib.Polynomial in
/-- The original affine triangle energy minus its homogeneous error budget bounds the primitive triangle energy.

All three points lie in the same continued neighborhood, and the root witness is explicitly possible at the original
sample's retained reading state. -/
theorem energy_lower (budget : PrimitiveTriangleBudget basis first second third) (coefficients : Coefficients count)
    (firstInside : patch.box.Contains first) (secondInside : patch.box.Contains second) (thirdInside :
      patch.box.Contains third)
    (sample : ContinuedNeighborhood.Point patch first) {root : Basic.Canonical}
    (possible : sample.certificate.value.name.process.Possible (sample.readingState index) root) :
    AffineTriangle.coordinateTriangleArea first second third *
      normSq ((Geometry.EvaluationLower.coefficientPolynomial coefficients).eval first / root) -
        coefficientNormSq coefficients * budget.total ≤
      AffineTriangle.primitiveTriangleEnergy (Polygon.energyPrimitivePoint (basis.value coefficients first))
        (Polygon.energyPrimitivePoint (basis.value coefficients second)) (Polygon.energyPrimitivePoint (basis.value
          coefficients third)) := by
  have bound := (budget.certificate coefficients firstInside secondInside thirdInside sample
    possible).affineEnergy_sub_totalBudget_le
  rw [budget.certificate_total, Norm.Basic.normSq_eq_canonical] at bound
  exact bound

end PrimitiveTriangleBudget

end Purelib.Riemann.Readings.PrimitiveTriangleEnergy
