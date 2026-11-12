module

public import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Uniform
public import Purelib.Curves.Hyperelliptic.Sheets.Continued
public import Purelib.Integration.Polynomial.Gaussian.Cell.Spatial.Observation
public import Purelib.Riemann.Normalization.ContinuedInverseRoot.Primitive.Uniform
public import Purelib.Algebra.Quadratic.Pair.Gaussian.Observation.Precision
public import Purelib.Algebra.Quadratic.Pair.Polynomial.Gaussian.Observation
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Tactic.Ring

/-!
# Productive observations from original continued-root models

The original local polynomial, coefficient denotation and shared root witness
are retained separately. A uniform source request pays the actual polynomial
residual, and a shared generator request pays the actual channel radius.
These two payments construct the existing odd-power observation certificate.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Integration.Algebraic.Uniform.Jets.UniformObservation

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction
open Purelib.Algebra.Quadratic.Pair.Polynomial (Coefficients Expression)
open Purelib.Algebra.Quadratic.Pair.Gaussian (ReadingPrecision)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.Normalization.ContinuedInverseRoot.ContinuedNeighborhood (UniformBounds UniformRequest)
open Purelib.Riemann.Normalization.ContinuedInverseRoot.ContinuedNeighborhood.Point
open Purelib.Riemann.Normalization.InverseRootPolynomial (Model)
open Purelib.Polynomial.Dense.Power (OddPowers)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedCell)
open Purelib.Integration.Polynomial.Gaussian.Cell
open Purelib.Integration.Polynomial.Gaussian.Cell.Basic (LocalObservation)
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential coefficientSpec)
open Purelib.Curves.Hyperelliptic.Sheets.Basic (AlgebraicSheetValue)

attribute [local irreducible] Riemann.RootContinuation.CertifiedSquareRoot.rawRoot

/-- Two quarter-allowances equal the original half-allowance. -/
private theorem twice_quarter (allowance : Rational) : 2 * (allowance / 4) = allowance / 2 := by
  rewrite [Fraction.Field.div_eq_mul_inv_direct, Fraction.Field.div_eq_mul_inv_direct]
  calc
    _ = allowance * ((2 : Rational) * (4 : Rational)⁻¹) := by ring1
    _ = _ := by rewrite [show (2 : Rational) * (4 : Rational)⁻¹ = (2 : Rational)⁻¹ by decide +kernel]; rfl

/-- A positive allowance pays its own quarter. -/
private theorem quarter_le (allowance : Rational) (positive : 0 < allowance) : allowance / 4 ≤ allowance := by
  apply (Order.Field.div_le_iff_pos (by decide : (0 : Rational) < 4)).mpr
  have scaled := Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (by decide : (1 : Rational) ≤ 4) positive.le
  rewrite [Fraction.Field.mul_one_direct] at scaled
  exact scaled

/-- Two half-allowances equal the original allowance. -/
private theorem half_add_half (allowance : Rational) : allowance / 2 + allowance / 2 = allowance := by
  calc
    _ = (allowance / 2) * 2 := by ring1
    _ = allowance := Fraction.Field.div_mul_cancel_of_ne allowance 2 (by decide)

/-- Reversing the actual retained source residual preserves its squared norm. -/
private theorem reverse_residual {polynomial : Coefficients} {count : Nat}
    {patch : ContinuedNeighborhood polynomial count} {point : Canonical}
    {sample : ContinuedNeighborhood.Point patch point}
    {depth : Nat} {model : Model polynomial patch.base.box} {powers : OddPowers model.value}
    {reading : PrimitiveReading sample depth model powers} {pairs : Fin 3} {numerator : Coefficients}
    {original : PrimitiveDenotation sample pairs numerator} {source : Coefficients}
    (value : PrimitiveValue reading pairs numerator original source) :
    Norm.Basic.normSq (value.linear - value.value) = Norm.Basic.normSq value.residual := by
  have reversed : value.linear - value.value = -value.residual := by
    rewrite [value.residual_eq]
    apply Basic.ext <;> simp only [Basic.sub_re, Basic.sub_im, Basic.neg_re, Basic.neg_im] <;> ring1
  rewrite [reversed, Norm.Basic.normSq_neg]
  rfl

/-- Construct the original odd-power observation from cached source data and its internally derived finite payments.

The exact original cell table is retained. Its same-point scalar readback
uses the original numerator and shared inverse-model power. The selected
root witness and state are shared by the cached reading; neither source
refinement nor root selection is repeated by this constructor. -/
@[noinline, nospecialize] def ofContinuedPrimitive {genus count depth : Nat}
    (curve : Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : OddPowerDifferential curve.polynomial) (pairs : Fin 3)
    (pairs_eq : differential.denominatorPairs = pairs.val)
    {start finish : LiftedPoint 2} (liftedCell : LiftedCell start finish)
    {coordinate : Spatial.Coordinate start.coordinate finish.coordinate}
    {source : Coefficients} {allowance : Rational} (pullback : Spatial.Pullback coordinate source allowance)
    (parameter : Rational) {patch : ContinuedNeighborhood curve.polynomial count}
    (sample : ContinuedNeighborhood.Point patch (coordinate.point parameter))
    (inside : patch.box.Contains (coordinate.point parameter))
    {bounds : UniformBounds patch} {floor : Nat}
    (request : UniformRequest bounds pairs (differential.numerator.scale differential.scale) floor (allowance / 4))
    {model : Model curve.polynomial patch.base.box} (sameModel : model = patch.base.refine depth)
    {powers : OddPowers model.value} {ceiling : Rational} (precision : ReadingPrecision ceiling allowance)
    (root : PrimitiveRoot sample depth precision.target)
    (reading : PrimitiveReading sample depth model powers)
    (reading_eq : reading = root.readModel model sameModel powers)
    (original : PrimitiveDenotation sample pairs (differential.numerator.scale differential.scale))
    (value : PrimitiveValue reading pairs (differential.numerator.scale differential.scale) original source)
    (stage : request.selection.stage ≤ depth) (coefficient_le : Norm.Basic.normSq original.value.im ≤ ceiling) :
    Uniform.Jets.UniformObservation curve differential liftedCell pullback.model parameter := by
  have residualBound := request.residual_lt sample.primitiveBounds value inside stage
  have errorBound : Norm.Basic.normSq (value.linear - value.value) ≤ allowance / 4 :=
    (reverse_residual value).trans_le residualBound.le
  have valueReading := value.value_eq
  rewrite [value.polynomial_eq] at valueReading
  let observation : LocalObservation pullback.model.polynomial pullback.model.localAllowance :=
    { parameter := parameter
      integrandReading := value.linear
      error := value.linear - value.value
      decomposition := by rewrite [pullback.eval_point, ← valueReading]; rfl
      error_le := by
        rewrite [pullback.allowance_eq, ← Norm.Basic.normSq_eq_canonical]
        exact errorBound.trans (quarter_le allowance precision.positive) }
  have expression_eq : Expression.oddReciprocal curve.polynomial pairs.val
      (differential.numerator.scale differential.scale) = differential.coefficient := by
    rewrite [differential.coefficient_eq, coefficientSpec, pairs_eq]
    rfl
  let interpretation := original.castExpression expression_eq
  have interpretationValue : interpretation.value = original.value := original.castExpression_value expression_eq
  have possible := interpretation.reading_possible reading.state reading.root reading.possible
  rewrite [interpretationValue, ← value.linear_readback] at possible
  have sameState : reading.state = root.state := by
    rewrite [reading_eq]
    exact root.readModel_state model sameModel powers
  have radius := interpretation.reading_radius reading.state
  rewrite [interpretationValue, sameState] at radius
  have normNonnegative := Norm.Basic.normSq_nonneg original.value.im
  have radiusCost : 64 * Norm.Basic.normSq original.value.im *
      (sample.certificate.value.name.process.ball root.state).radiusSq ≤ allowance / 2 :=
    (Order.Arithmetic.mul_le_mul_of_nonneg_left_direct root.radius_lt.le
      (Order.Arithmetic.mul_nonneg_direct (by decide +kernel) normNonnegative)).trans
      (precision.payment original.value.im coefficient_le)
  have residualCost : 2 * Norm.Basic.normSq (value.linear - value.value) ≤ allowance / 2 :=
    (Order.Arithmetic.mul_le_mul_of_nonneg_left_direct errorBound (by decide)).trans_eq (twice_quarter allowance)
  have semantic : 2 * (4 *
      (interpretation.channel.name.process.ball (interpretation.readingState reading.state)).radiusSq +
        Norm.Basic.normSq (value.linear - value.value)) ≤ pullback.model.localAllowance := by
    rewrite [pullback.allowance_eq, sameState, radius]
    calc
      _ = 64 * Norm.Basic.normSq original.value.im *
          (sample.certificate.value.name.process.ball root.state).radiusSq +
          2 * Norm.Basic.normSq (value.linear - value.value) := by ring1
      _ ≤ allowance / 2 + allowance / 2 := Order.Arithmetic.add_le_add_direct radiusCost residualCost
      _ = allowance := half_add_half allowance
  exact
    { observation := observation
      parameter_eq := rfl
      algebraic :=
        { point := coordinate.point parameter
          point_eq := (pullback.observationPoint_eq observation).symm
          sheetValue := AlgebraicSheetValue.ofContinuedPoint curve sample start.sheet
          chosenSheet_eq := rfl
          interpretation := interpretation
          readingState := interpretation.readingState reading.state
          readingPossible := possible }
      semantic_error_le := semantic }

/-- The actual continued-primitive observation keeps the original selected point certificate as its sheet generator.

The name belongs to the exact input point and certificate. The retained
coefficient interpretation, reading state and source polynomial are unchanged;
the equality does not identify independent point owners from sheet labels.
-/
theorem ofContinuedPrimitive_root_name {genus count depth : Nat}
    (curve : Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : OddPowerDifferential curve.polynomial) (pairs : Fin 3)
    (pairs_eq : differential.denominatorPairs = pairs.val)
    {start finish : LiftedPoint 2} (liftedCell : LiftedCell start finish)
    {coordinate : Spatial.Coordinate start.coordinate finish.coordinate}
    {source : Coefficients} {allowance : Rational} (pullback : Spatial.Pullback coordinate source allowance)
    (parameter : Rational) {patch : ContinuedNeighborhood curve.polynomial count}
    (sample : ContinuedNeighborhood.Point patch (coordinate.point parameter))
    (inside : patch.box.Contains (coordinate.point parameter))
    {bounds : UniformBounds patch} {floor : Nat}
    (request : UniformRequest bounds pairs (differential.numerator.scale differential.scale) floor (allowance / 4))
    {model : Model curve.polynomial patch.base.box} (sameModel : model = patch.base.refine depth)
    {powers : OddPowers model.value} {ceiling : Rational} (precision : ReadingPrecision ceiling allowance)
    (root : PrimitiveRoot sample depth precision.target)
    (reading : PrimitiveReading sample depth model powers)
    (reading_eq : reading = root.readModel model sameModel powers)
    (original : PrimitiveDenotation sample pairs (differential.numerator.scale differential.scale))
    (value : PrimitiveValue reading pairs (differential.numerator.scale differential.scale) original source)
    (stage : request.selection.stage ≤ depth) (coefficient_le : Norm.Basic.normSq original.value.im ≤ ceiling) :
    (ofContinuedPrimitive curve differential pairs pairs_eq liftedCell pullback parameter sample inside request
      sameModel precision root reading reading_eq original value stage coefficient_le).algebraic.sheetValue.value.name =
      sample.certificate.value.name := by rfl

end Purelib.Curves.Hyperelliptic.Integration.Algebraic.Uniform.Jets.UniformObservation

end
