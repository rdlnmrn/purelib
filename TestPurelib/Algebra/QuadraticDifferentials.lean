module

import Purelib.Algebra.Quadratic.Pair.Polynomial.Parameter
import Purelib.Riemann.Normalization.InverseModelDifferentialResidual
import Purelib.Riemann.Normalization.InverseModelPrimitiveResidual
import Purelib.Riemann.Normalization.InverseModelRemainderBounds
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Data.Rat.Fraction.Cast

/-!
# Quadratic differential laws and finite inverse-root models

Nonconstant radicands exercise the exact coefficient constructors. A constant
inverse-root model has a genuinely nonzero square residual at both its first
two stages, while its exact error equation is certified by the same cache.
-/

namespace TestPurelib.Algebra.QuadraticDifferentials

open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction
open Purelib.Polynomial.Dense
open Purelib.Polynomial.Dense.Basic
open DensePolynomial
open Purelib.Algebra.Quadratic.Pair.Polynomial
open Purelib.Riemann.Normalization
open Purelib.Riemann.Readings.PreparedObservationNeighborhoods (ObservationNeighborhood)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Approximation.Gaussian.Provenance.Power (PowerIdentity)

/-- The nonconstant radicand one plus the square of the spatial variable. -/
private def parameter : Coefficients := ⟨[1, 0, 1]⟩

/-- A primitive numerator equal to the original spatial coordinate. -/
private def numerator : Coefficients := ⟨[1, 0]⟩

example : (Expression.oddReciprocal parameter 0 numerator).derivative.Equal
    (Expression.oddPrimitiveDerivative parameter 0 numerator) :=
  Expression.derivative_oddReciprocal parameter numerator 0

example : (Expression.oddReciprocal parameter 1 numerator).derivative.Equal
    (Expression.oddPrimitiveDerivative parameter 1 numerator) :=
  Expression.derivative_oddReciprocal parameter numerator 1

example : (((Expression.inverseRoot parameter).derivative.scale (parameter.scale 2)).add
    ((Expression.inverseRoot parameter).scale
      (Derivative.derivative parameter))).Equal Expression.zero :=
  Expression.inverseRoot_equation parameter

/-- The retained nonconstant generator relation differentiates to zero. -/
private theorem nonconstant_relation :
    (((Expression.generator (radicand := parameter)).mul Expression.generator).sub
      (Expression.scalar parameter)).derivative.Equal Expression.zero :=
  Expression.derivative_generator_relation

/-- The finite directional generator rule also applies to the nonconstant radicand. -/
private theorem nonconstant_direction :
    ((Expression.generator (radicand := parameter)).directionalDerivative numerator 0 0 0).Equal
      ⟨⟨0, numerator⟩, parameter.scale 2⟩ := Expression.directional_generator parameter numerator

/-- The original primitive coefficient satisfies the polynomial product rule. -/
private theorem nonconstant_scaling :
    ((Expression.inverseRoot parameter).scale numerator).derivative.Equal
      (((Expression.inverseRoot parameter).derivative.scale numerator).add
        ((Expression.inverseRoot parameter).scale (Derivative.derivative numerator))) :=
  Expression.derivative_scale numerator (Expression.inverseRoot parameter)

/-- The original nonconstant radicand is nonzero at the exact spatial coordinate one. -/
private theorem parameter_one_nonzero : parameter.eval 1 ≠ 0 := by decide +kernel

/-- Build the finite regular observation site from the original nonconstant coefficient table. -/
private def site := ObservationNeighborhood.ofPoint parameter 0 1 parameter_one_nonzero

/-- Both original winding sheets produce actual continued regular neighborhoods of the same coordinate. -/
private def regular (sheet : Fin 2) :=
  ContinuedInverseRoot.ContinuedNeighborhood.ofOwner site (Owner.independent parameter_one_nonzero sheet)

/-- The continued site keeps the original exact center coordinate. -/
private theorem regular_center (sheet : Fin 2) : (regular sheet).base.site.center = 1 := rfl

/-- The certified regular box preserves nonvanishing of the original nonconstant radicand. -/
private theorem regular_nonzero (sheet : Fin 2) (point : Canonical)
    (inside : (regular sheet).box.Contains point) : parameter.eval point ≠ 0 :=
  (regular sheet).parameter_nonzero inside

/-- Acquire the original continued root at the retained center of its actual regular box. -/
private def regularPoint (sheet : Fin 2) :=
  ContinuedInverseRoot.ContinuedNeighborhood.Point.acquire (regular sheet) (regular sheet).base.site.center
    (regular sheet).center_inside

/-- Interpret an odd-power primitive at the same acquired original root on the certified regular box. -/
private def regularPrimitive (sheet : Fin 2) (pairs : Nat) :=
  let sample := regularPoint sheet
  (OddPowerDifferential.ofCoefficients parameter numerator pairs 1).interpret
    (regular sheet).base.site.center sample.certificate.value
    (PowerIdentity.ofSquare sample.certificate.square) sample.certificate.apart

/-- The actual interpreted primitive uses the same retained continued root channel. -/
private theorem regular_primitive_channel (sheet : Fin 2) (pairs : Nat) :
    (regularPrimitive sheet pairs).channel =
      ((OddPowerDifferential.ofCoefficients parameter numerator pairs 1).coefficient).denote
        (regular sheet).base.site.center (regularPoint sheet).certificate.value :=
  (regularPrimitive sheet pairs).channel_readback

/-- Interpret the original inverse root at that same acquired regular-sheet occurrence. -/
private def regularInverse (sheet : Fin 2) :=
  let sample := regularPoint sheet
  (OddPowerDifferential.ofCoefficients parameter (constant 1) 0 1).interpret
    (regular sheet).base.site.center sample.certificate.value
    (PowerIdentity.ofSquare sample.certificate.square) sample.certificate.apart

/-- The actual reciprocal on the regular nonconstant sheet realizes the same cached inverse-root pair. -/
private def regular_inverse_comparison (sheet : Fin 2) :=
  (regularInverse sheet).inverseRoot_reciprocal (regularPoint sheet).certificate.apart

/-- A displayed constant radicand equal to two. -/
private def two : Coefficients := constant 2

/-- The closed unit box retains the original endpoints in both coordinates. -/
private def box : Purelib.Geometry.Rational.Box := ⟨0, 1, 0, 1, by decide, by decide⟩

/-- A Gaussian rational coefficient built directly from integer fraction data. -/
private def fraction (numerator denominator : Int) : Canonical :=
  ⟨Cast.fromInt numerator / Cast.fromInt denominator, 0⟩

/-- A checked Newton model with value seven tenths and nonzero square residual. -/
private def model : InverseRootPolynomial.Model two box where
  value := constant (fraction 7 10)
  residual := constant (fraction 1 50)
  residual_eq := fun point => by
    rewrite [eval_constant, eval_constant, two, eval_constant]
    decide +kernel
  bound := Cast.fromInt 1 / Cast.fromInt 2500
  bound_nonnegative := by decide +kernel
  bound_small := by decide +kernel
  residualBound := fun point _ => by
    rewrite [eval_constant]
    decide +kernel

example : model.residual.eval 0 ≠ 0 := by
  change (constant (fraction 1 50)).eval 0 ≠ 0
  rewrite [eval_constant]
  decide +kernel

example : (model.refine 1).value.eval 0 = fraction 707 1000 := by decide +kernel

example : (model.refine 1).residual.eval 0 = fraction 151 500000 := by decide +kernel

example : (model.refine 1).residual.eval 0 ≠ 0 := by decide +kernel

example :
    let retained := InverseModelDifferentialResidual.DifferentialResidualBounds.build model
    InverseModelDifferentialResidual.ErrorEquation two retained.value retained.exactError retained.exactDerivative :=
  (InverseModelDifferentialResidual.DifferentialResidualBounds.build model).errorEquation

/-- The same constant radicand has exact uniform clearance on its original box. -/
private def clearance : Purelib.Riemann.Comparison.PrimitiveEdgeComparison.RegionClearance two box :=
  ⟨4, by decide, fun point _ => by rewrite [two, eval_constant]; decide +kernel⟩

/-- Retain the original model's uniform derivative data once. -/
private def rootBounds := InverseModelDerivativeBounds.DerivativeBounds.build clearance model

/-- Retain the original model's genuine differential residual once. -/
private def residualBounds := InverseModelDifferentialResidual.DifferentialResidualBounds.build model

/-- Retain the spatial numerator and its original derivative ceiling once. -/
private def primitiveBounds := InverseModelPrimitiveBounds.PrimitiveDerivativeBounds.build rootBounds numerator

/-- Compute the actual source-derived decay budget for a displayed positive sheet power. -/
private def budget (index : Nat) :=
  InverseModelPrimitiveResidual.PrimitiveResidualBounds.build rootBounds residualBounds primitiveBounds index

/-- The displayed strict request is constructed directly from retained rational fraction data. -/
private def target := Cast.fromInt 1 / Cast.fromInt 10000

/-- The zero coordinate belongs to the same original closed model box. -/
private theorem zeroInside : box.Contains 0 := by decide +kernel

example :
    let selected := (budget 0).choose 0 target (by decide +kernel)
    Purelib.Data.Gaussian.Basic.Canonical.normSq
      (InverseModelPrimitiveResidual.primitiveMismatch (model.refine selected.stage) numerator
        (budget 0).coefficient 0 0) < target :=
  (budget 0).selected_accurate_bound ((budget 0).choose 0 target (by decide +kernel)) zeroInside

example :
    let selected := (budget 2).choose 0 target (by decide +kernel)
    Purelib.Data.Gaussian.Basic.Canonical.normSq
      (InverseModelPrimitiveResidual.primitiveMismatch (model.refine selected.stage) numerator
        (budget 2).coefficient 2 0) < target :=
  (budget 2).selected_accurate_bound ((budget 2).choose 0 target (by decide +kernel)) zeroInside

/-- The original spatial numerator supplies the retained weighted square-residual coefficient. -/
private def remainder := InverseModelRemainderBounds.RemainderBounds.build rootBounds numerator

example :
    let selected := remainder.chooseConnection (budget 0) 0 target (by decide +kernel)
    Purelib.Approximation.Rational.Geometric.Basic.quarterRadius
      (remainder.connectionScale (budget 0)) (selected.stage + 1) < target :=
  (remainder.chooseConnection (budget 0) 0 target (by decide +kernel)).later_accurate (Nat.le_add_right _ _)

example :
    let selected := remainder.chooseScalar (budget 2) 0 target (by decide +kernel)
    Purelib.Data.Gaussian.Basic.Canonical.normSq
      ((model.refine selected.stage).residual.eval 0 *
          (numerator.eval 0 * (model.refine selected.stage).value.eval 0 ^ 3 -
            (model.refine selected.stage).value.eval 0 * (2 - (model.refine selected.stage).residual.eval 0)) -
        InverseModelPrimitiveResidual.primitiveMismatch (model.refine selected.stage) numerator
          (budget 2).coefficient 2 0) < target := by
  let selected := remainder.chooseScalar (budget 2) 0 target (by decide +kernel)
  have bound := remainder.scalar_bound (budget 2) selected.stage zeroInside
  rewrite [← selected.allowance_eq] at bound
  exact bound.trans_lt selected.accurate

end TestPurelib.Algebra.QuadraticDifferentials
