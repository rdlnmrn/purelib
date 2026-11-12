module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Primitive.Taylor
public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential
public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Tangent.Polynomial
public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Ordinate
public import Purelib.Curves.Hyperelliptic.Differentials.OddPower.Derivative.Factorization
import Purelib.Polynomial.Quadratic.Split
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring

/-!
# The paid spatial derivative discrepancy of the original chart primitive

The actual primitive chart constructor retains its computed chain-rule slope.
The independent original cubic derivative has a different scalar evaluation
at the displayed inexact cofactor root. The source root's fourth-power
residual, original coordinate/velocity budgets and distinct root floors pay
this discrepancy with a fixed finite factor. No desired derivative equality
or integral endpoint law is assumed.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Primitive.Taylor

open Purelib
open Purelib.Approximation
open Purelib.Calculus.Jet
open Purelib.Curves.Hyperelliptic.Differentials
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Data
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Geometry.Gaussian.UnitCircle
open Purelib.Riemann.RootContinuation

variable {site : Fin 2} {parameter : Canonical} {quarter : UnitCircuitQuarter}
variable {positive : (0 : Fraction.Rational) < 2}
variable {actual : Transport.Quarter site parameter 2 quarter positive}
variable {time delta : Fraction.Rational}
variable {firstInside : FixedRootBoxPath.Inside time} {lastInside : FixedRootBoxPath.Inside (time + delta)}

/-- The full factored spatial derivative reads the original chart pullback at the same displayed cofactor. -/
theorem spatialReading_eq {primitive : OddPowerDifferential (Paths.polynomial parameter)}
    (specification : OddPower.Derivative.Specification (Paths.polynomial parameter) primitive)
    (regular : parameter ≠ criticalValue site) (cofactor : Canonical) :
    OddPower.Derivative.Factorization.spatialReading specification
      (point site parameter 2 (Waist.direction quarter time) positive).base
      (point site parameter 2 (Waist.direction quarter time) positive).ordinate cofactor
      (Tangent.baseVelocity site parameter 2 quarter time) =
    Differential.reading site parameter quarter time specification.differential cofactor := by
  let ordinate := (point site parameter 2 (Waist.direction quarter time) positive).ordinate
  have nonzero : ordinate ≠ 0 := parallel_ordinate_ne_zero site parameter (Waist.direction quarter time) regular
  have inverse : ordinate⁻¹ * ordinate = 1 := by
    simpa only [Gaussian.Field.inv_eq] using Gaussian.Field.inv_mul ordinate nonzero
  have cancellation : ordinate * ordinate⁻¹ ^ specification.differential.denominatorExponent =
      ordinate⁻¹ ^ (2 * specification.differential.denominatorPairs) := by
    change ordinate * ordinate⁻¹ ^ (2 * specification.differential.denominatorPairs + 1) = _
    calc
      _ = ordinate⁻¹ ^ (2 * specification.differential.denominatorPairs) * (ordinate⁻¹ * ordinate) := by
        rewrite [pow_succ]
        ring1
      _ = _ := by rewrite [inverse, Gaussian.Basic.mul_one]; rfl
  unfold OddPower.Derivative.Factorization.spatialReading Differential.reading
  rewrite [Tangent.baseVelocity_eq_ordinate_mul site parameter 2 quarter positive time]
  calc
    _ = (specification.differential.scale * specification.differential.numerator.eval
        (point site parameter 2 (Waist.direction quarter time) positive).base) *
        Stereographic.Tangent.logarithmicVelocity time *
        (ordinate * ordinate⁻¹ ^ specification.differential.denominatorExponent) *
        cofactor⁻¹ ^ specification.differential.denominatorExponent := by dsimp only [ordinate]; ring1
    _ = _ := by rewrite [cancellation]; rfl

/-- The fixed original chart and coefficient budgets determine the finite source-residual discrepancy factor. -/
@[expose] def slopeResidualFactor (site : Fin 2) (parameter : Canonical)
    (primitive : OddPowerDifferential (Paths.polynomial parameter)) : Fraction.Rational :=
  let gap := Norm.Basic.normSq (halfGap site parameter)
  OddPower.Derivative.Factorization.factor primitive (spatialBox site)
    ((9 / 16) * gap) (1 / 16) ((25 / 4) * gap) ((25 / 16) * gap) ((25 / 4) * gap)

/-- Intrinsic regularity makes the original fixed chart discrepancy factor nonnegative. -/
theorem slopeResidualFactor_nonnegative (site : Fin 2) (parameter : Canonical)
    (primitive : OddPowerDifferential (Paths.polynomial parameter)) (regular : parameter ≠ criticalValue site) :
    0 ≤ slopeResidualFactor site parameter primitive := by
  have gapNonnegative := Norm.Basic.normSq_nonneg (halfGap site parameter)
  have positive : 0 < (9 / 16) * Norm.Basic.normSq (halfGap site parameter) :=
    Fraction.Order.Arithmetic.mul_pos_direct (by decide +kernel)
      (Norm.Basic.normSq_pos (Polynomial.Quadratic.Split.halfGap_ne_zero (by decide +kernel) regular.symm))
  exact OddPower.Derivative.Factorization.factor_nonnegative primitive (spatialBox site)
    positive (by decide +kernel)
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel) gapNonnegative)
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel) gapNonnegative)
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel) gapNonnegative)

/-- The actual source residual pays the independent spatial derivative's discrepancy from the chart builder.

The original source and target cofactor observations remain unchanged.
Intrinsic regularity and original admission derive both positive floors;
original conic and tangent laws derive the required curve product rule.
The fixed factor is independent of chart increment and sampling indices.
-/
theorem scalar_slope_le (primitive : OddPowerDifferential (Paths.polynomial parameter))
    (source : Transport.Reading actual time firstInside)
    (target : Transport.Reading actual (time + delta) lastInside) (regular : parameter ≠ criticalValue site)
    (accuracy : AccuracyRequest)
    (sourceSample : CertifiedSquareRoot.Sampling.ResidualObservation source.lift.unitRoot accuracy)
    (targetSample : CertifiedSquareRoot.Sampling.ResidualObservation target.lift.unitRoot accuracy)
    (accuracy_eq : accuracy.tolerance = delta ^ 4)
    (specification : OddPower.Derivative.Specification (Paths.polynomial parameter) primitive) :
    Norm.Basic.normSq
      (Differential.reading site parameter quarter time specification.differential sourceSample.reading -
      (build primitive source target regular accuracy sourceSample targetSample accuracy_eq).certificate.slope) ≤
      slopeResidualFactor site parameter primitive * delta ^ 4 := by
  let first := point site parameter 2 (Waist.direction quarter time) positive
  have sourceInside := point_inside site parameter 2 (Waist.direction quarter time) positive
    actual.data.lower actual.data.upper actual.data.bound
  have sourceLower : (1 / 16 : Fraction.Rational) ≤ Norm.Basic.normSq sourceSample.reading :=
    UnitRoot.root_normSq_lower site sourceInside
      (sourceSample.reading_residual_lt_target source.lift.unitOwner source.lift.unitRoot_eq).le
  have ordinatePositive : 0 < (9 / 16) * Norm.Basic.normSq (halfGap site parameter) :=
    Fraction.Order.Arithmetic.mul_pos_direct (by decide +kernel)
      (Norm.Basic.normSq_pos (Polynomial.Quadratic.Split.halfGap_ne_zero (by decide +kernel) regular.symm))
  have curveVelocity : specification.polynomialDerivative.eval first.base *
      Tangent.baseVelocity site parameter 2 quarter time =
      1 * Tangent.baseVelocity site parameter 2 quarter time * (first.ordinate * first.ordinate) +
        2 * (unitPolynomial site).eval first.base * first.ordinate *
          Tangent.ordinateVelocity site parameter 2 quarter time := by
    rewrite [specification.polynomialDerivative_eq, Gaussian.Basic.one_mul]
    exact Tangent.curveVelocity_eq site parameter 2 quarter positive time
  rewrite [build_slope_eq primitive source target regular accuracy sourceSample targetSample accuracy_eq specification,
    ← spatialReading_eq specification regular sourceSample.reading]
  exact OddPower.Derivative.Factorization.difference_normSq_le specification first.base first.ordinate
    sourceSample.reading (Tangent.baseVelocity site parameter 2 quarter time)
    (Tangent.ordinateVelocity site parameter 2 quarter time) ((unitPolynomial site).eval first.base) 1
    (parallel_ordinate_ne_zero site parameter (Waist.direction quarter time) regular)
    sourceSample.reading_nonzero first.polynomial_eq curveVelocity sourceInside ordinatePositive (by decide +kernel)
    (parallel_ordinate_lower site parameter (Waist.direction quarter time)) sourceLower
    (Tangent.baseVelocity_normSq_le site parameter 2 quarter positive actual.data.lower actual.data.upper time)
    (point_ordinate_normSq_le site parameter 2 (Waist.direction quarter time) positive
      actual.data.lower actual.data.upper)
    (Tangent.ordinateVelocity_normSq_le site parameter 2 quarter positive actual.data.lower actual.data.upper time)
    (sourceSample.reading_residual_lt.le.trans_eq accuracy_eq)

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Primitive.Taylor

end
