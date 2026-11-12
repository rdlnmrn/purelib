module

public import Purelib.Curves.Legendre.Periods.Jets.Variation.Sampling
public import Purelib.Curves.Legendre.Degeneration.UnitRoot
import Purelib.Approximation.Gaussian.Process.Sampling
import Purelib.Data.Rat.Fraction.Square.Check
import Purelib.Data.Rat.Fraction.Cast
import Purelib.Data.Gaussian.Field
import Purelib.Tactic.Ring

/-! # Paid parameter variation from two retained original root owners

At the fixed spatial coordinate two, parameter three halves has radicand one,
and an increment of one eighth gives radicand three quarters. Both original
tracked roots are constructed in the same positive-real signed window. The
first radicand has the exact rational root one; the target radicand has no
rational Gaussian root, so its actual selected reading has a nonzero residual.

The fixture keeps the original owner and certificate caches. The generic
sampler pays both square residuals before the shared inverse/cubic caches
construct both value and first derivative row banks. Assertions use retained
readback laws rather than executing the tracked sampling algorithm in proofs.
-/

namespace TestPurelib.Curves.Legendre.PeriodVariation.Sampling

open Purelib
open Purelib.Approximation.Gaussian
open Purelib.Calculus.Jet
open Purelib.Curves.Legendre
open Purelib.Curves.Legendre.PicardFuchs
open Purelib.Curves.Legendre.Periods.Jets
open Purelib.Data
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Geometry.Rational
open Purelib.Riemann.RootContinuation
open Purelib.Riemann.Topology

/-- The fixed original Legendre parameter shared by both row banks. -/
@[expose] public def parameter : Canonical := ⟨3 / 2, 0⟩

/-- The nonzero original parameter increment used by both observations. -/
@[expose] public def increment : Canonical := ⟨1 / 8, 0⟩

/-- The computed fourth-order residual tolerance, using the direct integer cast of its denominator. -/
private def tolerance : Fraction.Rational := 1 / Fraction.Cast.fromInt 4096

/-- The common signed positive-real square containing both original root tracks. -/
@[expose] public def window : Box := Degeneration.UnitRoot.box 1

/-- The original left-side exclusion of zero on the retained signed window. -/
@[expose] public def side : window.OutsideSide 0 := .left (by decide +kernel)

/-- Construct the positive original track of the source radicand from the existing signed owner machinery. -/
@[expose] public def sourceOwner : SquareRootContinuationChain.Owner (Polynomials.curveValue parameter 2) := by
  change SquareRootContinuationChain.Owner ((Degeneration.unitPolynomial 1).eval 1)
  exact Degeneration.UnitRoot.owner 1 1 (by decide +kernel)

/-- Construct the positive original track of the nonsquare target radicand in the same signed window. -/
@[expose] public def targetOwner :
    SquareRootContinuationChain.Owner (Polynomials.curveValue (parameter + increment) 2) := by
  change SquareRootContinuationChain.Owner ((Degeneration.unitPolynomial 1).eval (⟨3 / 4, 0⟩ : Canonical))
  exact Degeneration.UnitRoot.owner 1 ⟨3 / 4, 0⟩ (by decide +kernel)

/-- Cache the certificate of the exact retained source owner. -/
@[expose] public def source : CertifiedSquareRoot.Certificate (Polynomials.curveValue parameter 2) :=
  sourceOwner.certificate sourceOwner.parameterNonzero

/-- Cache the certificate of the distinct retained target owner. -/
@[expose] public def target : CertifiedSquareRoot.Certificate (Polynomials.curveValue (parameter + increment) 2) :=
  targetOwner.certificate targetOwner.parameterNonzero

/-- The actual source track retains the original common signed box. -/
private theorem source_box : sourceOwner.track.initial.box = window :=
  Degeneration.UnitRoot.owner_initial_box 1 1 (by decide +kernel)

/-- The actual target track retains that same signed box. -/
private theorem target_box : targetOwner.track.initial.box = window :=
  Degeneration.UnitRoot.owner_initial_box 1 ⟨3 / 4, 0⟩ (by decide +kernel)

/-- The finite increment remains inside the original unit-quadrance Taylor range. -/
public theorem increment_unit : Norm.Basic.normSq increment ≤ 1 := by decide +kernel

/-- Retain the original signed window and one core built from the same two requested owner observations. -/
public def windowJet : Variation.Sampling.WindowedJet parameter increment 2 source target window side increment_unit :=
  Variation.Sampling.buildFromOwners parameter increment 2 source target sourceOwner targetOwner rfl rfl
    window side
    (by rewrite [source_box]; exact Box.refines_refl window)
    (by rewrite [target_box]; exact Box.refines_refl window)
    (by decide +kernel) increment_unit

/-- Read the identical scalar core cached in the original window view. -/
public abbrev jet : Variation.Sampling.SampledJet parameter increment 2 source target increment_unit := windowJet.core

-- Keep the actual retained processes and sampling indices opaque to scalar
-- assertions, which consume their existing readback and payment theorems.
attribute [local irreducible] sourceOwner targetOwner source target windowJet

/-- The source radicand has the exact rational Gaussian root one. -/
theorem source_exact_square : (1 : Canonical) * 1 = Polynomials.curveValue parameter 2 := by decide +kernel

/-- The selected source state is the actual state of its original certificate process at the chosen comparison index. -/
theorem source_state : jet.sourceSample.state =
    Process.Sampling.stateAt source.value.name.process source.value.name.state jet.sourceSample.comparison.leftIndex :=
  jet.sourceSample.state_eq

/-- The target retains its own original process state and its independently selected comparison index. -/
theorem target_state : jet.targetSample.state =
    Process.Sampling.stateAt target.value.name.process target.value.name.state jet.targetSample.comparison.leftIndex :=
  jet.targetSample.state_eq

/-- The shared request is exactly the fourth-order increment quadrance. -/
theorem fourth_order_accuracy : jet.accuracy.tolerance = tolerance := by
  rewrite [jet.accuracy_eq]
  change Norm.Basic.normSq (⟨1 / 8, 0⟩ : Canonical) ^ 2 = 1 / Fraction.Cast.fromInt 4096
  decide +kernel

/-- The actual source reading pays the retained fourth-order square-residual request. -/
theorem source_residual :
    Norm.Basic.normSq (jet.sourceSample.reading * jet.sourceSample.reading - Polynomials.curveValue parameter 2) <
      tolerance :=
  jet.sourceSample.reading_residual_lt.trans_eq fourth_order_accuracy

/-- The distinct actual target reading pays the same request on the original target radicand. -/
theorem target_residual :
    Norm.Basic.normSq
      (jet.targetSample.reading * jet.targetSample.reading - Polynomials.curveValue (parameter + increment) 2) <
      tolerance :=
  jet.targetSample.reading_residual_lt.trans_eq fourth_order_accuracy

/-- The source reading retains its original certificate's quantitative denominator clearance. -/
theorem source_original_lower : source.apart.certificate.lowerSq ≤ Norm.Basic.normSq jet.sourceSample.reading :=
  jet.source_lower

/-- The target reading retains the distinct original certificate's quantitative denominator clearance. -/
theorem target_original_lower : target.apart.certificate.lowerSq ≤ Norm.Basic.normSq jet.targetSample.reading :=
  jet.target_lower

/-- The original signed side separately bounds the actual source reading's squared norm by one quarter. -/
theorem source_window_lower : (1 / 4 : Fraction.Rational) ≤ Norm.Basic.normSq jet.sourceSample.reading := by
  have bound := side.margin_le_normSq_sub windowJet.sourceInside
  rewrite [show side.margin = (1 / 4 : Fraction.Rational) by decide +kernel, Gaussian.Basic.sub_zero] at bound
  exact bound

/-- The same signed side bounds the distinct actual target reading by the same geometric floor. -/
theorem target_window_lower : (1 / 4 : Fraction.Rational) ≤ Norm.Basic.normSq jet.targetSample.reading := by
  have bound := side.margin_le_normSq_sub windowJet.targetInside
  rewrite [show side.margin = (1 / 4 : Fraction.Rational) by decide +kernel, Gaussian.Basic.sub_zero] at bound
  exact bound

/-- The actual two original readings have squared sum at least one by their signed-window margin. -/
theorem sum_lower : (1 : Fraction.Rational) ≤
    Norm.Basic.normSq (jet.sourceSample.reading + jet.targetSample.reading) := by
  have bound := windowJet.sum_lower
  rewrite [show 4 * side.margin = (1 : Fraction.Rational) by decide +kernel] at bound
  exact bound

/-- The actual source reading lies in its original owner's initial box. -/
theorem source_original_box : sourceOwner.track.initial.box.Contains jet.sourceSample.reading :=
  jet.sourceSample.reading_in_initial_box sourceOwner (by unfold source; rfl)

/-- The actual target reading lies in its distinct original owner's initial box. -/
theorem target_original_box : targetOwner.track.initial.box.Contains jet.targetSample.reading :=
  jet.targetSample.reading_in_initial_box targetOwner (by unfold target; rfl)

/-- No Gaussian rational in the original positive-real signed window squares to the target radicand. -/
private theorem target_nonsquare {reading : Canonical} (inside : window.Contains reading) :
    reading * reading ≠ Polynomials.curveValue (parameter + increment) 2 := by
  intro equal
  have realEquation : reading.re * reading.re - reading.im * reading.im = 3 / 4 :=
    congrArg Canonical.re equal
  have imaginaryEquation : reading.re * reading.im + reading.im * reading.re = 0 :=
    congrArg Canonical.im equal
  have realPositive : (0 : Fraction.Rational) < reading.re :=
    (by decide +kernel : (0 : Fraction.Rational) < 1 / 2).trans_le inside.1
  have imaginaryZero : reading.im = 0 := by
    apply Fraction.mul_left_cancel_of_nonzero (factor := 2 * reading.re)
      (Fraction.Field.mul_ne_zero_direct (by decide +kernel) realPositive.ne')
    calc
      _ = reading.re * reading.im + reading.im * reading.re := by ring1
      _ = 0 := imaginaryEquation
      _ = _ := by ring1
  have square : reading.re * reading.re = (3 / 4 : Fraction.Rational) := by
    rewrite [imaginaryZero] at realEquation
    exact (show reading.re * reading.re = reading.re * reading.re - 0 * 0 by ring1).trans realEquation
  exact (Fraction.Square.inspect (3 / 4)).not_square_of_missing (by decide +kernel) reading.re square

/-- The actual selected target reading has a nonzero residual, so its retained payment is substantive. -/
theorem target_residual_nonzero :
    jet.targetSample.reading * jet.targetSample.reading - Polynomials.curveValue (parameter + increment) 2 ≠ 0 := by
  intro zero
  apply target_nonsquare windowJet.targetInside
  calc
    _ = (jet.targetSample.reading * jet.targetSample.reading -
        Polynomials.curveValue (parameter + increment) 2) +
        Polynomials.curveValue (parameter + increment) 2 := by ring1
    _ = 0 + Polynomials.curveValue (parameter + increment) 2 :=
      congrArg (fun value : Canonical => value + Polynomials.curveValue (parameter + increment) 2) zero
    _ = _ := by ring1

/-- The actual nonsquare target reading has strictly positive square-residual quadrance below its paid request. -/
theorem target_residual_positive : 0 < Norm.Basic.normSq
    (jet.targetSample.reading * jet.targetSample.reading - Polynomials.curveValue (parameter + increment) 2) :=
  Norm.Basic.normSq_pos target_residual_nonzero

/-- Every value-row entry uses the same retained inverse-root certificate cache. -/
theorem value_cache (coordinate : Fin 2) : jet.value coordinate = jet.inverse.scale
    ((Specification.valueSpecification parameter coordinate).scale *
      (Specification.valueSpecification parameter coordinate).numerator.eval 2) :=
  jet.value_eq coordinate

/-- The cubic certificate composes the exact retained inverse cache with the original coordinate-cube polynomial. -/
theorem cubic_cache : jet.cubic = jet.inverse.compose
    (Quadratic.Polynomial.certificate
      (Polynomial.Dense.Gaussian.Power.Coordinate.coordinatePositivePower 2) jet.inverse.base jet.inverse.output)
    (by simpa only [Norm.Basic.normSq_eq_canonical] using increment_unit) :=
  jet.cubic_eq

/-- Every first derivative-row entry uses the same retained cubic composition cache. -/
theorem first_cache (coordinate : Fin 2) : jet.first coordinate = jet.cubic.scale
    ((Specification.firstDerivativeSpecification parameter coordinate).scale *
      (Specification.firstDerivativeSpecification parameter coordinate).numerator.eval 2) :=
  jet.first_eq coordinate

/-- The value-bank slope is the original first differential row on the actual retained source reading. -/
theorem value_original_slope (coordinate : Fin 2) :
    (jet.value coordinate).slope = Variation.firstReading coordinate 2 jet.sourceSample.reading := by
  rewrite [jet.value_agrees coordinate, Variation.valueCertificate_slope]
  rfl

/-- The first-bank slope is the original second differential row on that same retained source reading. -/
theorem first_original_slope (coordinate : Fin 2) :
    (jet.first coordinate).slope = Variation.secondReading coordinate 2 jet.sourceSample.reading := by
  rewrite [jet.first_agrees coordinate, Variation.firstCertificate_slope]
  rfl

/-- Both original value rows satisfy their constructed finite remainder bounds on the actual paid readings. -/
theorem value_remainder (coordinate : Fin 2) :
    Canonical.normSq ((jet.value coordinate).output - (jet.value coordinate).base -
      increment * (jet.value coordinate).slope) ≤
      (jet.value coordinate).factor * Canonical.normSq increment ^ 2 := by
  rewrite [(jet.value coordinate).expansion]
  exact (jet.value coordinate).remainder_le

/-- Both original first derivative rows satisfy their finite bounds using the same two paid observations. -/
theorem first_remainder (coordinate : Fin 2) :
    Canonical.normSq ((jet.first coordinate).output - (jet.first coordinate).base -
      increment * (jet.first coordinate).slope) ≤
      (jet.first coordinate).factor * Canonical.normSq increment ^ 2 := by
  rewrite [(jet.first coordinate).expansion]
  exact (jet.first coordinate).remainder_le

end TestPurelib.Curves.Legendre.PeriodVariation.Sampling
