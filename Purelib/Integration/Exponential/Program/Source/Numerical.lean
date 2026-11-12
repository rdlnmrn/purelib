module
public import Purelib.Integration.Exponential.Program.Source.Comparison
public import Purelib.Integration.Cell.Source.Numerical
public import Purelib.Integration.Cell.Numerical.Common.Weights
public import Purelib.Approximation.Gaussian.Exponential.Horner.Real.Numerical
import Purelib.Data.Rat.Fraction.Order.Arithmetic

/-!
# Comparing original exponential stages with numerical source frontiers

The original finite Taylor frontier is viewed through exact rational point
processes, retaining its cached readings. Common queries then compare it
with the actual original Gaussian exponential point states and their finite
coordinate intervals.
-/

public section

namespace Purelib.Integration.Exponential.Program.Source

open Purelib.Approximation
open Purelib.Approximation.Gaussian.Exponential.Horner
open Purelib.Data.Nat.Schedule
open Purelib.Data.Rat
open Purelib.Integration.Exponential

/-- The actual common numerical observations of an original stage and exponential frontier. -/
@[expose] def numericalCommon {policy : Geometry.Policy} {schedule : PositiveStride} {extraDepth index : Nat}
    {stageRequest : AccuracyRequest} (stage : Result policy schedule extraDepth index stageRequest)
    (numerical : NumericalFrontier Real.source) (pointRequest : AccuracyRequest) :=
  NumericalFrontier.commonReadings (SourceFrontier.Numerical.frontier stage.sourceResult.frontier pointRequest)
    numerical pointRequest

/-- One original stage/common numerical query is paid by the actual point width and selected-depth radius. -/
theorem reading_bound (depth : Nat) {left : NumericalFrontier (fun point => BoundProcess.exact
    (Real.finiteSource depth point))} {right : NumericalFrontier Real.source} {request : AccuracyRequest}
    (reading : NumericalFrontier.CommonReading left right request) :
    reading.discrepancy ≤ request.tolerance + Real.tailRadius depth := by
  have lower : 0 ≤ reading.tag := reading.valid.1.trans reading.tag_inside.1
  have upper : reading.tag ≤ 1 := reading.tag_inside.2.trans reading.valid.2.2
  have leftInside := reading.left_inside.2
  rw [reading.left_point_eq] at leftInside
  rw [NumericalPoint.reading_eq] at leftInside
  change (Purelib.Data.Rat.Interval.exact (Real.finiteSource depth reading.tag)).Contains
    reading.leftReading at leftInside
  have leftEq := (Purelib.Data.Rat.Interval.exact_contains_iff _ _).mp leftInside
  let observed := reading.rightOrigin.retag reading.entry.child reading.tag
    reading.tag_inside.1 reading.tag_inside.2 request
  have rightInside := reading.right_inside.2
  rw [reading.right_point_eq] at rightInside
  change observed.reading.Contains reading.rightReading at rightInside
  rw [observed.reading_eq] at rightInside
  have width := reading.right_width_lt
  rw [reading.right_point_eq] at width
  rw [observed.reading_eq] at width
  change ((Real.source reading.tag).bound observed.state).width < request.tolerance at width
  have compared := Real.finite_numerical_difference depth reading.tag ⟨lower, upper⟩ observed.state
    reading.rightReading rightInside
  have paid := Fraction.Order.Arithmetic.add_le_add_direct width.le
    (Fraction.Order.Basic.le_refl (Real.tailRadius depth))
  change Fraction.abs (reading.leftReading - reading.rightReading) ≤ _
  rw [leftEq]
  exact compared.trans paid

/-- Any returned common readings pay for their exact finite-source and numerical observations. -/
theorem finite_numerical_pointBudget_le (depth : Nat)
    {left : NumericalFrontier (fun point => BoundProcess.exact (Real.finiteSource depth point))}
    {right : NumericalFrontier Real.source} {request : AccuracyRequest}
    (common : NumericalFrontier.CommonReadings left right request) :
    common.pointBudget ≤ request.tolerance + Real.tailRadius depth :=
  common.pointBudget_le_of_reading_bound _ (reading_bound depth)

/-- The actual common numerical point budget is paid by its request and the original selected depth. -/
theorem numerical_pointBudget_le {policy : Geometry.Policy} {schedule : PositiveStride} {extraDepth index : Nat}
    {stageRequest : AccuracyRequest} (stage : Result policy schedule extraDepth index stageRequest)
    (numerical : NumericalFrontier Real.source) (pointRequest : AccuracyRequest) :
    (numericalCommon stage numerical pointRequest).pointBudget ≤ pointRequest.tolerance +
      Real.tailRadius (Selection.selection policy schedule index).depth :=
  finite_numerical_pointBudget_le (Selection.selection policy schedule index).depth
    (numericalCommon stage numerical pointRequest)

/-- An actual finite-source frontier and numerical frontier are compared using their supplied common readings.

Both answers remain attached to their own original enclosures. The displayed
common value retains its returned point witnesses and their weighted budget. -/
theorem finite_numerical_answers_difference_le_from_common (depth : Nat)
    (left : SourceFrontier (Real.finiteSource depth)) (right : NumericalFrontier Real.source)
    (request : AccuracyRequest)
    (common : NumericalFrontier.CommonReadings (SourceFrontier.Numerical.frontier left request) right request)
    (leftAnswer rightAnswer : Fraction.Rational) (leftInside : (integralBound left.cells).Contains leftAnswer)
    (rightInside : (integralBound right.cells).Contains rightAnswer) :
    Fraction.abs (leftAnswer - rightAnswer) ≤
      (integralBound left.cells).width + (integralBound right.cells).width + common.pointBudget := by
  have inside : (integralBound (SourceFrontier.Numerical.frontier left request).cells).Contains leftAnswer := by
    rw [SourceFrontier.Numerical.integralBound_eq]
    exact leftInside
  have compared := common.answers_difference_le leftAnswer rightAnswer inside rightInside
  rw [SourceFrontier.Numerical.integralBound_eq] at compared
  exact compared

/-- The supplied common readings pay for the original stage sample and numerical answer.

The common value retains the exact finite-stage frontier, the actual numerical
frontier and its own returned point witnesses. This bound uses that supplied
value directly without constructing another common refinement. -/
theorem sample_answer_difference_le_from_common
    {policy : Geometry.Policy} {schedule : PositiveStride} {extraDepth index : Nat}
    {stageRequest : AccuracyRequest} (stage : Result policy schedule extraDepth index stageRequest)
    (numerical : NumericalFrontier Real.source) (answer : Fraction.Rational)
    (inside : (integralBound numerical.cells).Contains answer) (pointRequest : AccuracyRequest)
    (common : NumericalFrontier.CommonReadings
      (SourceFrontier.Numerical.frontier stage.sourceResult.frontier pointRequest) numerical pointRequest) :
    Fraction.abs (stage.stage.sample.re - answer) ≤
      (integralBound stage.sourceResult.frontier.cells).width + (integralBound numerical.cells).width +
        common.pointBudget :=
  finite_numerical_answers_difference_le_from_common _ stage.sourceResult.frontier numerical pointRequest common
    stage.stage.sample.re answer stage.sample_inside inside

/-- An original cached stage sample and a numerical exponential answer agree within their finite budgets.

The exact stage frontier and the original numerical frontier are compared on
their actual common child tags. The bound retains both original enclosure
widths, the actual numerical point request and the selected Taylor depth's
shrinking rational radius. -/
theorem sample_answer_difference_le {policy : Geometry.Policy} {schedule : PositiveStride} {extraDepth index : Nat}
    {stageRequest : AccuracyRequest} (stage : Result policy schedule extraDepth index stageRequest)
    (numerical : NumericalFrontier Real.source) (answer : Fraction.Rational)
    (inside : (integralBound numerical.cells).Contains answer) (pointRequest : AccuracyRequest) :
    Fraction.abs (stage.stage.sample.re - answer) ≤
      (integralBound stage.sourceResult.frontier.cells).width + (integralBound numerical.cells).width +
        (pointRequest.tolerance + Real.tailRadius (Selection.selection policy schedule index).depth) := by
  have compared := sample_answer_difference_le_from_common stage numerical answer inside pointRequest
    (numericalCommon stage numerical pointRequest)
  have paid := Fraction.Order.Arithmetic.add_le_add_direct
    (Fraction.Order.Basic.le_refl ((integralBound stage.sourceResult.frontier.cells).width +
      (integralBound numerical.cells).width)) (numerical_pointBudget_le stage numerical pointRequest)
  exact compared.trans paid

end Purelib.Integration.Exponential.Program.Source

end
