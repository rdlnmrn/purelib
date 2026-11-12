module

public import Purelib.Integration.Exponential.Real.Observation
public import Purelib.Approximation.Gaussian.Exponential.Horner.Real.Comparison
import Purelib.Approximation.Gaussian.Exponential.Horner.Real.Numerical
import Purelib.Data.Rat.Interval.Bisection
import Purelib.Data.Nat.Order
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Paired Gaussian observations of retained exponential points

Each paired point retains its original numerical observation and its original
Gaussian origin ball. Imaginary continuation preserves the actual real state.
-/

public section

namespace Purelib.Integration.Exponential.Real.Paired

open Purelib.Approximation
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Exponential
open Purelib.Approximation.Gaussian.Process
open Purelib.Computation.Query
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Integration.Exponential.Real.Observation

/-- The rational unit tag belonging to the original numerical point. -/
abbrev tag (point : NumericalPoint Horner.Real.source) (unit : 0 ≤ point.point ∧ point.point ≤ 1) : Point :=
  ⟨point.point, unit⟩

set_option genInjectivity false in
/-- A paired observation retaining an actual exponential numerical point and origin ball.

The paired real state is exactly the original point's returned state, transported
to its Gaussian source. The ball is the original response at that source's origin. -/
structure PointState (point : NumericalPoint Horner.Real.source) (unit : 0 ≤ point.point ∧ point.point ≤ 1) where
  /-- The certified original Gaussian ball at the source origin. -/
  originBall : Coordinate.Observation.Response (process (tag point unit)) (.ball (0 : Nat))
  /-- The retained real and imaginary observations of the same original source. -/
  paired : Coordinate.Paired (process (tag point unit)) (0 : Nat)
  /-- The retained real coordinate is the original numerical point's actual state. -/
  real_eq : paired.real = Horner.Real.originalState point.point unit point.state

constructive_injectivity PointState

/-- Assemble a paired point from the actual cached origin-ball response. -/
@[expose] def fromCached (point : NumericalPoint Horner.Real.source) (unit : 0 ≤ point.point ∧ point.point ≤ 1)
    (cached : Coordinate.Observation.CachedFromReal (Horner.Real.originalState point.point unit point.state)) :
    PointState point unit := by
  refine ⟨cached.1, cached.2.val, ?_⟩
  rw [cached.2.property]
  exact Coordinate.Paired.fromRealWith_real _ _ _

/-- Observe the original origin ball and attach its actual reply to the retained numerical point. -/
@[expose] def attach (point : NumericalPoint Horner.Real.source) (unit : 0 ≤ point.point ∧ point.point ≤ 1) :
    Program Query Reply (Except Failure (PointState point unit)) :=
  (Coordinate.Observation.fromRealCached (Horner.Real.originalState point.point unit point.state)).substituteChecked
    (pointHandler (tag point unit)) |>.map fun result =>
      match result with
      | .error invalid => .error invalid
      | .ok execution =>
          match execution.value with
          | .error invalid => .error (.operation (tag point unit) invalid)
          | .ok cached => .ok (fromCached point unit cached)

/-- Retain a continued imaginary coordinate and the same actual real state and origin ball. -/
@[expose] def withImaginary (point : NumericalPoint Horner.Real.source) (unit : 0 ≤ point.point ∧ point.point ≤ 1)
    (saved : PointState point unit) (request : AccuracyRequest)
    (next : Coordinate.Observation.CertifiedImaginary saved.paired request.tolerance request.positive) :
    PointState point unit := by
  refine ⟨saved.originBall, next.val, ?_⟩
  rw [next.property, Coordinate.Paired.requestImaginary_real]
  exact saved.real_eq

/-- Continue only the imaginary coordinate when its retained interval is too wide.

An adequate saved pair returns without any Gaussian request. Otherwise the
original saved paired state supplies the next imaginary refinement. -/
@[expose] def requestImaginary (point : NumericalPoint Horner.Real.source) (unit : 0 ≤ point.point ∧ point.point ≤ 1)
    (saved : PointState point unit) (request : AccuracyRequest) :
    Program Query Reply (Except Failure (PointState point unit)) :=
  if saved.paired.imaginary.interval.width < request.tolerance then .pure (.ok saved)
  else
    (Coordinate.Observation.imaginaryOnly saved.paired request.tolerance request.positive).substituteChecked
      (pointHandler (tag point unit)) |>.map fun result =>
        match result with
        | .error invalid => .error invalid
        | .ok execution =>
            match execution.value with
            | .error invalid => .error (.operation (tag point unit) invalid)
            | .ok next => .ok (withImaginary point unit saved request next)

/-- An adequate retained imaginary interval causes no Gaussian calls. -/
theorem requestImaginary_reused (point : NumericalPoint Horner.Real.source) (unit : 0 ≤ point.point ∧ point.point ≤ 1)
    (saved : PointState point unit) (request : AccuracyRequest)
    (adequate : saved.paired.imaginary.interval.width < request.tolerance) (oracle : Query → Reply) :
    ((requestImaginary point unit saved request).protocol.run oracle).value = .ok saved ∧
      ((requestImaginary point unit saved request).protocol.run oracle).trace = [] := by
  unfold requestImaginary
  rw [if_pos adequate]
  exact ⟨rfl, rfl⟩

/-- The paired intervals admit one common Gaussian sample from their original source. -/
theorem admits (point : NumericalPoint Horner.Real.source) (unit : 0 ≤ point.point ∧ point.point ≤ 1)
    (saved : PointState point unit) :
    saved.paired.real.interval.Contains
        ((Horner.Real.approximation point.point unit).sample saved.paired.current).re ∧
      saved.paired.imaginary.interval.Contains
        ((Horner.Real.approximation point.point unit).sample saved.paired.current).im :=
  saved.paired.admits ((Horner.Real.approximation point.point unit).sample saved.paired.current)
    ((Horner.Real.approximation point.point unit).sample_possible saved.paired.current)

/-- The retained paired real interval is the actual numerical point's cached reading. -/
theorem real_reading (point : NumericalPoint Horner.Real.source) (unit : 0 ≤ point.point ∧ point.point ≤ 1)
    (saved : PointState point unit) : saved.paired.real.interval = point.reading := by
  rw [saved.real_eq, point.reading_eq]
  exact (Horner.Real.originalState_bound point.point unit point.state).symm

/-- The retained paired midpoint has a squared error bound against the same original Gaussian sample. -/
theorem sample_midpoint_bound (point : NumericalPoint Horner.Real.source)
    (unit : 0 ≤ point.point ∧ point.point ≤ 1) (saved : PointState point unit) :
    Norm.Basic.normSq ((Horner.Real.approximation point.point unit).sample saved.paired.current -
      saved.paired.midpoint) ≤
        (saved.paired.real.interval.width * (1 / 2)) ^ 2 +
          (saved.paired.imaginary.interval.width * (1 / 2)) ^ 2 :=
  saved.paired.normSq_sub_midpoint_le
    ((Horner.Real.approximation point.point unit).sample saved.paired.current)
    ((Horner.Real.approximation point.point unit).sample_possible saved.paired.current)

/-- Transport the first retained pair along an explicitly supplied equality of original rational tags. -/
@[expose] def transportPair (left right : NumericalPoint Horner.Real.source)
    (leftUnit : 0 ≤ left.point ∧ left.point ≤ 1) (rightUnit : 0 ≤ right.point ∧ right.point ≤ 1)
    (first : PointState left leftUnit) (same : tag left leftUnit = tag right rightUnit) :
    Coordinate.Paired (process (tag right rightUnit)) (0 : Nat) :=
  same ▸ first.paired

/-- Independent retained point pairs at the same tag admit one common later sample and a squared-norm bound. -/
theorem independent_midpoints_normSq_le (left right : NumericalPoint Horner.Real.source)
    (leftUnit : 0 ≤ left.point ∧ left.point ≤ 1) (rightUnit : 0 ≤ right.point ∧ right.point ≤ 1)
    (first : PointState left leftUnit) (second : PointState right rightUnit)
    (same : tag left leftUnit = tag right rightUnit) :
    let transported := transportPair left right leftUnit rightUnit first same
    Norm.Basic.normSq (transported.midpoint - second.paired.midpoint) ≤
      (transported.real.interval.width + second.paired.real.interval.width) ^ 2 +
        (transported.imaginary.interval.width + second.paired.imaginary.interval.width) ^ 2 := by
  let transported := transportPair left right leftUnit rightUnit first same
  let depth := max (show Nat from transported.current) (show Nat from second.paired.current)
  let value := (Horner.Real.approximation right.point rightUnit).sample depth
  have firstPossible : (Horner.Real.approximation right.point rightUnit).toProcess.Possible transported.current value :=
    ⟨depth, Purelib.Data.Nat.Order.le_max_left _ _, rfl⟩
  have secondPossible :
      (Horner.Real.approximation right.point rightUnit).toProcess.Possible second.paired.current value :=
    ⟨depth, Purelib.Data.Nat.Order.le_max_right _ _, rfl⟩
  exact Coordinate.Paired.midpoints_normSq_le transported second.paired value firstPossible secondPossible

/-- The original origin-ball reply constructs this exact retained pair. -/
@[expose] def originalAttached (point : NumericalPoint Horner.Real.source) (unit : 0 ≤ point.point ∧ point.point ≤ 1) :
    PointState point unit :=
  fromCached point unit ⟨⟨(process (tag point unit)).ball (0 : Nat), rfl⟩,
    ⟨Coordinate.Paired.fromReal (Horner.Real.originalState point.point unit point.state), rfl⟩⟩

/-- Original Gaussian replies attach the exact origin ball and original real state. -/
theorem attach_original (point : NumericalPoint Horner.Real.source) (unit : 0 ≤ point.point ∧ point.point ≤ 1) :
    ((attach point unit).protocol.run original).value = .ok (originalAttached point unit) := by
  unfold attach
  rw [Program.map_execution, Protocol.map_run_value]
  have returned := Program.substituteChecked_value
    (pointHandler (tag point unit))
    (Coordinate.Observation.fromRealCached (Horner.Real.originalState point.point unit point.state))
    original (Coordinate.Observation.original (process (tag point unit)))
    (pointHandler_original (tag point unit))
  rw [returned]
  dsimp only
  let assemble (outcome : Except (Coordinate.Observation.Invalid (process (tag point unit)).State)
      (Coordinate.Observation.CachedFromReal (Horner.Real.originalState point.point unit point.state))) :
      Except Failure (PointState point unit) :=
    match outcome with
    | .error invalid => .error (.operation (tag point unit) invalid)
    | .ok cached => .ok (fromCached point unit cached)
  change assemble (((Coordinate.Observation.fromRealCached
      (Horner.Real.originalState point.point unit point.state)).protocol.run
        (Coordinate.Observation.original (process (tag point unit)))).value) =
    assemble (.ok ⟨⟨(process (tag point unit)).ball (0 : Nat), rfl⟩,
      ⟨Coordinate.Paired.fromReal (Horner.Real.originalState point.point unit point.state), rfl⟩⟩)
  exact congrArg assemble (Coordinate.Observation.fromRealCached_original
    (Horner.Real.originalState point.point unit point.state))

/-- The pair obtained by continuing only the original saved imaginary coordinate. -/
@[expose] def requestedState (point : NumericalPoint Horner.Real.source) (unit : 0 ≤ point.point ∧ point.point ≤ 1)
    (saved : PointState point unit) (request : AccuracyRequest) : PointState point unit :=
  withImaginary point unit saved request ⟨saved.paired.requestImaginary request.tolerance request.positive, rfl⟩

/-- Original Gaussian replies either reuse the adequate pair or return its exact imaginary continuation. -/
theorem requestImaginary_original (point : NumericalPoint Horner.Real.source)
    (unit : 0 ≤ point.point ∧ point.point ≤ 1) (saved : PointState point unit) (request : AccuracyRequest) :
    ((requestImaginary point unit saved request).protocol.run original).value =
      .ok (if saved.paired.imaginary.interval.width < request.tolerance then saved
        else requestedState point unit saved request) := by
  unfold requestImaginary
  by_cases adequate : saved.paired.imaginary.interval.width < request.tolerance
  · rw [if_pos adequate, if_pos adequate]
    rfl
  · rw [if_neg adequate, if_neg adequate]
    rw [Program.map_execution, Protocol.map_run_value]
    have returned := Program.substituteChecked_value
      (pointHandler (tag point unit))
      (Coordinate.Observation.imaginaryOnly saved.paired request.tolerance request.positive)
      original (Coordinate.Observation.original (process (tag point unit)))
      (pointHandler_original (tag point unit))
    rw [returned]
    dsimp only
    let assemble (outcome : Except (Coordinate.Observation.Invalid (process (tag point unit)).State)
        (Coordinate.Observation.CertifiedImaginary saved.paired request.tolerance request.positive)) :
        Except Failure (PointState point unit) :=
      match outcome with
      | .error invalid => .error (.operation (tag point unit) invalid)
      | .ok next => .ok (withImaginary point unit saved request next)
    change assemble
      (((Coordinate.Observation.imaginaryOnly saved.paired request.tolerance request.positive).protocol.run
        (Coordinate.Observation.original (process (tag point unit)))).value) =
      assemble (.ok ⟨saved.paired.requestImaginary request.tolerance request.positive, rfl⟩)
    exact congrArg assemble (Coordinate.Observation.imaginaryOnly_original saved.paired
      request.tolerance request.positive)

/-- Original Gaussian execution meets the requested imaginary width. -/
theorem requestImaginary_original_accurate (point : NumericalPoint Horner.Real.source)
    (unit : 0 ≤ point.point ∧ point.point ≤ 1) (saved : PointState point unit) (request : AccuracyRequest) :
    ∃ next, ((requestImaginary point unit saved request).protocol.run original).value = .ok next ∧
      next.paired.imaginary.interval.width < request.tolerance := by
  by_cases adequate : saved.paired.imaginary.interval.width < request.tolerance
  · refine ⟨saved, ?_, adequate⟩
    rw [requestImaginary_original, if_pos adequate]
  · refine ⟨requestedState point unit saved request, ?_, ?_⟩
    · rw [requestImaginary_original, if_neg adequate]
    · exact saved.paired.requestImaginary_accurate request.tolerance request.positive

/-- A finite Taylor reading and the paired real midpoint use the actual point width and tail radius. -/
private theorem finiteSample_real_bound (point : NumericalPoint Horner.Real.source)
    (unit : 0 ≤ point.point ∧ point.point ≤ 1) (saved : PointState point unit) (depth : Nat) :
    Fraction.abs ((Horner.Sample.sample (RationalEmbedding.realPoint point.point) depth).re -
      saved.paired.midpoint.re) ≤ saved.paired.real.interval.width + Horner.Real.tailRadius depth := by
  have sameBound : saved.paired.real.interval = (Horner.Real.source point.point).bound point.state :=
    (real_reading point unit saved).trans point.reading_eq
  have realInside : ((Horner.Real.source point.point).bound point.state).Contains
      saved.paired.real.interval.midpoint := by
    rw [← sameBound]
    exact saved.paired.real.interval.midpoint_contains
  have comparison := Horner.Real.finite_numerical_difference depth point.point unit point.state
    saved.paired.real.interval.midpoint realInside
  have widthEq := congrArg (fun interval : Purelib.Data.Rat.Interval => interval.width) sameBound
  change Fraction.abs (Horner.Real.finiteSource depth point.point - saved.paired.real.interval.midpoint) ≤ _
  rw [widthEq]
  exact comparison

/-- A finite real-input Taylor sample and the paired imaginary midpoint use the actual imaginary half-width. -/
private theorem finiteSample_imaginary_bound (point : NumericalPoint Horner.Real.source)
    (unit : 0 ≤ point.point ∧ point.point ≤ 1) (saved : PointState point unit) (depth : Nat) :
    Fraction.abs ((Horner.Sample.sample (RationalEmbedding.realPoint point.point) depth).im -
      saved.paired.midpoint.im) ≤ saved.paired.imaginary.interval.width * (1 / 2) := by
  have observed := (admits point unit saved).2
  have laterZero := Horner.Sample.sample_im_zero (RationalEmbedding.realPoint point.point)
    (RationalEmbedding.realPoint_im point.point) (show Nat from saved.paired.current)
  change saved.paired.imaginary.interval.Contains
    (Horner.Sample.sample (RationalEmbedding.realPoint point.point) (show Nat from saved.paired.current)).im at observed
  rw [laterZero] at observed
  have imaginaryBound := Purelib.Data.Rat.Interval.abs_sub_midpoint_le observed
  have depthZero := Horner.Sample.sample_im_zero (RationalEmbedding.realPoint point.point)
    (RationalEmbedding.realPoint_im point.point) depth
  change Fraction.abs ((Horner.Sample.sample (RationalEmbedding.realPoint point.point) depth).im -
    saved.paired.imaginary.interval.midpoint) ≤ _
  rw [depthZero]
  exact imaginaryBound

/-- Compare a finite Taylor sample with the midpoint of an actual paired numerical point.

The real budget uses the retained numerical interval width and the finite
Taylor depth's tail radius. The imaginary budget is the retained imaginary
half-width, using the same original real-input Gaussian process. -/
theorem finiteSample_midpoint_normSq_le (point : NumericalPoint Horner.Real.source)
    (unit : 0 ≤ point.point ∧ point.point ≤ 1) (saved : PointState point unit) (depth : Nat) :
    Norm.Basic.normSq
        (Horner.Sample.sample (RationalEmbedding.realPoint point.point) depth - saved.paired.midpoint) ≤
      (saved.paired.real.interval.width + Horner.Real.tailRadius depth) ^ 2 +
        (saved.paired.imaginary.interval.width * (1 / 2)) ^ 2 :=
  Norm.Coordinates.sub_normSq_le
    (Horner.Sample.sample (RationalEmbedding.realPoint point.point) depth) saved.paired.midpoint
    (saved.paired.real.interval.width + Horner.Real.tailRadius depth)
    (saved.paired.imaginary.interval.width * (1 / 2))
    (finiteSample_real_bound point unit saved depth) (finiteSample_imaginary_bound point unit saved depth)

end Purelib.Integration.Exponential.Real.Paired

end
