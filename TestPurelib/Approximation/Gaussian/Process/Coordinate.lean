module
import Purelib.Approximation.Gaussian.Process.Coordinate
import Purelib.Approximation.Gaussian.Process.Coordinate.Observation
import Purelib.Approximation.Gaussian.Sequence.Process
import Purelib.Approximation.Gaussian.Exponential.Horner.Sequence
import Purelib.Data.Gaussian.Norm.Basic

/-! Coordinate projections retain original Gaussian process states and finite witnesses. -/

namespace TestPurelib.Approximation.Gaussian.Process.Coordinate

open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Process.Coordinate
open Purelib.Data.Gaussian
open Purelib.Data.Rat

/-- An exact Gaussian source with two different rational coordinates. -/
private def point : Basic.Canonical := ⟨2, 3⟩

/-- Its original Gaussian process and two rational coordinate projections. -/
private def source : Process := Process.exact point
private instance : DecidableEq source.State := Process.exactStateDecidableEq point
private def real := Purelib.Approximation.Gaussian.Process.Coordinate.real source ()
private def imaginary := Purelib.Approximation.Gaussian.Process.Coordinate.imaginary source ()

/-- Continue each projection with two distinct positive requests. -/
private def realFirst := real.request real.initial 4 (by decide)
private def realLater := real.request realFirst 2 (by decide)
private def imaginaryFirst := imaginary.request imaginary.initial 4 (by decide)

/-- A paired observation continues both coordinates through the same nonreal Gaussian process. -/
private def paired := Purelib.Approximation.Gaussian.Process.Coordinate.Paired.initial source ()
private def pairedLater := paired.request 2 (by decide) 1 (by decide)

/-- The actual paired request observed at its two refinement and ball boundaries. -/
private def pairedObservation := Observation.computation paired 2 (by decide) 1 (by decide)

/-- Continue only the saved imaginary coordinate at the original nonreal Gaussian state. -/
private def imaginaryOnlyLater := pairedLater.requestImaginary (1 / 2) (by decide)
private def imaginaryOnlyObservation := Observation.imaginaryOnly pairedLater (1 / 2) (by decide)

/-- Pair an already retained real state by observing the original Gaussian origin ball. -/
private def fromRealObservation := Observation.fromReal realLater

/-- A ball reply returned where the first refinement was requested. -/
private def wrongReply (_ : Observation.Request source.State) : Observation.Reply source :=
  Observation.original source (.ball ())

/-- A refinement reply returned where the original ball was requested. -/
private def wrongOriginReply (_ : Observation.Request source.State) : Observation.Reply source :=
  Observation.original source (.refine () 1 (by decide))

example : (pairedObservation.protocol.run (Observation.original source)).value = .ok pairedLater :=
  Observation.computation_original paired 2 (by decide) 1 (by decide)

example : (pairedObservation.protocol.run (Observation.original source)).trace.length = 4 :=
  Observation.computation_original_count paired 2 (by decide) 1 (by decide)

example : pairedObservation.protocol.replayExact (pairedObservation.protocol.run (Observation.original source)).trace =
    .ok (.ok pairedLater) := Observation.computation_replay paired 2 (by decide) 1 (by decide)

example : (match (pairedObservation.protocol.run wrongReply).value with
    | .error invalid => match invalid.requested with
      | .refine _ _ _ => true
      | .ball _ => false
    | .ok _ => false) = true := by decide +kernel

example : (pairedObservation.protocol.run wrongReply).trace.length = 1 := by decide +kernel

example : imaginaryOnlyLater.real = pairedLater.real := pairedLater.requestImaginary_real (1 / 2) (by decide)

example : imaginaryOnlyLater.imaginary.interval.width < 1 / 2 :=
  pairedLater.requestImaginary_accurate (1 / 2) (by decide)

example : imaginaryOnlyLater.real.interval.Contains point.re ∧
    imaginaryOnlyLater.imaginary.interval.Contains point.im :=
  imaginaryOnlyLater.admits point rfl

example : (imaginaryOnlyObservation.protocol.run (Observation.original source)).value =
    .ok ⟨imaginaryOnlyLater, rfl⟩ := Observation.imaginaryOnly_original pairedLater (1 / 2) (by decide)

example : (imaginaryOnlyObservation.protocol.run (Observation.original source)).trace.length = 2 := by
  exact (congrArg List.length (Observation.imaginaryOnly_trace pairedLater (1 / 2) (by decide))).trans rfl

example : imaginaryOnlyObservation.protocol.replayExact
    (imaginaryOnlyObservation.protocol.run (Observation.original source)).trace = .ok (.ok ⟨imaginaryOnlyLater, rfl⟩) :=
  Observation.imaginaryOnly_replay pairedLater (1 / 2) (by decide)

example : (match (imaginaryOnlyObservation.protocol.run wrongReply).value with
    | .error invalid => match invalid.requested with
      | .refine _ _ _ => true
      | .ball _ => false
    | .ok _ => false) = true := by decide +kernel

example : (imaginaryOnlyObservation.protocol.run wrongReply).trace.length = 1 := by decide +kernel

/-- Retain the exact origin ball used to construct the paired coordinate. -/
private def cachedFromRealObservation := Observation.fromRealCached realLater

example : (cachedFromRealObservation.protocol.run (Observation.original source)).value =
    .ok ⟨⟨source.ball (), rfl⟩, ⟨Paired.fromReal realLater, rfl⟩⟩ :=
  Observation.fromRealCached_original realLater

example : (cachedFromRealObservation.protocol.run (Observation.original source)).trace.length = 1 := by
  exact (congrArg List.length (Observation.fromRealCached_trace realLater (Observation.original source))).trans rfl

example : cachedFromRealObservation.protocol.replayExact
    (cachedFromRealObservation.protocol.run (Observation.original source)).trace =
      .ok (.ok ⟨⟨source.ball (), rfl⟩, ⟨Paired.fromReal realLater, rfl⟩⟩) :=
  Observation.fromRealCached_replay realLater

example : (fromRealObservation.protocol.run (Observation.original source)).value =
    .ok ⟨Paired.fromReal realLater, rfl⟩ := Observation.fromReal_original realLater

example : (fromRealObservation.protocol.run (Observation.original source)).trace.length = 1 := by
  exact (congrArg List.length (Observation.fromReal_trace realLater (Observation.original source))).trans rfl

example : fromRealObservation.protocol.replayExact
    (fromRealObservation.protocol.run (Observation.original source)).trace =
      .ok (.ok ⟨Paired.fromReal realLater, rfl⟩) :=
  Observation.fromReal_replay realLater

example : (match (fromRealObservation.protocol.run wrongOriginReply).value with
    | .error invalid => match invalid.requested with
      | .ball _ => true
      | .refine _ _ _ => false
    | .ok _ => false) = true := by decide +kernel

example : (fromRealObservation.protocol.run wrongOriginReply).trace.length = 1 := by decide +kernel

example : pairedLater.real.interval.Contains point.re ∧ pairedLater.imaginary.interval.Contains point.im :=
  pairedLater.admits point rfl

example : Norm.Basic.normSq (point - pairedLater.midpoint) ≤
    (pairedLater.real.interval.width * (1 / 2)) ^ 2 +
      (pairedLater.imaginary.interval.width * (1 / 2)) ^ 2 :=
  pairedLater.normSq_sub_midpoint_le point rfl

example : pairedLater.real.interval.width < 2 ∧ pairedLater.imaginary.interval.width < 1 :=
  ⟨paired.request_real_accurate 2 (by decide) 1 (by decide),
    paired.request_imaginary_accurate 2 (by decide) 1 (by decide)⟩

example : (real.bound realLater).Contains 2 := by
  exact realLater.admits point rfl

example : (imaginary.bound imaginaryFirst).Contains 3 := by
  exact imaginaryFirst.admits point rfl

example : (real.bound realLater).Refines (real.bound realFirst) :=
  real.request_refines realFirst 2 (by decide)

example : (real.bound realLater).width < 2 :=
  real.accurate realFirst 2 (by decide)

example : (real.bound realLater).lower = 3 / 2 ∧ (real.bound realLater).upper = 5 / 2 := by
  constructor <;> decide

/-- The original finite exponential approximation at zero input. -/
private def exponential := Exponential.Horner.Sequence.approximation 0 (by
  rw [Norm.Basic.normSq_zero]
  decide)

/-- Its original Gaussian process and a real-coordinate request. -/
private def exponentialSource := exponential.toProcess
private instance : DecidableEq exponentialSource.State := Sequence.ApproximationData.stateDecidableEq exponential
private def exponentialReal := Purelib.Approximation.Gaussian.Process.Coordinate.real exponentialSource (0 : Nat)
private def exponentialState := exponentialReal.request exponentialReal.initial 4 (by decide)

/-- Pair the actual retained exponential real state with its original Gaussian imaginary coordinate. -/
private def exponentialPaired :=
  Purelib.Approximation.Gaussian.Process.Coordinate.Paired.fromReal exponentialState

/-- Observe two requests continuing the original retained exponential Gaussian state. -/
private def exponentialObservation := Observation.computation exponentialPaired 4 (by decide) 2 (by decide)

example : (exponentialObservation.protocol.run (Observation.original exponentialSource)).value =
    .ok (exponentialPaired.request 4 (by decide) 2 (by decide)) :=
  Observation.computation_original exponentialPaired 4 (by decide) 2 (by decide)

example : (exponentialObservation.protocol.run (Observation.original exponentialSource)).trace.length = 4 :=
  Observation.computation_original_count exponentialPaired 4 (by decide) 2 (by decide)

example : exponentialPaired.real.interval.Contains (exponential.sample exponentialPaired.current).re ∧
    exponentialPaired.imaginary.interval.Contains (exponential.sample exponentialPaired.current).im :=
  exponentialPaired.admits (exponential.sample exponentialPaired.current)
    (exponential.sample_possible exponentialPaired.current)

example : (exponentialReal.bound exponentialState).Contains 1 := by
  have present := exponentialState.admits (exponential.sample exponentialState.current)
    (exponential.sample_possible exponentialState.current)
  change (exponentialReal.bound exponentialState).Contains
    (Exponential.Horner.Sample.sample 0 exponentialState.current).re at present
  rw [Exponential.Horner.Sample.sample_zero] at present
  exact present

example : (exponentialReal.bound exponentialState).width < 4 :=
  exponentialReal.accurate exponentialReal.initial 4 (by decide)

end TestPurelib.Approximation.Gaussian.Process.Coordinate
