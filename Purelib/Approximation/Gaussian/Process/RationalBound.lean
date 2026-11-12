module

public import Purelib.Approximation.Gaussian.Process.OneSided
public import Purelib.Approximation.OneSided.BoundProcess
public import Purelib.Data.Rat.Interval.Bisection

/-!
# Gaussian observations of rational bound processes

The paired lower and upper views use the same original bound state. The
existing located-pair conversion supplies Gaussian balls and translates a
squared accuracy request into a finite rational width request.
-/

namespace Purelib.Approximation.Gaussian.Process.RationalBound

open Purelib.Approximation
open Purelib.Data.Gaussian
open Purelib.Data.Rat

/-- Pair the endpoints of each original rational bound without changing its state or request.

The fixed request in the one-sided endpoint views is only their individual
refinement operation. The paired request is the original arbitrary positive
width request, and both endpoints always retain the same original state. -/
@[expose] public def locatedPair (process : BoundProcess) :
    LocatedPair (process.lowerRequestProcess 1 (by decide))
      (process.upperRequestProcess 1 (by decide)) where
  State := process.State
  observation state := ⟨state, state, (process.bound state).valid⟩
  initial := process.initial
  request := process.request
  request_refines state epsilon positive :=
    ⟨(process.request_refines state epsilon positive).lower,
      (process.request_refines state epsilon positive).upper⟩
  accurate state epsilon positive := process.accurate state epsilon positive
  refinesInitial state :=
    ⟨(process.refinesInitial state).lower, (process.refinesInitial state).upper⟩

/-- Observe the original rational bound states as real-axis Gaussian balls.

Refinement calls the original bound process with the existing rational gap
selector. The witness is the midpoint of that same retained interval. This
conversion alone does not establish coherence between branches. -/
@[expose] public def toProcess (process : BoundProcess) : Gaussian.Process :=
  { OneSided.LocatedPair.toProcess (locatedPair process) with
    witness := fun state =>
      ⟨RationalEmbedding.realPoint (process.bound state).midpoint,
        ⟨(process.bound state).midpoint, (process.bound state).midpoint_contains, rfl⟩⟩ }

/-- A Gaussian bound observation uses the original rational interval at the same state. -/
public theorem ball_eq (process : BoundProcess) (state : process.State) :
    (toProcess process).ball state = Enclosure.Ball.RationalInterval.ballOfBound (process.bound state) := rfl

/-- The Gaussian witness is the midpoint of the same original retained interval. -/
public theorem witness_eq (process : BoundProcess) (state : process.State) :
    ((toProcess process).witness state).val = RationalEmbedding.realPoint (process.bound state).midpoint := rfl

/-- Gaussian refinement calls the original rational request with the selected finite gap. -/
public theorem refine_eq (process : BoundProcess) (state : process.State)
    (target : Fraction.Rational) (positive : 0 < target) :
    (toProcess process).refine state target positive =
      process.request state (Rational.Request.Square.gapTarget target)
        (Rational.Request.Square.gapTarget_pos positive) := rfl

end Purelib.Approximation.Gaussian.Process.RationalBound
