module

import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Interval.Basic

public import Purelib.Approximation.Bound.Process
public import Purelib.Approximation.OneSided.Basic
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Rat.Fraction.Order
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib

open Purelib.Data

open Purelib.Data.Rat

@[expose] public section

/-!
# One-sided rational refinement processes

These processes expose improving rational evidence without postulating a
hidden endpoint.  A lower process only promises increasing lower bounds, and
an upper process only promises decreasing upper bounds.  In particular,
neither structure contains an accuracy request or a convergence claim.

A `LocatedPair` is deliberately stronger: it supplies a finite request which
puts one lower observation and one upper observation within an explicitly
requested positive rational gap.  Only at that boundary do the observations
become an ordinary two-sided `BoundProcess`.
-/

namespace Purelib.Approximation
namespace LowerProcess
namespace Refines
end Refines
end LowerProcess

namespace UpperProcess
namespace Refines
end Refines
end UpperProcess

/-! ## One-sided views of a fixed rational-bound request -/

namespace BoundProcess
end BoundProcess

/-! ## Pairing one-sided observations -/

set_option genInjectivity false in
/-- One compatible lower/upper observation at explicitly displayed states. -/
structure PairedObservation (lower : Approximation.LowerProcess) (upper :
  Approximation.UpperProcess) where
  /-- The original lower-process state retained by this paired observation. -/ lowerState : lower.State
  /-- The original upper-process state retained by this paired observation. -/ upperState : upper.State
  /-- The displayed lower bound does not exceed the displayed upper bound. -/ ordered : lower.bound lowerState ≤
    upper.bound upperState

constructive_injectivity PairedObservation

namespace PairedObservation

/-- The rational gap displayed by a paired observation. -/
def gap {lower : Approximation.LowerProcess} {upper :
  Approximation.UpperProcess}
    (observation : Approximation.PairedObservation lower upper) : Fraction.Rational :=
  upper.bound observation.upperState - lower.bound observation.lowerState

/-- The rational gap of a compatible paired observation is nonnegative. -/
theorem gap_nonnegative {lower : Approximation.LowerProcess} {upper :
  Approximation.UpperProcess}
    (observation : Approximation.PairedObservation lower upper) : 0 ≤ observation.gap :=
  Fraction.Order.Arithmetic.sub_nonneg_direct observation.ordered

/-- Forget the origins of the endpoints and retain an ordinary rational enclosure. -/
def bound {lower : Approximation.LowerProcess} {upper :
  Approximation.UpperProcess}
    (observation : Approximation.PairedObservation lower upper) : Rat.Interval where
  lower := lower.bound observation.lowerState
  upper := upper.bound observation.upperState
  valid := observation.ordered

/-- The enclosure width equals the paired observation's retained gap. -/
@[simp] theorem bound_width {lower : Approximation.LowerProcess} {upper :
  Approximation.UpperProcess}
    (observation : Approximation.PairedObservation lower upper) :
    observation.bound.width = observation.gap :=
  rfl

/-- A paired observation refines another when its lower endpoint rises and its upper endpoint falls. -/
structure Refines {lower : Approximation.LowerProcess} {upper :
  Approximation.UpperProcess}
    (inner outer : Approximation.PairedObservation lower upper) : Prop where
  /-- The inner lower bound is at least the outer lower bound. -/ lower : lower.bound outer.lowerState ≤ lower.bound
    inner.lowerState
  /-- The inner upper bound is at most the outer upper bound. -/ upper : upper.bound inner.upperState ≤ upper.bound
    outer.upperState

namespace Refines

/-- Every paired observation refines itself. -/
theorem refl {lower : Approximation.LowerProcess} {upper :
  Approximation.UpperProcess}
    (observation : Approximation.PairedObservation lower upper) :
    Approximation.PairedObservation.Refines observation observation :=
  ⟨le_rfl, le_rfl⟩

/-- Compose two paired-observation refinements. -/
theorem trans {lower : Approximation.LowerProcess} {upper :
  Approximation.UpperProcess}
    {inner middle outer : Approximation.PairedObservation lower upper}
    (innerMiddle : Approximation.PairedObservation.Refines inner middle)
    (middleOuter : Approximation.PairedObservation.Refines middle outer) : Approximation.PairedObservation.Refines inner
      outer :=
  ⟨middleOuter.lower.trans innerMiddle.lower,
    innerMiddle.upper.trans middleOuter.upper⟩

/-- Refinement of paired observations induces refinement of their rational enclosures. -/
theorem bound {lower : Approximation.LowerProcess} {upper :
  Approximation.UpperProcess}
    {inner outer : Approximation.PairedObservation lower upper}
    (refines : Approximation.PairedObservation.Refines inner outer) :
    Interval.Refines inner.bound outer.bound :=
  ⟨refines.lower, refines.upper⟩

end Refines

end PairedObservation

set_option genInjectivity false in
/-- A lower/upper pair equipped with an executable finite gap modulus. This extra request data, not one-sided
monotonicity alone, licenses conversion to a located two-sided process. -/
structure LocatedPair (lower : Approximation.LowerProcess) (upper :
  Approximation.UpperProcess) where
  /-- The retained state type of the joint gap-refinement process. -/ State : Type
  /-- The compatible lower/upper observation displayed at each retained state. -/ observation : State →
    PairedObservation lower upper
  /-- The distinguished initial paired state. -/ initial : State
  /-- Refine a paired state to meet a positive rational gap request. -/ request : (state : State) → (epsilon :
    Fraction.Rational) → 0 < epsilon → State
  /-- A request refines the original lower and upper observations. -/ request_refines : ∀ state epsilon positive,
    PairedObservation.Refines
      (observation (request state epsilon positive)) (observation state)
  /-- The requested paired observation has gap strictly below the supplied tolerance. -/ accurate : ∀ state epsilon
    positive,
    (observation (request state epsilon positive)).gap < epsilon
  /-- Every paired observation refines the initial paired observation. -/ refinesInitial : ∀ state,
    PairedObservation.Refines (observation state) (observation initial)

constructive_injectivity LocatedPair

namespace LocatedPair

/-- Convert an explicitly gap-controlled one-sided pair to the ordinary finite rational enclosure protocol. -/
def toBoundProcess {lower : Approximation.LowerProcess} {upper :
  Approximation.UpperProcess}
    (pair : Approximation.LocatedPair lower upper) : Approximation.BoundProcess where
  State := pair.State
  bound state := (pair.observation state).bound
  initial := pair.initial
  request := pair.request
  request_refines state epsilon positive :=
    (pair.request_refines state epsilon positive).bound
  accurate state epsilon positive := by
    rw [Approximation.PairedObservation.bound_width]
    exact pair.accurate state epsilon positive
  refinesInitial state := (pair.refinesInitial state).bound

/-- A gap request can only increase the displayed lower bound. -/
theorem request_lower_mono {lower : Approximation.LowerProcess} {upper :
  Approximation.UpperProcess}
    (pair : Approximation.LocatedPair lower upper) (state : pair.State)
    (epsilon : Fraction.Rational) (positive : 0 < epsilon) :
    lower.bound (pair.observation state).lowerState ≤
      lower.bound
        (pair.observation (pair.request state epsilon positive)).lowerState :=
  (pair.request_refines state epsilon positive).lower

/-- A gap request can only decrease the displayed upper bound. -/
theorem request_upper_antitone {lower : Approximation.LowerProcess} {upper :
  Approximation.UpperProcess}
    (pair : Approximation.LocatedPair lower upper) (state : pair.State)
    (epsilon : Fraction.Rational) (positive : 0 < epsilon) :
    upper.bound
        (pair.observation (pair.request state epsilon positive)).upperState ≤
      upper.bound (pair.observation state).upperState :=
  (pair.request_refines state epsilon positive).upper

end LocatedPair

end Purelib.Approximation

end
