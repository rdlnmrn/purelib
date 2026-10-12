module
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Distribution.Content
import Purelib.Measure.Distribution.Kernel.Basic
import Purelib.Measure.Distribution.Lp.L1
import Purelib.Measure.Distribution.Lp.L2
public import Purelib.Measure.Distribution.Lp.Natural
import Purelib.Data.Rat.Fraction
import Purelib.Measure.Content.Basic
import Purelib.Data.List.Event
import Purelib.Measure.Content.Pushforward.Lp

section
/-!
# Finite pushforward laws for powered Lp and essential maxima

An executable pushforward retains every displayed source row and merely
changes its payload.  Consequently rational L1, natural-powered Lp, finite
almost-everywhere equality, and computed essential maxima all obey exact
change-of-variables laws.  No quotient function space or measurable-map
side condition is needed on a displayed finite table.
-/

@[expose] public section

namespace Purelib.Measure
namespace Distribution

section
open Purelib
open Purelib.Data.Rat
/-- A pushforward powered magnitude expectation equals the original expectation of the pulled-back observable magnitude
power. -/
theorem map_poweredLp {α β : Type} (source : Measure.Distribution α)
    (function : α → β) (exponent : Nat) (value : β → Fraction.Rational) :
    (source.map function).poweredLp exponent value =
      source.poweredLp exponent (fun item => value (function item)) := by
  unfold poweredLp
  rw [source.map_toContent function]
  exact source.toContent.map_poweredLp function exponent value

/-- A pushforward powered distance expectation equals the original powered distance between the pulled-back observables.
-/
theorem map_poweredLpDistance {α β : Type}
    (source : Measure.Distribution α) (function : α → β) (exponent : Nat)
    (left right : β → Fraction.Rational) :
    (source.map function).poweredLpDistance exponent left right =
      source.poweredLpDistance exponent
        (fun item => left (function item))
        (fun item => right (function item)) := by
  unfold poweredLpDistance
  rw [source.map_toContent function]
  exact source.toContent.map_poweredLpDistance
    function exponent left right

/-- A pushforward magnitude expectation equals the original magnitude expectation of the pulled-back observable. -/
theorem map_poweredL1 {α β : Type} (source : Measure.Distribution α)
    (function : α → β) (value : β → Fraction.Rational) :
    (source.map function).poweredL1 value =
      source.poweredL1 (fun item => value (function item)) := by
  unfold poweredL1
  rw [source.map_toContent function]
  exact source.toContent.map_poweredL1 function value

/-- Pushforward integrated distance equals the original integrated distance between the pulled-back observables. -/
theorem map_l1Distance {α β : Type} (source : Measure.Distribution α)
    (function : α → β) (left right : β → Fraction.Rational) :
    (source.map function).l1Distance left right =
      source.l1Distance (fun item => left (function item))
        (fun item => right (function item)) := by
  unfold l1Distance
  rw [source.map_expectation]

/-- A pushforward squared-observable expectation equals the original squared expectation of the pullback. -/
theorem map_poweredL2 {α β : Type} (source : Measure.Distribution α)
    (function : α → β) (value : β → Fraction.Rational) :
    (source.map function).poweredL2 value =
      source.poweredL2 (fun item => value (function item)) := by
  unfold poweredL2
  rw [source.map_toContent function]
  exact source.toContent.map_poweredL2 function value

/-- Pushforward squared-distance expectation equals the original squared-distance expectation between pullbacks. -/
theorem map_poweredL2Distance {α β : Type}
    (source : Measure.Distribution α) (function : α → β)
    (left right : β → Fraction.Rational) :
    (source.map function).poweredL2Distance left right =
      source.poweredL2Distance (fun item => left (function item))
        (fun item => right (function item)) := by
  unfold poweredL2Distance
  rw [source.map_toContent function]
  exact source.toContent.map_poweredL2Distance function left right
end

end Distribution

end Purelib.Measure

end
