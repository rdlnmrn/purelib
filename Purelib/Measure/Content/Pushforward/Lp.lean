module
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Measure.Content.Basic
import Purelib.Measure.Content.Integral
import Purelib.Measure.Content.Lp.L1
import Purelib.Measure.Content.Lp.L2
public import Purelib.Measure.Content.Lp.Natural
import Purelib.Measure.Content.Operations
import Purelib.Data.Rat.Fraction

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
namespace Content

open Purelib.Data.Rat
/-- Powered integration under mapped content equals original powered integration of the observable composed with the
exact payload map. -/
theorem map_poweredLp {α β : Type} (content : Content α)
    (function : α → β) (exponent : Nat) (value : β → Fraction.Rational) :
    (content.map function).poweredLp exponent value =
      content.poweredLp exponent (fun item => value (function item)) := by
  unfold poweredLp
  exact content.map_integral function _

/-- Powered distance under mapped content equals original powered distance of the two composed observables. -/
theorem map_poweredLpDistance {α β : Type}
    (content : Content α) (function : α → β) (exponent : Nat)
    (left right : β → Fraction.Rational) :
    (content.map function).poweredLpDistance exponent left right =
      content.poweredLpDistance exponent
        (fun item => left (function item))
        (fun item => right (function item)) := by
  unfold poweredLpDistance
  exact content.map_integral function _

/-- Magnitude integration under mapped content equals original magnitude integration of the composed observable. -/
theorem map_poweredL1 {α β : Type} (content : Content α)
    (function : α → β) (value : β → Fraction.Rational) :
    (content.map function).poweredL1 value =
      content.poweredL1 (fun item => value (function item)) := by
  unfold poweredL1
  exact content.map_integral function _

/-- Integrated separation under mapped content equals original separation integration of the composed observables. -/
theorem map_l1Distance {α β : Type} (content : Content α)
    (function : α → β) (left right : β → Fraction.Rational) :
    (content.map function).l1Distance left right =
      content.l1Distance (fun item => left (function item))
        (fun item => right (function item)) := by
  unfold l1Distance
  exact content.map_integral function _

/-- Square integration under mapped content equals original square integration of the composed observable. -/
theorem map_poweredL2 {α β : Type} (content : Content α)
    (function : α → β) (value : β → Fraction.Rational) :
    (content.map function).poweredL2 value =
      content.poweredL2 (fun item => value (function item)) := by
  unfold poweredL2
  exact content.map_integral function _

/-- Squared integrated distance under mapped content equals original squared distance of the composed observables. -/
theorem map_poweredL2Distance {α β : Type}
    (content : Content α) (function : α → β)
    (left right : β → Fraction.Rational) :
    (content.map function).poweredL2Distance left right =
      content.poweredL2Distance (fun item => left (function item))
        (fun item => right (function item)) := by
  unfold poweredL2Distance
  rw [content.map_poweredL2]
end Content

end Purelib.Measure

end
