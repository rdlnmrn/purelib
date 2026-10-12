module
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Distribution.EssentialMaximum.Basic
public import Purelib.Measure.Distribution.Kernel.Basic
import Purelib.Measure.Distribution.Lp.AlmostEverywhere
import Purelib.Measure.Distribution.Lp.L1
import Purelib.Measure.Distribution.Lp.Natural
import Purelib.Measure.Distribution.Pushforward.EssentialMaximum
import Purelib.Measure.Distribution.Pushforward.Lp
import Purelib.Data.Rat.Fraction
public import Purelib.Examples.Measure.Distribution.Coin.Basic

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Measure.Content.Basic
import Purelib.Measure.Classified.Basic
import Purelib.Measure.Filtration.Basic
import Purelib.Measure.Distribution.Partition.Basic
import Purelib.Measure.Distribution.Partition.Positive
import Purelib.Measure.EventAlgebra.Simple.Basic
import Purelib.Measure.Event.Chain
import Purelib.Approximation.OneSided.Basic
import Purelib.Measure.Classified.FixedLawProcess
import Purelib.Approximation.OneSided.Located
import Purelib.Measure.EventAlgebra.Basic

@[expose] public section

/-!
# Executable finite measure examples

All numerical examples reduce to finite rational calculations checked by the
kernel.  The final examples exercise the generic CCL area-request interface
without postulating a completed CCL value.
-/

namespace Purelib.Examples.Measure.Distribution.Coin.Law

open Purelib.Data.Rat
open Purelib.Examples
open Purelib.Measure
open Purelib.Examples.Measure.Distribution.Coin.Basic (coinNumber fairCoin)

/-- The rational-valued law obtained by pushing the fair coin through its zero-one indicator. -/
def coinNumberLaw : Distribution Fraction.Rational :=
  fairCoin.map coinNumber

/-- The pushed-forward law preserves the indicator's powered L2 value. -/
example : coinNumberLaw.poweredLp 2 (fun value => value) =
    fairCoin.poweredLp 2 coinNumber := by
  unfold coinNumberLaw
  exact fairCoin.map_poweredLp coinNumber 2 (fun value
    => value)

/-- The pushed-forward law preserves the indicator's L1 distance from zero. -/
example : coinNumberLaw.l1Distance (fun value => value) (fun _ => 0) =
    fairCoin.l1Distance coinNumber (fun _ => 0) := by
  unfold coinNumberLaw
  exact fairCoin.map_l1Distance coinNumber (fun value =>
    value) (fun _ => 0)

/-- The pushed-forward law preserves the indicator's essential maximum magnitude. -/
example : coinNumberLaw.essentialMaximumMagnitude (fun value => value) =
    fairCoin.essentialMaximumMagnitude coinNumber := by
  unfold coinNumberLaw
  exact fairCoin.map_essentialMaximumMagnitude
    coinNumber (fun value => value)

/-- The coin-number law has powered L2 value one half and essential maximum one. -/
example : coinNumberLaw.poweredLp 2 (fun value => value) = 1 / 2 ∧
    coinNumberLaw.essentialMaximumMagnitude (fun value => value) = 1 := by
  decide

/-- Almost-everywhere equality under the coin-number law is equivalent to equality after pullback to the original coin.
-/
example (left right : Fraction.Rational → Fraction.Rational) :
    coinNumberLaw.EqualAlmostEverywhere left right ↔
      fairCoin.EqualAlmostEverywhere
        (fun outcome => left (coinNumber outcome))
        (fun outcome => right (coinNumber outcome)) := by
  unfold coinNumberLaw
  exact fairCoin.map_equalAlmostEverywhere_iff
    coinNumber left right

end Purelib.Examples.Measure.Distribution.Coin.Law

end
