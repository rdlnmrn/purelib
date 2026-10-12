module
import Purelib.Data.Rat.Distance.Basic
public import Purelib.Examples.Measure.Distribution.Coin.Basic

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Measure.Distribution.Basic
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
import Purelib.Measure.Content.Restriction.Lp
public import Purelib.Measure.Distribution.Conditioning.Basic
import Purelib.Measure.Distribution.Conditioning.Mean
import Purelib.Measure.Distribution.Lp.Natural
import Purelib.Measure.Distribution.EssentialMaximum.Basic
import Purelib.Measure.Distribution.Conditioning.Lp
import Purelib.Measure.EventAlgebra.Basic
import Purelib.Measure.Distribution.EssentialMaximum.Operations
import Purelib.Measure.Distribution.Lp.L2
import Purelib.Measure.Distribution.Content
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic

@[expose] public section

/-!
# Executable finite measure examples

All numerical examples reduce to finite rational calculations checked by the
kernel.  The final examples exercise the generic CCL area-request interface
without postulating a completed CCL value.
-/

namespace Purelib.Examples.Measure.Distribution.Conditioned.Coin.Basic

open Purelib.Examples
open Purelib.Measure
open Purelib.Examples.Measure.Distribution.Coin.Basic (coinNumber fairCoin reverseCoinNumber)

/-- The heads event has positive fair-coin probability. -/
theorem fairCoin_true_positive :
    0 < fairCoin.probability (fun outcome => outcome) := by
  decide

/-- Restricting fair-coin content to heads cannot increase the powered L2 value of the indicator. -/
example : (fairCoin.toContent.restrict
      (fun outcome => outcome)).poweredL2 coinNumber ≤
    fairCoin.toContent.poweredL2 coinNumber :=
  fairCoin.toContent.restrict_poweredL2_le
    (fun outcome => outcome) coinNumber

/-- Both the original and heads-restricted indicator have powered L2 value one half. -/
example : (fairCoin.toContent.restrict
      (fun outcome => outcome)).poweredL2 coinNumber = 1 / 2 ∧
    fairCoin.toContent.poweredL2 coinNumber = 1 / 2 :=
      by
  decide

/-- The fair coin conditioned on its positive-probability heads event. -/
def trueCoin : Distribution Bool :=
  fairCoin.conditioned (fun outcome => outcome)
    fairCoin_true_positive

/-- Conditioning on heads cannot increase the reverse indicator's essential maximum. -/
example : trueCoin.essentialMaximumMagnitude
  reverseCoinNumber ≤
    fairCoin.essentialMaximumMagnitude reverseCoinNumber
      := by
  unfold trueCoin
  exact fairCoin.conditioned_essentialMaximumMagnitude_le
    (fun outcome => outcome) fairCoin_true_positive
      reverseCoinNumber

/-- The reverse indicator has essential maximum zero after conditioning, compared with one before conditioning. -/
example : trueCoin.essentialMaximumMagnitude
  reverseCoinNumber = 0 ∧
    fairCoin.essentialMaximumMagnitude reverseCoinNumber
      = 1 := by
  decide

/-- Conditioning on heads cannot increase the essential maximum distance between the two indicators. -/
example : trueCoin.essentialMaximumDistance
      coinNumber reverseCoinNumber ≤
    fairCoin.essentialMaximumDistance coinNumber
      reverseCoinNumber := by
  unfold trueCoin
  exact fairCoin.conditioned_essentialMaximumDistance_le
    (fun outcome => outcome) fairCoin_true_positive
    coinNumber reverseCoinNumber

/-- The conditioned powered L3 value equals the original conditional mean of the cubed magnitude. -/
example : trueCoin.poweredLp 3 coinNumber =
    fairCoin.conditionalMean (fun outcome => outcome) (fun outcome =>
      Purelib.Data.Rat.Distance.rationalSeparation (coinNumber outcome) 0 ^ 3) := by
  unfold trueCoin
  exact fairCoin.conditioned_poweredLp_eq_conditionalMean
    (fun outcome => outcome) fairCoin_true_positive 3
      coinNumber

/-- The heads-conditioned coin indicator has powered L3 value one. -/
example : trueCoin.poweredLp 3 coinNumber =
  1 := by
  decide

end Purelib.Examples.Measure.Distribution.Conditioned.Coin.Basic

end
