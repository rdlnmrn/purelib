module
import Purelib.Data.Rat.Fraction
import Purelib.Data.List.Membership
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
public import Purelib.Measure.Distribution.Convergence.Tail
import Purelib.Measure.Event.RationalDistance
import Purelib.Measure.EventAlgebra.Basic
import Purelib.Measure.Distribution.Lp.Natural
import Purelib.Measure.Distribution.Lp.L2
import Purelib.Measure.Distribution.Content
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic

@[expose] public section

/-!
# Executable finite measure examples

All numerical examples reduce to finite rational calculations checked by the
kernel.  The final examples exercise the generic CCL area-request interface
without postulating a completed CCL value.
-/

namespace Purelib.Examples.Measure.Distribution.Lp.Coin.WorkedExamples

open Purelib.Data.Rat
open Purelib.Data.List
open Purelib.Examples
open Purelib.Measure
open Purelib.Examples.Measure.Distribution.Coin.Basic (coinNumber fairCoin reverseCoinNumber)

/-- The common powered-L2 ceiling one half for the two coin indicators. -/
def coinL2FamilyBudget : Distribution.L2FamilyBudget
  fairCoin
    [coinNumber, reverseCoinNumber] where
  ceiling := 1 / 2
  ceiling_nonnegative := by decide
  poweredL2_le value member := by
    have selected : value = coinNumber ∨
        value = reverseCoinNumber := by
      rcases Membership.mem_cons.mp member with same | tail
      · exact Or.inl same
      · exact Or.inr (Membership.mem_singleton.mp tail)
    rcases selected with rfl | rfl <;> decide

/-- The coin indicator's absolute tail integral at threshold one is one half. -/
example : fairCoin.absoluteTailIntegral 1 coinNumber = 1
  / 2 := by
  decide

/-- Each indicator in the retained family has absolute tail integral at most one half at threshold one. -/
example (value : Bool → Fraction.Rational)
    (member : value ∈ [coinNumber, reverseCoinNumber]) :
    fairCoin.absoluteTailIntegral 1 value ≤ 1 / 2 := by
  have bound := coinL2FamilyBudget.absoluteTailIntegral_le value member 1
    (by decide)
  change fairCoin.absoluteTailIntegral 1 value ≤ (1 / 2 : Fraction.Rational) / 1
    at bound
  have quotient : (1 / 2 : Fraction.Rational) / 1 = 1 / 2 := by decide
  rw [quotient] at bound
  exact bound

/-- The coin indicator has powered L2 value one half. -/
example : fairCoin.poweredLp 2 coinNumber = 1 / 2 := by
  decide

/-- Scaling both indicators by minus two scales their powered L3 distance by the cubed scalar magnitude. -/
example : fairCoin.poweredLpDistance 3
      (fun outcome => (-2 : Fraction.Rational) * coinNumber outcome)
      (fun outcome => (-2 : Fraction.Rational) * reverseCoinNumber outcome) =
    Purelib.Data.Rat.Distance.rationalSeparation (-2) 0 ^ 3 *
      fairCoin.poweredLpDistance 3 coinNumber
        reverseCoinNumber :=
  fairCoin.poweredLpDistance_scale 3 (-2)
    coinNumber reverseCoinNumber

/-- The scaled indicators have powered L3 distance eight. -/
example : fairCoin.poweredLpDistance 3
      (fun outcome => (-2 : Fraction.Rational) * coinNumber outcome)
      (fun outcome => (-2 : Fraction.Rational) * reverseCoinNumber outcome) = 8 := by
  decide

/-- The exponent-two powered Lp distance agrees with the powered L2 distance on the original coin content. -/
example : fairCoin.toContent.poweredLpDistance 2
      coinNumber reverseCoinNumber =
    fairCoin.toContent.poweredL2Distance
      coinNumber reverseCoinNumber :=
  fairCoin.toContent.poweredLpDistance_two
    coinNumber reverseCoinNumber

/-- The separation-at-one probability satisfies the powered-L2 tail bound. -/
example : fairCoin.probability
      (separationAtLeast 1 coinNumber reverseCoinNumber)
        ≤
    fairCoin.poweredLpDistance 2 coinNumber
      reverseCoinNumber / 1 ^ 2 :=
  fairCoin.probability_separationAtLeast_le_poweredLpDistance
    2 1 (by decide) coinNumber reverseCoinNumber

end Purelib.Examples.Measure.Distribution.Lp.Coin.WorkedExamples

end
