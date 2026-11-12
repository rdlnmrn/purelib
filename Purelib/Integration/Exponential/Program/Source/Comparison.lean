module
public import Purelib.Integration.Exponential.Program.Source
public import Purelib.Approximation.Gaussian.Exponential.Horner.Real.Comparison
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Field

/-!
# Quantitative comparison of original exponential program stages

Each common child retains both original finite point readings. The two
selected Taylor depths supply shrinking rational coordinate radii, which
pay for the actual length-weighted discrepancy without a new oracle.
-/

public section

namespace Purelib.Integration.Exponential.Program.Source

open Purelib.Approximation
open Purelib.Approximation.Gaussian.Exponential.Horner
open Purelib.Data.Nat.Schedule
open Purelib.Data.Rat
open Purelib.Integration.Exponential

/-- The two fixed-depth source frontiers pay their common-point discrepancy with their original radii. -/
theorem finitePointBudget (leftDepth rightDepth : Nat) (left : SourceFrontier (Real.finiteSource leftDepth))
    (right : SourceFrontier (Real.finiteSource rightDepth)) :
    (SourceFrontier.commonReadings left right).pointBudget ≤
      Real.tailRadius leftDepth + Real.tailRadius rightDepth :=
  (SourceFrontier.commonReadings left right).pointBudget_le_of_bound _ (Real.finite_difference leftDepth rightDepth)

/-- The actual common-point discrepancy is paid by the two original selected-depth coordinate radii. -/
theorem pointBudget_le {leftPolicy rightPolicy : Geometry.Policy} {leftSchedule rightSchedule : PositiveStride}
    {leftExtra rightExtra leftIndex rightIndex : Nat} {leftRequest rightRequest : AccuracyRequest}
    (left : Result leftPolicy leftSchedule leftExtra leftIndex leftRequest)
    (right : Result rightPolicy rightSchedule rightExtra rightIndex rightRequest) :
    (common left right).pointBudget ≤ Real.tailRadius (Selection.selection leftPolicy leftSchedule leftIndex).depth +
      Real.tailRadius (Selection.selection rightPolicy rightSchedule rightIndex).depth :=
  finitePointBudget _ _ left.sourceResult.frontier right.sourceResult.frontier

/-- Independently selected original stage samples differ by their source widths and explicit finite-depth radii.

The displayed radii come from the same original selected Taylor depths.
They bound the actual common-point budget and shrink with those finite
depths; both original cached stage samples and enclosures remain unchanged. -/
theorem samples_difference_le_radii {leftPolicy rightPolicy : Geometry.Policy}
    {leftSchedule rightSchedule : PositiveStride} {leftExtra rightExtra leftIndex rightIndex : Nat}
    {leftRequest rightRequest : AccuracyRequest}
    (left : Result leftPolicy leftSchedule leftExtra leftIndex leftRequest)
    (right : Result rightPolicy rightSchedule rightExtra rightIndex rightRequest) :
    Fraction.abs (left.stage.sample.re - right.stage.sample.re) ≤
      (integralBound left.sourceResult.frontier.cells).width + (integralBound right.sourceResult.frontier.cells).width +
        (Real.tailRadius (Selection.selection leftPolicy leftSchedule leftIndex).depth +
          Real.tailRadius (Selection.selection rightPolicy rightSchedule rightIndex).depth) := by
  have compared := samples_difference_le left right
  have paid := Fraction.Order.Arithmetic.add_le_add_direct
    (Fraction.Order.Basic.le_refl ((integralBound left.sourceResult.frontier.cells).width +
      (integralBound right.sourceResult.frontier.cells).width)) (pointBudget_le left right)
  exact compared.trans paid

end Purelib.Integration.Exponential.Program.Source

end
