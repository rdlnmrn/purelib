module

public import Purelib.Approximation.Rational.Geometric.Search

/-! # Initial-stage readbacks of an already paid quarter-radius selection

The original scan and Selection keep their complete factories. When the
first tested stage already pays the original request, their literal output
stage is that same input; no modified scan or relabelled selection is used.
-/

public section

namespace Purelib.Approximation.Rational.Geometric.Search

open Purelib.Data.Rat.Fraction (Rational)

/-- An already accurate initial stage is unchanged by the original finite scan at every fuel. -/
theorem scanFirstBelow_eq_current (scale target : Rational) (current : Nat)
    (accurate : Basic.quarterRadius scale current < target) :
    ∀ fuel, scanFirstBelow scale target current fuel = current
  | 0 => rfl
  | _ + 1 => by
    rewrite [scanFirstBelow, if_pos accurate]
    rfl

/-- The original bounded stage producer retains an already accurate input stage. -/
theorem firstQuarterBelow_eq_current (scale target : Rational) (current : Nat)
    (accurate : Basic.quarterRadius scale current < target) :
    firstQuarterBelow scale current target = current := by
  unfold firstQuarterBelow
  exact scanFirstBelow_eq_current scale target current accurate _

/-- The original whole Selection factory returns its input stage when that stage already pays its request. -/
theorem Selection.build_stage_eq_of_accurate (scale : Rational) (nonnegative : 0 ≤ scale)
    (current : Nat) (target : Rational) (positive : 0 < target)
    (accurate : Basic.quarterRadius scale current < target) :
    (Selection.build scale nonnegative current target positive).stage = current :=
  (Selection.build scale nonnegative current target positive).stage_eq.trans
    (scanFirstBelow_eq_current scale target current accurate _)

end Purelib.Approximation.Rational.Geometric.Search

end
