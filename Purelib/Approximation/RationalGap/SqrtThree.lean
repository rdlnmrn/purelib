module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Interval.Basic
import Purelib.Data.Rat.Interval.Bisection
public import Purelib.NumberTheory.SquareClass.Rational.Nonsquare
import Purelib.Approximation.Bound.Process
public import Purelib.Approximation.RationalGap.Basic
import Purelib.Data.Rat.Fraction.Compatibility
public import Purelib.Approximation.Rational.Budget.Geometric
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Interval.Exclusion
import Purelib.Tactic.Ring

open Purelib.Data.Rat.Fraction.Order

open Purelib

open Purelib.Approximation

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Data.Rat.Interval

open Purelib.NumberTheory

@[expose] public section

/-!
# A concrete rational enclosure process for the square-three gap

The process below repeatedly bisects rational brackets whose lower endpoint
has square below three and whose upper endpoint has square above three.  The
finite geometric search computes enough bisections for any positive rational
request.  No square root or completed real is defined.
-/

namespace Purelib.Approximation.SqrtThree

set_option genInjectivity false in
/-- Finite rational data straddling the positive square-three gap. -/
structure Bracket where
  /-- The retained lower rational endpoint. -/ lower : Fraction.Rational
  /-- The retained upper rational endpoint. -/ upper : Fraction.Rational
  /-- The lower endpoint is nonnegative. -/ lower_nonnegative : 0 ≤ lower
  /-- The lower endpoint squared is strictly below three. -/ lower_square_lt : lower ^ 2 < 3
  /-- The upper endpoint squared is strictly above three. -/ upper_square_gt : 3 < upper ^ 2
  /-- The lower endpoint is strictly below the upper endpoint. -/ ordered : lower < upper

constructive_injectivity Bracket

namespace Bracket

/-- Forget the square certificates while retaining the rational enclosure. -/
def bound (bracket : Bracket) : Interval where
  lower := bracket.lower
  upper := bracket.upper
  valid := Arithmetic.le_of_lt_direct bracket.ordered

/-- Every square-three bracket has strictly positive enclosure width. -/
theorem bound_width_pos (bracket : Bracket) : 0 < bracket.bound.width := by
  dsimp only [Interval.width, bound]
  exact Arithmetic.sub_pos_direct bracket.ordered

/-- The upper endpoint of a square-three bracket is nonnegative. -/
theorem upper_nonnegative (bracket : Bracket) : 0 ≤ bracket.upper :=
  Basic.Compatibility.le_trans 0 bracket.lower bracket.upper
    bracket.lower_nonnegative
    (Arithmetic.le_of_lt_direct bracket.ordered)

/-- Rational midpoint. -/
def midpoint (bracket : Bracket) : Fraction.Rational :=
  (bracket.lower + bracket.upper) / 2

/-- The rational midpoint lies strictly above the lower endpoint. -/
theorem lower_lt_midpoint (bracket : Bracket) :
    bracket.lower < bracket.midpoint := by
  apply (Field.lt_div_iff_pos
    (by decide : (0 : Fraction.Rational) < 2)).2
  calc
    bracket.lower * 2 = bracket.lower + bracket.lower := by ring1
    _ < bracket.lower + bracket.upper :=
      Arithmetic.add_lt_add_left_direct
        bracket.ordered bracket.lower

/-- The rational midpoint lies strictly below the upper endpoint. -/
theorem midpoint_lt_upper (bracket : Bracket) :
    bracket.midpoint < bracket.upper := by
  apply (Field.div_lt_iff_pos
    (by decide : (0 : Fraction.Rational) < 2)).2
  calc
    bracket.lower + bracket.upper <
        bracket.upper + bracket.upper :=
      Arithmetic.add_lt_add_right_direct
        bracket.ordered bracket.upper
    _ = bracket.upper * 2 := by ring1

/-- The midpoint of a square-three bracket is nonnegative. -/
theorem midpoint_nonnegative (bracket : Bracket) :
    0 ≤ bracket.midpoint :=
  Field.div_nonneg_direct
    (add_nonneg bracket.lower_nonnegative bracket.upper_nonnegative)
    (by decide)

/-- One exact rational bisection, choosing the side whose endpoint squares still straddle three. `square_ne_three` makes
the branch strict. -/
def bisect (bracket : Bracket) : Bracket :=
  if below : bracket.midpoint ^ 2 < 3 then
    { lower := bracket.midpoint
      upper := bracket.upper
      lower_nonnegative := bracket.midpoint_nonnegative
      lower_square_lt := below
      upper_square_gt := bracket.upper_square_gt
      ordered := bracket.midpoint_lt_upper }
  else
    { lower := bracket.lower
      upper := bracket.midpoint
      lower_nonnegative := bracket.lower_nonnegative
      lower_square_lt := bracket.lower_square_lt
      upper_square_gt := by
        have threeLe : (3 : Fraction.Rational) ≤ bracket.midpoint ^ 2 :=
          Arithmetic.le_of_not_gt_direct below
        exact ⟨threeLe, fun reverse =>
          SquareClass.Rational.Nonsquare.square_ne_three bracket.midpoint
            (Basic.Compatibility.le_antisymm _ _
              threeLe reverse).symm⟩
      ordered := bracket.lower_lt_midpoint }

/-- Bisection refines the original square-three enclosure. -/
theorem bisect_bound_refines (bracket : Bracket) :
    Refines bracket.bisect.bound bracket.bound := by
  unfold bisect
  split
  · exact ⟨Arithmetic.le_of_lt_direct
      bracket.lower_lt_midpoint, le_rfl⟩
  · exact ⟨le_rfl, Arithmetic.le_of_lt_direct
      bracket.midpoint_lt_upper⟩

/-- Square-three bisection halves the original enclosure width exactly. -/
theorem bisect_width (bracket : Bracket) :
    bracket.bisect.bound.width = bracket.bound.width * (1 / 2) := by
  unfold bisect
  split
  · dsimp only [bound, Interval.width, midpoint]
    exact Interval.Bisection.upper_sub_midpoint_eq_half_width bracket.lower bracket.upper
  · dsimp only [bound, Interval.width, midpoint]
    exact Interval.Bisection.midpoint_sub_lower_eq_half_width bracket.lower bracket.upper

/-- Execute exactly the displayed finite number of bisections. -/
def iterateBisect : Nat → Bracket → Bracket
  | 0, bracket => bracket
  | count + 1, bracket => Bracket.iterateBisect count bracket.bisect

/-- Every finite sequence of square-three bisections refines its initial enclosure. -/
theorem iterateBisect_refines :
    ∀ (count : Nat) (bracket : Bracket),
      Refines (iterateBisect count bracket).bound bracket.bound
  | 0, _ => Refines.refl _
  | count + 1, bracket =>
      (Bracket.iterateBisect_refines count bracket.bisect).trans
        bracket.bisect_bound_refines

/-- Finite repeated bisection multiplies the original width by the corresponding half-power. -/
theorem iterateBisect_width :
    ∀ (count : Nat) (bracket : Bracket),
      (iterateBisect count bracket).bound.width =
        bracket.bound.width * (1 / 2 : Fraction.Rational) ^ count
  | 0, bracket => by
      dsimp only [iterateBisect]
      rewrite [pow_zero]
      exact (Fraction.Field.mul_one_direct _).symm
  | count + 1, bracket => by
      rw [iterateBisect, Bracket.iterateBisect_width
        count bracket.bisect,
        bracket.bisect_width, pow_succ]
      ring1

/-- An even half-power equals the corresponding quarter-power. -/
private theorem half_pow_two_mul (index : Nat) :
    (1 / 2 : Fraction.Rational) ^ (2 * index) = (1 / 4 : Fraction.Rational) ^ index := by
  calc
    (1 / 2 : Fraction.Rational) ^ (2 * index) =
        ((1 / 2 : Fraction.Rational) ^ 2) ^ index := by rw [pow_mul]
    _ = (1 / 4 : Fraction.Rational) ^ index := by
      have halfSquare : (1 / 2 : Fraction.Rational) ^ 2 = 1 / 4 := by decide
      rw [halfSquare]

/-- Computed finite bisection count for one positive rational width request. -/
def requiredBisections (bracket : Bracket) (target : Fraction.Rational) : Nat :=
  2 * Geometric.firstQuarterBelow bracket.bound.width 0 target

/-- The computed finite bisection count yields width strictly below a positive target. -/
theorem requiredBisections_accurate (bracket : Bracket)
    {target : Fraction.Rational} (positive : 0 < target) :
    (iterateBisect (requiredBisections bracket target)
      bracket).bound.width <
      target := by
  let index := Geometric.firstQuarterBelow bracket.bound.width 0 target
  have requested := Geometric.firstQuarterBelow_accurate
    bracket.bound.width
      (Arithmetic.sub_nonneg_direct bracket.bound.valid)
      0 target positive
  rw [Geometric.quarterAllowance_eq_mul_pow] at requested
  rw [iterateBisect_width, requiredBisections,
    half_pow_two_mul]
  exact requested

end Bracket

/-- Initial rational square-three bracket `[1,2]`. -/
def initialBracket : Bracket where
  lower := 1
  upper := 2
  lower_nonnegative := by decide
  lower_square_lt := by decide
  upper_square_gt := by decide
  ordered := by decide

set_option genInjectivity false in
/-- A reachable-style state retains an explicit refinement certificate back to the initial rational bracket. -/
structure State where
  /-- The retained square-three bracket at this state. -/ bracket : Bracket
  /-- The retained bracket refines the distinguished initial bracket. -/ refines_initial : Refines
    bracket.bound initialBracket.bound

constructive_injectivity State

/-- Distinguished initial state. -/
def initialState : State :=
  ⟨initialBracket, Refines.refl _⟩

/-- Request a finite square-three bracket below a positive rational width. -/
def request (state : State) (target : Fraction.Rational) : State :=
  let refined := state.bracket.iterateBisect
    (state.bracket.requiredBisections target)
  ⟨refined,
    (state.bracket.iterateBisect_refines
      (state.bracket.requiredBisections target)).trans state.refines_initial⟩

/-- Concrete arbitrary-accuracy rational enclosure process naming no real number. -/
def process : BoundProcess where
  State := State
  bound state := state.bracket.bound
  initial := initialState
  request state target _ := request state target
  request_refines state target _ :=
    state.bracket.iterateBisect_refines
      (state.bracket.requiredBisections target)
  accurate state target positive :=
    state.bracket.requiredBisections_accurate (target := target) positive
  refinesInitial state := state.refines_initial

/-- Every state remains a genuinely positive-width rational bracket; no finite request silently manufactures an exact
rational value. -/
theorem state_width_pos (state : State) :
    0 < (process.bound state).width :=
  state.bracket.bound_width_pos

/-- A finite square-three state cannot be an exact rational singleton enclosure. -/
theorem state_bound_ne_exact (state : State) (candidate : Fraction.Rational) :
    process.bound state ≠ Interval.exact candidate := by
  intro equal
  have widths := congrArg Interval.width equal
  rw [Interval.exact_width] at widths
  exact (state_width_pos state).ne' widths

/-- The rational square obstruction is independently decidable at every displayed candidate. -/
theorem candidate_square_ne_three (candidate : Fraction.Rational) :
    candidate ^ 2 ≠ 3 :=
  SquareClass.Rational.Nonsquare.square_ne_three candidate

/-! ## Candidate-by-candidate rational separation -/

/-- Positive rational width small enough to distinguish a displayed candidate by its nonzero square residual. -/
def separationTolerance (candidate : Fraction.Rational) : Fraction.Rational :=
  if candidate ^ 2 < 3 then (3 - candidate ^ 2) / 4
  else (candidate ^ 2 - 3) / 4

/-- Every rational candidate has strictly positive square-residual separation tolerance. -/
theorem separationTolerance_pos (candidate : Fraction.Rational) :
    0 < separationTolerance candidate := by
  unfold separationTolerance
  split
  · exact Field.div_pos_direct
      (Arithmetic.sub_pos_direct (by assumption)) (by decide)
  · have threeLe : (3 : Fraction.Rational) ≤ candidate ^ 2 :=
      Arithmetic.le_of_not_gt_direct (by assumption)
    have threeLt : (3 : Fraction.Rational) < candidate ^ 2 :=
      ⟨threeLe, fun reverse =>
        candidate_square_ne_three candidate
          (Basic.Compatibility.le_antisymm _ _
            threeLe reverse).symm⟩
    exact Field.div_pos_direct
      (Arithmetic.sub_pos_direct threeLt) (by decide)

/-- A width below one quarter of a residual remains below that residual after scaling by four. -/
private theorem scaled_width_lt_residual
    {width residual : Fraction.Rational} (small : width < residual / 4) :
    width * 4 < residual := by
  have scaled := Arithmetic.mul_lt_mul_of_pos_right_direct
    small (by decide : (0 : Fraction.Rational) < 4)
  calc
    width * 4 < (residual / 4) * 4 := scaled
    _ = residual :=
      Fraction.Field.div_mul_cancel_of_ne residual 4 (by decide)

/-- A sufficiently narrow square-three state excludes the displayed rational candidate. -/
theorem excludes_of_width_lt_separationTolerance
    (state : State) (candidate : Fraction.Rational)
    (small : state.bracket.bound.width < separationTolerance candidate) :
    state.bracket.bound.Excludes candidate := by
  by_cases belowLower : candidate < state.bracket.lower
  · exact Or.inl belowLower
  by_cases aboveUpper : state.bracket.upper < candidate
  · exact Or.inr aboveUpper
  have inside : state.bracket.lower ≤ candidate ∧
      candidate ≤ state.bracket.upper :=
    ⟨Arithmetic.le_of_not_gt_direct belowLower,
      Arithmetic.le_of_not_gt_direct aboveUpper⟩
  have upperLeTwo : state.bracket.upper ≤ 2 := by
    exact state.refines_initial.upper
  have candidateNonnegative : 0 ≤ candidate :=
    state.bracket.lower_nonnegative.trans inside.1
  by_cases belowSquare : candidate ^ 2 < 3
  · have residualSmall :
        state.bracket.bound.width < (3 - candidate ^ 2) / 4 := by
      rewrite [separationTolerance, if_pos belowSquare] at small
      exact small
    have residualLtDifference :
        3 - candidate ^ 2 <
          state.bracket.upper ^ 2 - candidate ^ 2 :=
      Arithmetic.sub_lt_sub_right_direct
        state.bracket.upper_square_gt (candidate ^ 2)
    have firstFactor :
        state.bracket.upper - candidate ≤ state.bracket.bound.width := by
      dsimp only [Bracket.bound, Interval.width]
      exact Arithmetic.sub_le_sub_direct le_rfl inside.1
    have secondFactor : state.bracket.upper + candidate ≤ 4 := by
      calc
        state.bracket.upper + candidate ≤ 2 + 2 :=
          add_le_add upperLeTwo (inside.2.trans upperLeTwo)
        _ = 4 := by ring1
    have factorNonnegative : 0 ≤ state.bracket.upper + candidate :=
      add_nonneg state.bracket.upper_nonnegative candidateNonnegative
    have productBound :
        (state.bracket.upper - candidate) *
            (state.bracket.upper + candidate) ≤
          state.bracket.bound.width * 4 :=
      Arithmetic.mul_le_mul_direct firstFactor secondFactor
        factorNonnegative state.bracket.bound.width_nonneg
    have residualLtWidth :
        3 - candidate ^ 2 < state.bracket.bound.width * 4 := by
      calc
        3 - candidate ^ 2 <
            state.bracket.upper ^ 2 - candidate ^ 2 := residualLtDifference
        _ = (state.bracket.upper - candidate) *
              (state.bracket.upper + candidate) := by ring1
        _ ≤ state.bracket.bound.width * 4 := productBound
    have widthLtResidual := scaled_width_lt_residual residualSmall
    exact (lt_asymm residualLtWidth widthLtResidual).elim
  · have threeLe : (3 : Fraction.Rational) ≤ candidate ^ 2 :=
      Arithmetic.le_of_not_gt_direct belowSquare
    have threeLt : (3 : Fraction.Rational) < candidate ^ 2 :=
      ⟨threeLe, fun reverse =>
        candidate_square_ne_three candidate
          (Basic.Compatibility.le_antisymm _ _
            threeLe reverse).symm⟩
    have residualSmall :
        state.bracket.bound.width < (candidate ^ 2 - 3) / 4 := by
      rewrite [separationTolerance, if_neg belowSquare] at small
      exact small
    have residualLtDifference :
        candidate ^ 2 - 3 <
          candidate ^ 2 - state.bracket.lower ^ 2 :=
      Arithmetic.sub_lt_sub_left_direct
        state.bracket.lower_square_lt (candidate ^ 2)
    have firstFactor :
        candidate - state.bracket.lower ≤ state.bracket.bound.width := by
      dsimp only [Bracket.bound, Interval.width]
      exact Arithmetic.sub_le_sub_direct inside.2 le_rfl
    have lowerLeTwo : state.bracket.lower ≤ 2 :=
      (Arithmetic.le_of_lt_direct
        state.bracket.ordered).trans upperLeTwo
    have secondFactor : candidate + state.bracket.lower ≤ 4 := by
      calc
        candidate + state.bracket.lower ≤ 2 + 2 :=
          add_le_add (inside.2.trans upperLeTwo) lowerLeTwo
        _ = 4 := by ring1
    have factorNonnegative : 0 ≤ candidate + state.bracket.lower :=
      add_nonneg candidateNonnegative state.bracket.lower_nonnegative
    have productBound :
        (candidate - state.bracket.lower) *
            (candidate + state.bracket.lower) ≤
          state.bracket.bound.width * 4 :=
      Arithmetic.mul_le_mul_direct firstFactor secondFactor
        factorNonnegative state.bracket.bound.width_nonneg
    have residualLtWidth :
        candidate ^ 2 - 3 < state.bracket.bound.width * 4 := by
      calc
        candidate ^ 2 - 3 <
            candidate ^ 2 - state.bracket.lower ^ 2 := residualLtDifference
        _ = (candidate - state.bracket.lower) *
              (candidate + state.bracket.lower) := by ring1
        _ ≤ state.bracket.bound.width * 4 := productBound
    have widthLtResidual := scaled_width_lt_residual residualSmall
    exact (lt_asymm residualLtWidth widthLtResidual).elim

/-- Refine far enough to exclude one displayed rational candidate. -/
def separate (state : State) (candidate : Fraction.Rational) : State :=
  request state (separationTolerance candidate)

/-- Separating one rational candidate refines the original state enclosure. -/
theorem separate_refines (state : State) (candidate : Fraction.Rational) :
    Refines (process.bound (separate state candidate))
      (process.bound state) :=
  process.request_refines state (separationTolerance candidate)
    (separationTolerance_pos candidate)

/-- The computed separation state excludes the supplied rational candidate. -/
theorem separate_excludes (state : State) (candidate : Fraction.Rational) :
    (process.bound (separate state candidate)).Excludes candidate := by
  apply excludes_of_width_lt_separationTolerance
  exact process.accurate state (separationTolerance candidate)
    (separationTolerance_pos candidate)

/-- Concrete finite rational-gap protocol for the square-three enclosure. -/
def gapProcess : RationalGapProcess where
  process := process
  separate := separate
  separate_refines := separate_refines
  separate_excludes := separate_excludes

end Purelib.Approximation.SqrtThree

end
