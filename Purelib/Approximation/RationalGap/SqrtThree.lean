module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Interval.Basic
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
def bound (bracket : Approximation.SqrtThree.Bracket) : Rat.Interval where
  lower := bracket.lower
  upper := bracket.upper
  valid := Fraction.Order.Arithmetic.le_of_lt_direct bracket.ordered

/-- Every square-three bracket has strictly positive enclosure width. -/
theorem bound_width_pos (bracket : Approximation.SqrtThree.Bracket) : 0 < bracket.bound.width := by
  dsimp only [Interval.width, Approximation.SqrtThree.Bracket.bound]
  exact Fraction.Order.Arithmetic.sub_pos_direct bracket.ordered

/-- The upper endpoint of a square-three bracket is nonnegative. -/
theorem upper_nonnegative (bracket : Approximation.SqrtThree.Bracket) : 0 ≤ bracket.upper :=
  Fraction.Order.Basic.Compatibility.le_trans 0 bracket.lower bracket.upper
    bracket.lower_nonnegative
    (Fraction.Order.Arithmetic.le_of_lt_direct bracket.ordered)

/-- Rational midpoint. -/
def midpoint (bracket : Approximation.SqrtThree.Bracket) : Fraction.Rational :=
  (bracket.lower + bracket.upper) / 2

/-- The rational midpoint lies strictly above the lower endpoint. -/
theorem lower_lt_midpoint (bracket : Approximation.SqrtThree.Bracket) :
    bracket.lower < bracket.midpoint := by
  apply (Fraction.Order.Field.lt_div_iff_pos
    (by decide : (0 : Fraction.Rational) < 2)).2
  calc
    bracket.lower * 2 = bracket.lower + bracket.lower := by ring1
    _ < bracket.lower + bracket.upper :=
      Fraction.Order.Arithmetic.add_lt_add_left_direct
        bracket.ordered bracket.lower

/-- The rational midpoint lies strictly below the upper endpoint. -/
theorem midpoint_lt_upper (bracket : Approximation.SqrtThree.Bracket) :
    bracket.midpoint < bracket.upper := by
  apply (Fraction.Order.Field.div_lt_iff_pos
    (by decide : (0 : Fraction.Rational) < 2)).2
  calc
    bracket.lower + bracket.upper <
        bracket.upper + bracket.upper :=
      Fraction.Order.Arithmetic.add_lt_add_right_direct
        bracket.ordered bracket.upper
    _ = bracket.upper * 2 := by ring1

/-- The midpoint of a square-three bracket is nonnegative. -/
theorem midpoint_nonnegative (bracket : Approximation.SqrtThree.Bracket) :
    0 ≤ bracket.midpoint :=
  Fraction.Order.Field.div_nonneg_direct
    (add_nonneg bracket.lower_nonnegative bracket.upper_nonnegative)
    (by decide)

/-- One exact rational bisection, choosing the side whose endpoint squares still straddle three. `square_ne_three` makes
the branch strict. -/
def bisect (bracket : Approximation.SqrtThree.Bracket) : Approximation.SqrtThree.Bracket :=
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
          Fraction.Order.Arithmetic.le_of_not_gt_direct below
        exact ⟨threeLe, fun reverse =>
          SquareClass.Rational.Nonsquare.square_ne_three bracket.midpoint
            (Fraction.Order.Basic.Compatibility.le_antisymm _ _
              threeLe reverse).symm⟩
      ordered := bracket.lower_lt_midpoint }

/-- Bisection refines the original square-three enclosure. -/
theorem bisect_bound_refines (bracket : Approximation.SqrtThree.Bracket) :
    Interval.Refines bracket.bisect.bound bracket.bound := by
  unfold SqrtThree.Bracket.bisect
  split
  · exact ⟨Fraction.Order.Arithmetic.le_of_lt_direct
      bracket.lower_lt_midpoint, le_rfl⟩
  · exact ⟨le_rfl, Fraction.Order.Arithmetic.le_of_lt_direct
      bracket.midpoint_lt_upper⟩

/-- Division by two is multiplication by one half. -/
private theorem div_two_eq_mul_half (value : Fraction.Rational) :
    value / 2 = value * (1 / 2) := by
  change value * (2 : Fraction.Rational)⁻¹ =
    value * ((1 : Fraction.Rational) * (2 : Fraction.Rational)⁻¹)
  rw [Fraction.Field.one_mul]

/-- The upper endpoint minus the midpoint is half the original width. -/
private theorem upper_sub_midpoint_eq_half_width
    (lower upper : Fraction.Rational) :
    upper - (lower + upper) / 2 = (upper - lower) * (1 / 2) := by
  have numerator :
      upper * 2 - (lower + upper) * 1 = upper - lower := by
    ring1
  calc
    upper - (lower + upper) / 2 =
        upper / 1 - (lower + upper) / 2 := by
      change upper - (lower + upper) / 2 =
        upper * (1 : Fraction.Rational)⁻¹ - (lower + upper) / 2
      rw [show (1 : Fraction.Rational)⁻¹ = 1 by decide,
        Fraction.Field.mul_one_direct]
    _ = (upper * 2 - (lower + upper) * 1) / (1 * 2) :=
      Fraction.Field.div_sub_div_direct upper 1
        (lower + upper) 2 (by decide) (by decide)
    _ = (upper - lower) / 2 := by
      rw [numerator, Fraction.Field.one_mul]
    _ = (upper - lower) * (1 / 2) := Approximation.SqrtThree.Bracket.div_two_eq_mul_half _

/-- The midpoint minus the lower endpoint is half the original width. -/
private theorem midpoint_sub_lower_eq_half_width
    (lower upper : Fraction.Rational) :
    (lower + upper) / 2 - lower = (upper - lower) * (1 / 2) := by
  have numerator :
      (lower + upper) * 1 - lower * 2 = upper - lower := by
    ring1
  calc
    (lower + upper) / 2 - lower =
        (lower + upper) / 2 - lower / 1 := by
      change (lower + upper) / 2 - lower =
        (lower + upper) / 2 - lower * (1 : Fraction.Rational)⁻¹
      rw [show (1 : Fraction.Rational)⁻¹ = 1 by decide,
        Fraction.Field.mul_one_direct]
    _ = ((lower + upper) * 1 - lower * 2) / (2 * 1) :=
      Fraction.Field.div_sub_div_direct (lower + upper) 2
        lower 1 (by decide) (by decide)
    _ = (upper - lower) / 2 := by
      rw [numerator, Fraction.Field.mul_one_direct]
    _ = (upper - lower) * (1 / 2) := Approximation.SqrtThree.Bracket.div_two_eq_mul_half _

/-- Square-three bisection halves the original enclosure width exactly. -/
theorem bisect_width (bracket : Approximation.SqrtThree.Bracket) :
    bracket.bisect.bound.width = bracket.bound.width * (1 / 2) := by
  unfold SqrtThree.Bracket.bisect
  split
  · dsimp only [Approximation.SqrtThree.Bracket.bound, Interval.width, Approximation.SqrtThree.Bracket.midpoint]
    exact Approximation.SqrtThree.Bracket.upper_sub_midpoint_eq_half_width bracket.lower bracket.upper
  · dsimp only [Approximation.SqrtThree.Bracket.bound, Interval.width, Approximation.SqrtThree.Bracket.midpoint]
    exact Approximation.SqrtThree.Bracket.midpoint_sub_lower_eq_half_width bracket.lower bracket.upper

/-- Execute exactly the displayed finite number of bisections. -/
def iterateBisect : Nat → Purelib.Approximation.SqrtThree.Bracket → Purelib.Approximation.SqrtThree.Bracket
  | 0, bracket => bracket
  | count + 1, bracket => Purelib.Approximation.SqrtThree.Bracket.iterateBisect count bracket.bisect

/-- Every finite sequence of square-three bisections refines its initial enclosure. -/
theorem iterateBisect_refines :
    ∀ (count : Nat) (bracket : Approximation.SqrtThree.Bracket),
      Interval.Refines (Approximation.SqrtThree.Bracket.iterateBisect count bracket).bound bracket.bound
  | 0, _ => Refines.refl _
  | count + 1, bracket =>
      (Purelib.Approximation.SqrtThree.Bracket.iterateBisect_refines count bracket.bisect).trans
        bracket.bisect_bound_refines

/-- Finite repeated bisection multiplies the original width by the corresponding half-power. -/
theorem iterateBisect_width :
    ∀ (count : Nat) (bracket : Approximation.SqrtThree.Bracket),
      (Approximation.SqrtThree.Bracket.iterateBisect count bracket).bound.width =
        bracket.bound.width * (1 / 2 : Fraction.Rational) ^ count
  | 0, bracket => by
      dsimp only [Approximation.SqrtThree.Bracket.iterateBisect]
      rewrite [pow_zero]
      exact (Fraction.Field.mul_one_direct _).symm
  | count + 1, bracket => by
      rw [Approximation.SqrtThree.Bracket.iterateBisect, Purelib.Approximation.SqrtThree.Bracket.iterateBisect_width
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
def requiredBisections (bracket : Approximation.SqrtThree.Bracket) (target : Fraction.Rational) : Nat :=
  2 * Geometric.firstQuarterBelow bracket.bound.width 0 target

/-- The computed finite bisection count yields width strictly below a positive target. -/
theorem requiredBisections_accurate (bracket : Approximation.SqrtThree.Bracket)
    {target : Fraction.Rational} (positive : 0 < target) :
    (Approximation.SqrtThree.Bracket.iterateBisect (Approximation.SqrtThree.Bracket.requiredBisections bracket target)
      bracket).bound.width <
      target := by
  let index := Geometric.firstQuarterBelow bracket.bound.width 0 target
  have requested := Geometric.firstQuarterBelow_accurate
    bracket.bound.width
      (Fraction.Order.Arithmetic.sub_nonneg_direct bracket.bound.valid)
      0 target positive
  rw [Geometric.quarterAllowance_eq_mul_pow] at requested
  rw [Approximation.SqrtThree.Bracket.iterateBisect_width, Approximation.SqrtThree.Bracket.requiredBisections,
    Approximation.SqrtThree.Bracket.half_pow_two_mul]
  exact requested

end Bracket

/-- Initial rational square-three bracket `[1,2]`. -/
def initialBracket : Approximation.SqrtThree.Bracket where
  lower := 1
  upper := 2
  lower_nonnegative := by decide
  lower_square_lt := by decide
  upper_square_gt := by decide
  ordered := by decide

set_option genInjectivity false in
/-- A reachable-style state retains an explicit refinement certificate back to the initial rational bracket. -/
structure State where
  /-- The retained square-three bracket at this state. -/ bracket : Approximation.SqrtThree.Bracket
  /-- The retained bracket refines the distinguished initial bracket. -/ refines_initial : Interval.Refines
    bracket.bound Approximation.SqrtThree.initialBracket.bound

constructive_injectivity State

/-- Distinguished initial state. -/
def initialState : State :=
  ⟨Approximation.SqrtThree.initialBracket, Refines.refl _⟩

/-- Request a finite square-three bracket below a positive rational width. -/
def request (state : Approximation.SqrtThree.State) (target : Fraction.Rational) : State :=
  let refined := state.bracket.iterateBisect
    (state.bracket.requiredBisections target)
  ⟨refined,
    (state.bracket.iterateBisect_refines
      (state.bracket.requiredBisections target)).trans state.refines_initial⟩

/-- Concrete arbitrary-accuracy rational enclosure process naming no real number. -/
def process : Approximation.BoundProcess where
  State := Approximation.SqrtThree.State
  bound state := state.bracket.bound
  initial := Approximation.SqrtThree.initialState
  request state target _ := Approximation.SqrtThree.request state target
  request_refines state target _ :=
    state.bracket.iterateBisect_refines
      (state.bracket.requiredBisections target)
  accurate state target positive :=
    state.bracket.requiredBisections_accurate (target := target) positive
  refinesInitial state := state.refines_initial

/-- Every state remains a genuinely positive-width rational bracket; no finite request silently manufactures an exact
rational value. -/
theorem state_width_pos (state : Approximation.SqrtThree.State) :
    0 < (Approximation.SqrtThree.process.bound state).width :=
  state.bracket.bound_width_pos

/-- A finite square-three state cannot be an exact rational singleton enclosure. -/
theorem state_bound_ne_exact (state : Approximation.SqrtThree.State) (candidate : Fraction.Rational) :
    Approximation.SqrtThree.process.bound state ≠ Interval.exact candidate := by
  intro equal
  have widths := congrArg Interval.width equal
  rw [Interval.exact_width] at widths
  exact (Approximation.SqrtThree.state_width_pos state).ne' widths

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
    0 < Purelib.Approximation.SqrtThree.separationTolerance candidate := by
  unfold Approximation.SqrtThree.separationTolerance
  split
  · exact Fraction.Order.Field.div_pos_direct
      (Fraction.Order.Arithmetic.sub_pos_direct (by assumption)) (by decide)
  · have threeLe : (3 : Fraction.Rational) ≤ candidate ^ 2 :=
      Fraction.Order.Arithmetic.le_of_not_gt_direct (by assumption)
    have threeLt : (3 : Fraction.Rational) < candidate ^ 2 :=
      ⟨threeLe, fun reverse =>
        Approximation.SqrtThree.candidate_square_ne_three candidate
          (Fraction.Order.Basic.Compatibility.le_antisymm _ _
            threeLe reverse).symm⟩
    exact Fraction.Order.Field.div_pos_direct
      (Fraction.Order.Arithmetic.sub_pos_direct threeLt) (by decide)

/-- A width below one quarter of a residual remains below that residual after scaling by four. -/
private theorem scaled_width_lt_residual
    {width residual : Fraction.Rational} (small : width < residual / 4) :
    width * 4 < residual := by
  have scaled := Fraction.Order.Arithmetic.mul_lt_mul_of_pos_right_direct
    small (by decide : (0 : Fraction.Rational) < 4)
  calc
    width * 4 < (residual / 4) * 4 := scaled
    _ = residual :=
      Fraction.Field.div_mul_cancel_of_ne residual 4 (by decide)

/-- A sufficiently narrow square-three state excludes the displayed rational candidate. -/
theorem excludes_of_width_lt_separationTolerance
    (state : Approximation.SqrtThree.State) (candidate : Fraction.Rational)
    (small : state.bracket.bound.width < Approximation.SqrtThree.separationTolerance candidate) :
    state.bracket.bound.Excludes candidate := by
  by_cases belowLower : candidate < state.bracket.lower
  · exact Or.inl belowLower
  by_cases aboveUpper : state.bracket.upper < candidate
  · exact Or.inr aboveUpper
  have inside : state.bracket.lower ≤ candidate ∧
      candidate ≤ state.bracket.upper :=
    ⟨Fraction.Order.Arithmetic.le_of_not_gt_direct belowLower,
      Fraction.Order.Arithmetic.le_of_not_gt_direct aboveUpper⟩
  have upperLeTwo : state.bracket.upper ≤ 2 := by
    exact state.refines_initial.upper
  have candidateNonnegative : 0 ≤ candidate :=
    state.bracket.lower_nonnegative.trans inside.1
  by_cases belowSquare : candidate ^ 2 < 3
  · have residualSmall :
        state.bracket.bound.width < (3 - candidate ^ 2) / 4 := by
      rewrite [Approximation.SqrtThree.separationTolerance, if_pos belowSquare] at small
      exact small
    have residualLtDifference :
        3 - candidate ^ 2 <
          state.bracket.upper ^ 2 - candidate ^ 2 :=
      Fraction.Order.Arithmetic.sub_lt_sub_right_direct
        state.bracket.upper_square_gt (candidate ^ 2)
    have firstFactor :
        state.bracket.upper - candidate ≤ state.bracket.bound.width := by
      dsimp only [Approximation.SqrtThree.Bracket.bound, Interval.width]
      exact Fraction.Order.Arithmetic.sub_le_sub_direct le_rfl inside.1
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
      Fraction.Order.Arithmetic.mul_le_mul_direct firstFactor secondFactor
        factorNonnegative state.bracket.bound.width_nonneg
    have residualLtWidth :
        3 - candidate ^ 2 < state.bracket.bound.width * 4 := by
      calc
        3 - candidate ^ 2 <
            state.bracket.upper ^ 2 - candidate ^ 2 := residualLtDifference
        _ = (state.bracket.upper - candidate) *
              (state.bracket.upper + candidate) := by ring1
        _ ≤ state.bracket.bound.width * 4 := productBound
    have widthLtResidual := Approximation.SqrtThree.scaled_width_lt_residual residualSmall
    exact (lt_asymm residualLtWidth widthLtResidual).elim
  · have threeLe : (3 : Fraction.Rational) ≤ candidate ^ 2 :=
      Fraction.Order.Arithmetic.le_of_not_gt_direct belowSquare
    have threeLt : (3 : Fraction.Rational) < candidate ^ 2 :=
      ⟨threeLe, fun reverse =>
        Approximation.SqrtThree.candidate_square_ne_three candidate
          (Fraction.Order.Basic.Compatibility.le_antisymm _ _
            threeLe reverse).symm⟩
    have residualSmall :
        state.bracket.bound.width < (candidate ^ 2 - 3) / 4 := by
      rewrite [Approximation.SqrtThree.separationTolerance, if_neg belowSquare] at small
      exact small
    have residualLtDifference :
        candidate ^ 2 - 3 <
          candidate ^ 2 - state.bracket.lower ^ 2 :=
      Fraction.Order.Arithmetic.sub_lt_sub_left_direct
        state.bracket.lower_square_lt (candidate ^ 2)
    have firstFactor :
        candidate - state.bracket.lower ≤ state.bracket.bound.width := by
      dsimp only [Approximation.SqrtThree.Bracket.bound, Interval.width]
      exact Fraction.Order.Arithmetic.sub_le_sub_direct inside.2 le_rfl
    have lowerLeTwo : state.bracket.lower ≤ 2 :=
      (Fraction.Order.Arithmetic.le_of_lt_direct
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
      Fraction.Order.Arithmetic.mul_le_mul_direct firstFactor secondFactor
        factorNonnegative state.bracket.bound.width_nonneg
    have residualLtWidth :
        candidate ^ 2 - 3 < state.bracket.bound.width * 4 := by
      calc
        candidate ^ 2 - 3 <
            candidate ^ 2 - state.bracket.lower ^ 2 := residualLtDifference
        _ = (candidate - state.bracket.lower) *
              (candidate + state.bracket.lower) := by ring1
        _ ≤ state.bracket.bound.width * 4 := productBound
    have widthLtResidual := Approximation.SqrtThree.scaled_width_lt_residual residualSmall
    exact (lt_asymm residualLtWidth widthLtResidual).elim

/-- Refine far enough to exclude one displayed rational candidate. -/
def separate (state : Approximation.SqrtThree.State) (candidate : Fraction.Rational) : State :=
  Approximation.SqrtThree.request state (Approximation.SqrtThree.separationTolerance candidate)

/-- Separating one rational candidate refines the original state enclosure. -/
theorem separate_refines (state : Approximation.SqrtThree.State) (candidate : Fraction.Rational) :
    Interval.Refines (Approximation.SqrtThree.process.bound (Approximation.SqrtThree.separate state candidate))
      (Approximation.SqrtThree.process.bound state) :=
  Approximation.SqrtThree.process.request_refines state (Approximation.SqrtThree.separationTolerance candidate)
    (Approximation.SqrtThree.separationTolerance_pos candidate)

/-- The computed separation state excludes the supplied rational candidate. -/
theorem separate_excludes (state : Approximation.SqrtThree.State) (candidate : Fraction.Rational) :
    (Approximation.SqrtThree.process.bound (Approximation.SqrtThree.separate state candidate)).Excludes candidate := by
  apply Approximation.SqrtThree.excludes_of_width_lt_separationTolerance
  exact Approximation.SqrtThree.process.accurate state (Approximation.SqrtThree.separationTolerance candidate)
    (Approximation.SqrtThree.separationTolerance_pos candidate)

/-- Concrete finite rational-gap protocol for the square-three enclosure. -/
def gapProcess : Approximation.RationalGapProcess where
  process := Approximation.SqrtThree.process
  separate := Approximation.SqrtThree.separate
  separate_refines := Approximation.SqrtThree.separate_refines
  separate_excludes := Approximation.SqrtThree.separate_excludes

end Purelib.Approximation.SqrtThree

end
