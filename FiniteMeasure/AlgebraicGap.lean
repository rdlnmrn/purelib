import mathlib.Tactic.QuotientFreeRing
import FiniteMeasure.Gap
import FiniteMeasure.Geometric

/-!
# A concrete rational enclosure process for the square-three gap

The process below repeatedly bisects rational brackets whose lower endpoint
has square below three and whose upper endpoint has square above three.  The
finite geometric search computes enough bisections for any positive rational
request.  No square root or completed real is defined.
-/

namespace FiniteMeasure.SqrtThree

open FiniteMeasure

/-- Finite rational data straddling the positive square-three gap. -/
structure Bracket where
  lower : Coordinate
  upper : Coordinate
  lower_nonnegative : 0 ≤ lower
  lower_square_lt : lower ^ 2 < 3
  upper_square_gt : 3 < upper ^ 2
  ordered : lower < upper

namespace Bracket

/-- Forget the square certificates while retaining the rational enclosure. -/
def bound (bracket : Bracket) : Bound where
  lower := bracket.lower
  upper := bracket.upper
  valid := RFAP.ConstructiveFraction.le_of_lt_direct bracket.ordered

theorem bound_width_pos (bracket : Bracket) : 0 < bracket.bound.width := by
  dsimp only [Bound.width, bound]
  exact RFAP.ConstructiveFraction.sub_pos_direct bracket.ordered

theorem upper_nonnegative (bracket : Bracket) : 0 ≤ bracket.upper :=
  RFAP.ConstructiveFraction.le_trans 0 bracket.lower bracket.upper
    bracket.lower_nonnegative
    (RFAP.ConstructiveFraction.le_of_lt_direct bracket.ordered)

/-- Rational midpoint. -/
def midpoint (bracket : Bracket) : Coordinate :=
  (bracket.lower + bracket.upper) / 2

theorem lower_lt_midpoint (bracket : Bracket) :
    bracket.lower < bracket.midpoint := by
  apply (RFAP.ConstructiveFraction.lt_div_iff_pos
    (by decide : (0 : Coordinate) < 2)).2
  calc
    bracket.lower * 2 = bracket.lower + bracket.lower := by ring1
    _ < bracket.lower + bracket.upper :=
      RFAP.ConstructiveFraction.add_lt_add_left_direct
        bracket.ordered bracket.lower

theorem midpoint_lt_upper (bracket : Bracket) :
    bracket.midpoint < bracket.upper := by
  apply (RFAP.ConstructiveFraction.div_lt_iff_pos
    (by decide : (0 : Coordinate) < 2)).2
  calc
    bracket.lower + bracket.upper <
        bracket.upper + bracket.upper :=
      RFAP.ConstructiveFraction.add_lt_add_right_direct
        bracket.ordered bracket.upper
    _ = bracket.upper * 2 := by ring1

theorem midpoint_nonnegative (bracket : Bracket) :
    0 ≤ bracket.midpoint :=
  RFAP.ConstructiveFraction.div_nonneg_direct
    (add_nonneg bracket.lower_nonnegative bracket.upper_nonnegative)
    (by decide)

/-- One exact rational bisection, choosing the side whose endpoint squares
still straddle three.  `square_ne_three` makes the branch strict. -/
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
        have threeLe : (3 : Coordinate) ≤ bracket.midpoint ^ 2 :=
          RFAP.ConstructiveFraction.le_of_not_gt_direct below
        exact ⟨threeLe, fun reverse =>
          RFAP.ConstructiveFraction.square_ne_three bracket.midpoint
            (RFAP.ConstructiveFraction.le_antisymm _ _
              threeLe reverse).symm⟩
      ordered := bracket.lower_lt_midpoint }

theorem bisect_bound_refines (bracket : Bracket) :
    Bound.Refines bracket.bisect.bound bracket.bound := by
  unfold bisect
  split
  · exact ⟨RFAP.ConstructiveFraction.le_of_lt_direct
      bracket.lower_lt_midpoint, le_rfl⟩
  · exact ⟨le_rfl, RFAP.ConstructiveFraction.le_of_lt_direct
      bracket.midpoint_lt_upper⟩

private theorem div_two_eq_mul_half (value : Coordinate) :
    value / 2 = value * (1 / 2) := by
  change value * (2 : Coordinate)⁻¹ =
    value * ((1 : Coordinate) * (2 : Coordinate)⁻¹)
  rw [RFAP.ConstructiveFraction.one_mul]

private theorem upper_sub_midpoint_eq_half_width
    (lower upper : Coordinate) :
    upper - (lower + upper) / 2 = (upper - lower) * (1 / 2) := by
  have numerator :
      upper * 2 - (lower + upper) * 1 = upper - lower := by
    ring1
  calc
    upper - (lower + upper) / 2 =
        upper / 1 - (lower + upper) / 2 := by
      change upper - (lower + upper) / 2 =
        upper * (1 : Coordinate)⁻¹ - (lower + upper) / 2
      rw [show (1 : Coordinate)⁻¹ = 1 by decide,
        RFAP.ConstructiveFraction.mul_one_direct]
    _ = (upper * 2 - (lower + upper) * 1) / (1 * 2) :=
      RFAP.ConstructiveFraction.div_sub_div_direct upper 1
        (lower + upper) 2 (by decide) (by decide)
    _ = (upper - lower) / 2 := by
      rw [numerator, RFAP.ConstructiveFraction.one_mul]
    _ = (upper - lower) * (1 / 2) := div_two_eq_mul_half _

private theorem midpoint_sub_lower_eq_half_width
    (lower upper : Coordinate) :
    (lower + upper) / 2 - lower = (upper - lower) * (1 / 2) := by
  have numerator :
      (lower + upper) * 1 - lower * 2 = upper - lower := by
    ring1
  calc
    (lower + upper) / 2 - lower =
        (lower + upper) / 2 - lower / 1 := by
      change (lower + upper) / 2 - lower =
        (lower + upper) / 2 - lower * (1 : Coordinate)⁻¹
      rw [show (1 : Coordinate)⁻¹ = 1 by decide,
        RFAP.ConstructiveFraction.mul_one_direct]
    _ = ((lower + upper) * 1 - lower * 2) / (2 * 1) :=
      RFAP.ConstructiveFraction.div_sub_div_direct (lower + upper) 2
        lower 1 (by decide) (by decide)
    _ = (upper - lower) / 2 := by
      rw [numerator, RFAP.ConstructiveFraction.mul_one_direct]
    _ = (upper - lower) * (1 / 2) := div_two_eq_mul_half _

theorem bisect_width (bracket : Bracket) :
    bracket.bisect.bound.width = bracket.bound.width * (1 / 2) := by
  unfold bisect
  split
  · dsimp only [bound, Bound.width, midpoint]
    exact upper_sub_midpoint_eq_half_width bracket.lower bracket.upper
  · dsimp only [bound, Bound.width, midpoint]
    exact midpoint_sub_lower_eq_half_width bracket.lower bracket.upper

/-- Execute exactly the displayed finite number of bisections. -/
def iterateBisect : Nat → Bracket → Bracket
  | 0, bracket => bracket
  | count + 1, bracket => iterateBisect count bracket.bisect

theorem iterateBisect_refines :
    ∀ (count : Nat) (bracket : Bracket),
      Bound.Refines (iterateBisect count bracket).bound bracket.bound
  | 0, _ => Bound.Refines.refl _
  | count + 1, bracket =>
      (iterateBisect_refines count bracket.bisect).trans
        bracket.bisect_bound_refines

theorem iterateBisect_width :
    ∀ (count : Nat) (bracket : Bracket),
      (iterateBisect count bracket).bound.width =
        bracket.bound.width * (1 / 2 : Coordinate) ^ count
  | 0, bracket => by
      simp only [iterateBisect, pow_zero, mul_one]
  | count + 1, bracket => by
      rw [iterateBisect, iterateBisect_width count bracket.bisect,
        bracket.bisect_width, pow_succ]
      ring1

private theorem half_pow_two_mul (index : Nat) :
    (1 / 2 : Coordinate) ^ (2 * index) = (1 / 4 : Coordinate) ^ index := by
  calc
    (1 / 2 : Coordinate) ^ (2 * index) =
        ((1 / 2 : Coordinate) ^ 2) ^ index := by rw [pow_mul]
    _ = (1 / 4 : Coordinate) ^ index := by
      have halfSquare : (1 / 2 : Coordinate) ^ 2 = 1 / 4 := by decide
      rw [halfSquare]

/-- Computed finite bisection count for one positive rational width request. -/
def requiredBisections (bracket : Bracket) (target : Coordinate) : Nat :=
  2 * Geometric.firstQuarterBelow bracket.bound.width 0 target

theorem requiredBisections_accurate (bracket : Bracket)
    {target : Coordinate} (positive : 0 < target) :
    (iterateBisect (requiredBisections bracket target) bracket).bound.width <
      target := by
  let index := Geometric.firstQuarterBelow bracket.bound.width 0 target
  have requested := Geometric.firstQuarterBelow_accurate
    bracket.bound.width
      (RFAP.ConstructiveFraction.sub_nonneg_direct bracket.bound.valid)
      0 target positive
  rw [Geometric.quarterAllowance_eq_mul_pow] at requested
  rw [iterateBisect_width, requiredBisections, half_pow_two_mul]
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

/-- A reachable-style state retains an explicit refinement certificate back
to the initial rational bracket. -/
structure State where
  bracket : Bracket
  refines_initial : Bound.Refines bracket.bound initialBracket.bound

/-- Distinguished initial state. -/
def initialState : State :=
  ⟨initialBracket, Bound.Refines.refl _⟩

/-- Request a finite square-three bracket below a positive rational width. -/
def request (state : State) (target : Coordinate) : State :=
  let refined := state.bracket.iterateBisect
    (state.bracket.requiredBisections target)
  ⟨refined,
    (state.bracket.iterateBisect_refines
      (state.bracket.requiredBisections target)).trans state.refines_initial⟩

/-- Concrete arbitrary-accuracy rational enclosure process naming no real
number. -/
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

/-- Every state remains a genuinely positive-width rational bracket; no
finite request silently manufactures an exact rational value. -/
theorem state_width_pos (state : State) :
    0 < (process.bound state).width :=
  state.bracket.bound_width_pos

theorem state_bound_ne_exact (state : State) (candidate : Coordinate) :
    process.bound state ≠ Bound.exact candidate := by
  intro equal
  have widths := congrArg Bound.width equal
  rw [Bound.exact_width] at widths
  exact (state_width_pos state).ne' widths

/-- The rational square obstruction is independently decidable at every
displayed candidate. -/
theorem candidate_square_ne_three (candidate : Coordinate) :
    candidate ^ 2 ≠ 3 :=
  RFAP.ConstructiveFraction.square_ne_three candidate

/-! ## Candidate-by-candidate rational separation -/

/-- Positive rational width small enough to distinguish a displayed
candidate by its nonzero square residual. -/
def separationTolerance (candidate : Coordinate) : Coordinate :=
  if candidate ^ 2 < 3 then (3 - candidate ^ 2) / 4
  else (candidate ^ 2 - 3) / 4

theorem separationTolerance_pos (candidate : Coordinate) :
    0 < separationTolerance candidate := by
  unfold separationTolerance
  split
  · exact RFAP.ConstructiveFraction.div_pos_direct
      (RFAP.ConstructiveFraction.sub_pos_direct (by assumption)) (by decide)
  · have threeLe : (3 : Coordinate) ≤ candidate ^ 2 :=
      RFAP.ConstructiveFraction.le_of_not_gt_direct (by assumption)
    have threeLt : (3 : Coordinate) < candidate ^ 2 :=
      ⟨threeLe, fun reverse =>
        candidate_square_ne_three candidate
          (RFAP.ConstructiveFraction.le_antisymm _ _
            threeLe reverse).symm⟩
    exact RFAP.ConstructiveFraction.div_pos_direct
      (RFAP.ConstructiveFraction.sub_pos_direct threeLt) (by decide)

private theorem scaled_width_lt_residual
    {width residual : Coordinate} (small : width < residual / 4) :
    width * 4 < residual := by
  have scaled := RFAP.ConstructiveFraction.mul_lt_mul_of_pos_right_direct
    small (by decide : (0 : Coordinate) < 4)
  calc
    width * 4 < (residual / 4) * 4 := scaled
    _ = residual :=
      RFAP.ConstructiveFraction.div_mul_cancel_of_ne residual 4 (by decide)

/-- A sufficiently narrow square-three state excludes the displayed rational
candidate. -/
theorem excludes_of_width_lt_separationTolerance
    (state : State) (candidate : Coordinate)
    (small : state.bracket.bound.width < separationTolerance candidate) :
    state.bracket.bound.Excludes candidate := by
  by_cases belowLower : candidate < state.bracket.lower
  · exact Or.inl belowLower
  by_cases aboveUpper : state.bracket.upper < candidate
  · exact Or.inr aboveUpper
  have inside : state.bracket.lower ≤ candidate ∧
      candidate ≤ state.bracket.upper :=
    ⟨RFAP.ConstructiveFraction.le_of_not_gt_direct belowLower,
      RFAP.ConstructiveFraction.le_of_not_gt_direct aboveUpper⟩
  have upperLeTwo : state.bracket.upper ≤ 2 := by
    exact state.refines_initial.upper
  have candidateNonnegative : 0 ≤ candidate :=
    state.bracket.lower_nonnegative.trans inside.1
  by_cases belowSquare : candidate ^ 2 < 3
  · have residualSmall :
        state.bracket.bound.width < (3 - candidate ^ 2) / 4 := by
      simpa only [separationTolerance, belowSquare, ↓reduceIte] using small
    have residualLtDifference :
        3 - candidate ^ 2 <
          state.bracket.upper ^ 2 - candidate ^ 2 :=
      RFAP.ConstructiveFraction.sub_lt_sub_right_direct
        state.bracket.upper_square_gt (candidate ^ 2)
    have firstFactor :
        state.bracket.upper - candidate ≤ state.bracket.bound.width := by
      dsimp only [Bracket.bound, Bound.width]
      exact RFAP.ConstructiveFraction.sub_le_sub_direct le_rfl inside.1
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
      RFAP.ConstructiveFraction.mul_le_mul_direct firstFactor secondFactor
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
  · have threeLe : (3 : Coordinate) ≤ candidate ^ 2 :=
      RFAP.ConstructiveFraction.le_of_not_gt_direct belowSquare
    have threeLt : (3 : Coordinate) < candidate ^ 2 :=
      ⟨threeLe, fun reverse =>
        candidate_square_ne_three candidate
          (RFAP.ConstructiveFraction.le_antisymm _ _
            threeLe reverse).symm⟩
    have residualSmall :
        state.bracket.bound.width < (candidate ^ 2 - 3) / 4 := by
      simpa only [separationTolerance, belowSquare, ↓reduceIte] using small
    have residualLtDifference :
        candidate ^ 2 - 3 <
          candidate ^ 2 - state.bracket.lower ^ 2 :=
      RFAP.ConstructiveFraction.sub_lt_sub_left_direct
        state.bracket.lower_square_lt (candidate ^ 2)
    have firstFactor :
        candidate - state.bracket.lower ≤ state.bracket.bound.width := by
      dsimp only [Bracket.bound, Bound.width]
      exact RFAP.ConstructiveFraction.sub_le_sub_direct inside.2 le_rfl
    have lowerLeTwo : state.bracket.lower ≤ 2 :=
      (RFAP.ConstructiveFraction.le_of_lt_direct
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
      RFAP.ConstructiveFraction.mul_le_mul_direct firstFactor secondFactor
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
def separate (state : State) (candidate : Coordinate) : State :=
  request state (separationTolerance candidate)

theorem separate_refines (state : State) (candidate : Coordinate) :
    Bound.Refines (process.bound (separate state candidate))
      (process.bound state) :=
  process.request_refines state (separationTolerance candidate)
    (separationTolerance_pos candidate)

theorem separate_excludes (state : State) (candidate : Coordinate) :
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

end FiniteMeasure.SqrtThree
