import mathlib.Tactic.QuotientFreeRing
import RFAP.Isolation.SafeCandidates

/-!
# Finite dyadic square brackets

A bounded natural recursion selects a positive dyadic rational whose square
lies immediately above a displayed target in `(0, 1)`.  It then performs a
coefficient-computed finite number of rational bisections.  Given any
displayed rational factor greater than one, the returned square lies above
the target and at most that factor times it.  No square root or limiting
object is used.
-/

namespace RFAP.DyadicBracket

abbrev Coordinate := RFAP.ConstructiveFraction.Rational

private theorem half_add_half :
    (1 / 2 : Coordinate) + (1 / 2 : Coordinate) = 1 := by decide

private theorem half_double (value : Coordinate) :
    (1 / 2 : Coordinate) * (value + value) = value := by
  calc
    (1 / 2 : Coordinate) * (value + value) =
        ((1 / 2 : Coordinate) + (1 / 2 : Coordinate)) * value := by ring1
    _ = 1 * value := by rw [half_add_half]
    _ = value := RFAP.ConstructiveFraction.one_mul value

/-- A positive dyadic scale whose square brackets a positive target from
above, within the factor four caused by one halving step. -/
structure Bracket (target : Coordinate) where
  radius : Coordinate
  radiusPositive : 0 < radius
  target_lt_square : target < radius ^ 2
  square_le_four_target : radius ^ 2 <= 4 * target

private def search (target radius : Coordinate) :
    (fuel : Nat) ->
      0 < radius ->
      target < radius ^ 2 ->
      ((1 / 2 : Coordinate) ^ fuel * radius) ^ 2 <= target ->
      Bracket target
  | 0, radiusPositive, above, terminal => by
      have below : radius ^ 2 <= target := by
        simpa only [pow_zero, one_mul] using terminal
      exact ((not_lt_of_ge below) above).elim
  | fuel + 1, radiusPositive, above, terminal => by
      let next := (1 / 2 : Coordinate) * radius
      have nextPositive : 0 < next :=
        RFAP.ConstructiveFraction.mul_pos_direct (by decide) radiusPositive
      if nextAbove : target < next ^ 2 then
        have nextTerminal :
            ((1 / 2 : Coordinate) ^ fuel * next) ^ 2 <= target := by
          calc
            ((1 / 2 : Coordinate) ^ fuel * next) ^ 2 =
                ((1 / 2 : Coordinate) ^ (fuel + 1) * radius) ^ 2 := by
              dsimp only [next]
              rw [pow_succ]
              ring1
            _ <= target := terminal
        exact search target next fuel nextPositive nextAbove nextTerminal
      else
        have nextBelow : next ^ 2 <= target := le_of_not_gt nextAbove
        have scaled : 4 * next ^ 2 <= 4 * target :=
          RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
            nextBelow (by decide)
        exact
          { radius := radius
            radiusPositive := radiusPositive
            target_lt_square := above
            square_le_four_target := by
              have coefficient :
                  (4 : Coordinate) * (1 / 2 : Coordinate) ^ 2 = 1 := by
                decide
              calc
                radius ^ 2 = 4 * next ^ 2 := by
                  dsimp only [next]
                  rw [mul_pow]
                  calc
                    radius ^ 2 = 1 * radius ^ 2 := by ring1
                    _ = (4 * (1 / 2 : Coordinate) ^ 2) * radius ^ 2 := by
                      rw [coefficient]
                    _ = 4 * ((1 / 2 : Coordinate) ^ 2 * radius ^ 2) := by
                      ring1
                _ <= 4 * target := scaled }

/-- Coefficient-computed recursion fuel.  The existing geometric-depth bound
makes a dyadic power small enough before the recursion can run out. -/
def bracketFuel (target : Coordinate) : Nat :=
  RFAP.SafeCandidates.geometricDepth 1 target

/-- Select the first dyadic square above a displayed target in `(0, 1)`.
The construction performs only the bounded recursion `bracketFuel target`;
it does not compute or postulate a square root. -/
def select (target : Coordinate) (targetPositive : 0 < target)
    (target_lt_one : target < 1) : Bracket target := by
  let fuel := bracketFuel target
  let halfPower := (1 / 2 : Coordinate) ^ fuel
  have geometric : (2 / 3 : Coordinate) ^ fuel <= target := by
    have bound :=
      RFAP.SafeCandidates.geometricDepth_sufficient
        (width := (1 : Coordinate)) (epsilon := target)
        (by decide) targetPositive
    simpa only [fuel, bracketFuel, mul_one] using bound
  have halfPowerLeGeometric : halfPower <= (2 / 3 : Coordinate) ^ fuel := by
    exact RFAP.ConstructiveFraction.pow_le_pow_direct
      (show (0 : Coordinate) <= 1 / 2 by decide)
      (show (1 / 2 : Coordinate) <= 2 / 3 by decide) fuel
  have halfPowerLeTarget : halfPower <= target :=
    halfPowerLeGeometric.trans geometric
  have halfPowerNonnegative : 0 <= halfPower :=
    RFAP.ConstructiveFraction.pow_nonneg_direct (by decide) fuel
  have halfPowerLeOne : halfPower <= 1 := by
    simpa only [halfPower, one_pow] using
      (RFAP.ConstructiveFraction.pow_le_pow_direct
        (show (0 : Coordinate) <= 1 / 2 by decide)
        (show (1 / 2 : Coordinate) <= 1 by decide) fuel)
  have terminal : (halfPower * 1) ^ 2 <= target := by
    have squareLe : halfPower ^ 2 <= halfPower := by
      rw [pow_two]
      simpa only [one_mul] using
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
          halfPowerLeOne halfPowerNonnegative
    simpa only [mul_one] using squareLe.trans halfPowerLeTarget
  exact search target 1 fuel (by decide) (by simpa only [one_pow] using
    target_lt_one) (by simpa only [halfPower] using terminal)

/-! ## Accuracy-parameterized finite tightening -/

/-- A positive rational interval bracketing the positive square root of a
displayed target.  This is only finite endpoint data and two checked square
inequalities. -/
structure SquareInterval (target : Coordinate) where
  lower : Coordinate
  upper : Coordinate
  lowerPositive : 0 < lower
  upperPositive : 0 < upper
  lower_le_upper : lower ≤ upper
  lowerSq_le_target : lower ^ 2 ≤ target
  target_lt_upperSq : target < upper ^ 2

/-- The factor-four bracket supplies the initial square interval
`[radius / 2, radius]`. -/
def Bracket.toSquareInterval {target : Coordinate}
    (bracket : Bracket target) : SquareInterval target := by
  let lower := (1 / 2 : Coordinate) * bracket.radius
  have lowerPositive : 0 < lower :=
    RFAP.ConstructiveFraction.mul_pos_direct (by decide)
      bracket.radiusPositive
  have lowerLeUpper : lower ≤ bracket.radius := by
    have scaled :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
        (show (1 / 2 : Coordinate) ≤ 1 by decide)
        bracket.radiusPositive.le
    simpa only [lower, RFAP.ConstructiveFraction.one_mul] using scaled
  have quarterNonnegative : (0 : Coordinate) ≤ 1 / 4 := by decide
  have lowerSqLe : lower ^ 2 ≤ target := by
    have halfSquare : (1 / 2 : Coordinate) ^ 2 = 1 / 4 := by decide
    have scaled :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        bracket.square_le_four_target quarterNonnegative
    calc
      lower ^ 2 = (1 / 2 : Coordinate) ^ 2 * bracket.radius ^ 2 := by
        dsimp only [lower]
        rw [mul_pow]
      _ = (1 / 4 : Coordinate) * bracket.radius ^ 2 := by rw [halfSquare]
      _ ≤ (1 / 4 : Coordinate) * (4 * target) := scaled
      _ = target := by
        have quarterFour : (1 / 4 : Coordinate) * 4 = 1 := by decide
        rw [← RFAP.ConstructiveFraction.mul_assoc, quarterFour,
          RFAP.ConstructiveFraction.one_mul]
  exact
    { lower := lower
      upper := bracket.radius
      lowerPositive := lowerPositive
      upperPositive := bracket.radiusPositive
      lower_le_upper := lowerLeUpper
      lowerSq_le_target := lowerSqLe
      target_lt_upperSq := bracket.target_lt_square }

/-- Rational midpoint of a displayed square interval. -/
def SquareInterval.midpoint {target : Coordinate}
    (interval : SquareInterval target) : Coordinate :=
  RFAP.NormalizedFraction.normalizedMul (1 / 2 : Coordinate)
    (RFAP.NormalizedFraction.normalizedAdd interval.lower interval.upper)

theorem SquareInterval.midpoint_pos {target : Coordinate}
    (interval : SquareInterval target) : 0 < interval.midpoint :=
  (by
    simp only [SquareInterval.midpoint,
      RFAP.NormalizedFraction.normalizedMul_eq,
      RFAP.NormalizedFraction.normalizedAdd_eq]
    exact RFAP.ConstructiveFraction.mul_pos_direct (by decide)
      (RFAP.ConstructiveFraction.add_lt_add_direct
        interval.lowerPositive interval.upperPositive))

theorem SquareInterval.lower_le_midpoint {target : Coordinate}
    (interval : SquareInterval target) : interval.lower ≤ interval.midpoint := by
    have doubled := add_le_add (le_refl interval.lower)
      interval.lower_le_upper
    have halfNonnegative : (0 : Coordinate) ≤ 1 / 2 := by decide
    have scaled :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        doubled halfNonnegative
    calc
      interval.lower = (1 / 2 : Coordinate) *
          (interval.lower + interval.lower) :=
        (half_double interval.lower).symm
      _ ≤ (1 / 2 : Coordinate) *
          (interval.lower + interval.upper) :=
        scaled
      _ = interval.midpoint := by
        symm
        simp only [SquareInterval.midpoint,
          RFAP.NormalizedFraction.normalizedMul_eq,
          RFAP.NormalizedFraction.normalizedAdd_eq]

theorem SquareInterval.midpoint_le_upper {target : Coordinate}
    (interval : SquareInterval target) : interval.midpoint ≤ interval.upper := by
    have doubled := add_le_add interval.lower_le_upper
      (le_refl interval.upper)
    have halfNonnegative : (0 : Coordinate) ≤ 1 / 2 := by decide
    have scaled :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        doubled halfNonnegative
    calc
      interval.midpoint = (1 / 2 : Coordinate) *
          (interval.lower + interval.upper) := by
        simp only [SquareInterval.midpoint,
          RFAP.NormalizedFraction.normalizedMul_eq,
          RFAP.NormalizedFraction.normalizedAdd_eq]
      _ ≤ (1 / 2 : Coordinate) *
          (interval.upper + interval.upper) :=
        scaled
      _ = interval.upper := half_double interval.upper

/-- One exact rational comparison bisects a square interval and retains the
half which still brackets the target. -/
def SquareInterval.bisect {target : Coordinate}
    (interval : SquareInterval target) : SquareInterval target :=
  if midpointAbove : target < interval.midpoint ^ 2 then
    { lower := interval.lower
      upper := interval.midpoint
      lowerPositive := interval.lowerPositive
      upperPositive := interval.midpoint_pos
      lower_le_upper := interval.lower_le_midpoint
      lowerSq_le_target := interval.lowerSq_le_target
      target_lt_upperSq := midpointAbove }
  else
    { lower := interval.midpoint
      upper := interval.upper
      lowerPositive := interval.midpoint_pos
      upperPositive := interval.upperPositive
      lower_le_upper := interval.midpoint_le_upper
      lowerSq_le_target := le_of_not_gt midpointAbove
      target_lt_upperSq := interval.target_lt_upperSq }

/-- Perform exactly the displayed finite number of rational bisections. -/
def SquareInterval.refine {target : Coordinate}
    (interval : SquareInterval target) : Nat → SquareInterval target
  | 0 => interval
  | fuel + 1 => (interval.refine fuel).bisect

theorem SquareInterval.lower_le_bisect_lower {target : Coordinate}
    (interval : SquareInterval target) :
    interval.lower ≤ interval.bisect.lower := by
  by_cases midpointAbove : target < interval.midpoint ^ 2
  · simp only [SquareInterval.bisect, midpointAbove, ↓reduceDIte]
    exact le_rfl
  · simpa only [SquareInterval.bisect, midpointAbove, ↓reduceDIte] using
      interval.lower_le_midpoint

theorem SquareInterval.lower_le_refine_lower {target : Coordinate}
    (interval : SquareInterval target) (fuel : Nat) :
    interval.lower ≤ (interval.refine fuel).lower := by
  induction fuel with
  | zero => exact le_rfl
  | succ fuel inductionHypothesis =>
      exact inductionHypothesis.trans
        (SquareInterval.lower_le_bisect_lower (interval.refine fuel))

theorem SquareInterval.bisect_width {target : Coordinate}
    (interval : SquareInterval target) :
    interval.bisect.upper - interval.bisect.lower =
      (1 / 2 : Coordinate) * (interval.upper - interval.lower) := by
  by_cases midpointAbove : target < interval.midpoint ^ 2
  · simp only [SquareInterval.bisect, midpointAbove, ↓reduceDIte]
    calc
      interval.midpoint -
          interval.lower =
          (1 / 2 : Coordinate) * (interval.lower + interval.upper) -
            (1 / 2 : Coordinate) *
              (interval.lower + interval.lower) := by
        simp only [SquareInterval.midpoint,
          RFAP.NormalizedFraction.normalizedMul_eq,
          RFAP.NormalizedFraction.normalizedAdd_eq]
        rw [half_double interval.lower]
      _ = (1 / 2 : Coordinate) *
          (interval.upper - interval.lower) := by ring1
  · simp only [SquareInterval.bisect, midpointAbove, ↓reduceDIte]
    calc
      interval.upper -
          interval.midpoint =
          (1 / 2 : Coordinate) *
              (interval.upper + interval.upper) -
            (1 / 2 : Coordinate) *
              (interval.lower + interval.upper) := by
        simp only [SquareInterval.midpoint,
          RFAP.NormalizedFraction.normalizedMul_eq,
          RFAP.NormalizedFraction.normalizedAdd_eq]
        rw [half_double interval.upper]
      _ = (1 / 2 : Coordinate) *
          (interval.upper - interval.lower) := by ring1

theorem SquareInterval.refine_width {target : Coordinate}
    (interval : SquareInterval target) (fuel : Nat) :
    (interval.refine fuel).upper - (interval.refine fuel).lower =
      (1 / 2 : Coordinate) ^ fuel *
        (interval.upper - interval.lower) := by
  induction fuel with
  | zero => simp only [SquareInterval.refine, pow_zero, one_mul]
  | succ fuel inductionHypothesis =>
      rw [SquareInterval.refine, SquareInterval.bisect_width,
        inductionHypothesis, pow_succ]
      ring1

/-- A deliberately conservative positive gap whose square expansion is
bounded by the caller's requested factor. -/
def factorGap (factor : Coordinate) : Coordinate :=
  min 1 ((factor - 1) / 3)

theorem factorGap_pos {factor : Coordinate} (factorGreater : 1 < factor) :
    0 < factorGap factor := by
  apply lt_min
  · decide
  · exact RFAP.ConstructiveFraction.div_pos_direct
      (RFAP.ConstructiveFraction.sub_pos_direct factorGreater) (by decide)

theorem one_add_factorGap_sq_le {factor : Coordinate}
    (factorGreater : 1 < factor) :
    (1 + factorGap factor) ^ 2 ≤ factor := by
  let gap := factorGap factor
  have gapPositive : 0 < gap := factorGap_pos factorGreater
  have gapLeOne : gap ≤ 1 := min_le_left _ _
  have gapLeThird : gap ≤ (factor - 1) / 3 := min_le_right _ _
  have gapSqLeGap : gap ^ 2 ≤ gap := by
    rw [pow_two]
    simpa only [RFAP.ConstructiveFraction.one_mul] using
      (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
        gapLeOne gapPositive.le)
  have threeGapLe : 3 * gap ≤ factor - 1 := by
    have scaled :=
      (RFAP.ConstructiveFraction.le_div_iff_pos
        (show (0 : Coordinate) < 3 by decide)).1 gapLeThird
    simpa only [RFAP.ConstructiveFraction.mul_comm] using scaled
  calc
    (1 + factorGap factor) ^ 2 = 1 + 2 * gap + gap ^ 2 := by
      dsimp only [gap]
      ring1
    _ ≤ 1 + 2 * gap + gap := add_le_add (le_refl _) gapSqLeGap
    _ = 1 + 3 * gap := by ring1
    _ ≤ 1 + (factor - 1) := add_le_add (le_refl _) threeGapLe
    _ = factor := by ring1

/-- A positive rational scale whose square is above the target and no more
than the caller's displayed factor times the target. -/
structure AdjustableBracket (target factor : Coordinate) where
  radius : Coordinate
  radiusPositive : 0 < radius
  target_lt_square : target < radius ^ 2
  square_le_factor_target : radius ^ 2 ≤ factor * target

/-- The coefficient-computed number of bisections required for a requested
multiplicative square factor. -/
def refinementFuel (factor : Coordinate) : Nat :=
  RFAP.SafeCandidates.geometricDepth 1 (factorGap factor)

/-- Select a rational square bracket with any displayed factor greater than
one.  The initial dyadic search and the subsequent bisection count are both
bounded before their recursions begin. -/
def selectWithin (target factor : Coordinate) (targetPositive : 0 < target)
    (target_lt_one : target < 1) (factorGreater : 1 < factor) :
    AdjustableBracket target factor := by
  let initial := (select target targetPositive target_lt_one).toSquareInterval
  let fuel := refinementFuel factor
  let interval := initial.refine fuel
  let gap := factorGap factor
  have gapPositive : 0 < gap := factorGap_pos factorGreater
  have halfPowerLeGap : (1 / 2 : Coordinate) ^ fuel ≤ gap := by
    have geometric := RFAP.SafeCandidates.geometricDepth_sufficient
      (width := (1 : Coordinate)) (epsilon := gap)
      (by decide) gapPositive
    change (2 / 3 : Coordinate) ^ fuel * 1 ≤ gap at geometric
    have halfLeTwoThirds : (1 / 2 : Coordinate) ^ fuel ≤
        (2 / 3 : Coordinate) ^ fuel :=
      RFAP.ConstructiveFraction.pow_le_pow_direct
        (show (0 : Coordinate) ≤ 1 / 2 by decide)
        (show (1 / 2 : Coordinate) ≤ 2 / 3 by decide) fuel
    exact halfLeTwoThirds.trans (by
      simpa only [RFAP.ConstructiveFraction.mul_one_direct] using geometric)
  have initialWidth : initial.upper - initial.lower = initial.lower := by
    dsimp only [initial, Bracket.toSquareInterval]
    calc
      (select target targetPositive target_lt_one).radius -
          (1 / 2 : Coordinate) *
            (select target targetPositive target_lt_one).radius =
          (1 / 2 : Coordinate) *
              ((select target targetPositive target_lt_one).radius +
                (select target targetPositive target_lt_one).radius) -
            (1 / 2 : Coordinate) *
              (select target targetPositive target_lt_one).radius := by
        rw [half_double]
      _ = (1 / 2 : Coordinate) *
          (select target targetPositive target_lt_one).radius := by ring1
  have widthLeGapLower : interval.upper - interval.lower ≤
      gap * interval.lower := by
    have lowerNonnegative : 0 ≤ initial.lower := initial.lowerPositive.le
    have scaledPower :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
        halfPowerLeGap lowerNonnegative
    have lowerMonotone : initial.lower ≤ interval.lower :=
      initial.lower_le_refine_lower fuel
    have scaledLower :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        lowerMonotone gapPositive.le
    calc
      interval.upper - interval.lower =
          (1 / 2 : Coordinate) ^ fuel *
            (initial.upper - initial.lower) :=
        initial.refine_width fuel
      _ = (1 / 2 : Coordinate) ^ fuel * initial.lower := by
        rw [initialWidth]
      _ ≤ gap * initial.lower := scaledPower
      _ ≤ gap * interval.lower := scaledLower
  have upperLe : interval.upper ≤ (1 + gap) * interval.lower := by
    calc
      interval.upper = interval.lower +
          (interval.upper - interval.lower) := by ring1
      _ ≤ interval.lower + gap * interval.lower :=
        add_le_add (le_refl _) widthLeGapLower
      _ = (1 + gap) * interval.lower := by ring1
  have upperSqLe : interval.upper ^ 2 ≤
      ((1 + gap) * interval.lower) ^ 2 :=
    RFAP.ConstructiveFraction.pow_le_pow_direct
      interval.upperPositive.le upperLe 2
  have coefficientLe : (1 + gap) ^ 2 ≤ factor := by
    simpa only [gap] using one_add_factorGap_sq_le factorGreater
  have productLe : (1 + gap) ^ 2 * interval.lower ^ 2 ≤
      factor * target :=
    RFAP.ConstructiveFraction.mul_le_mul_direct coefficientLe
      interval.lowerSq_le_target
      (RFAP.ConstructiveFraction.pow_nonneg_direct
        interval.lowerPositive.le 2)
      ((show (0 : Coordinate) ≤ 1 by decide).trans factorGreater.le)
  exact
    { radius := interval.upper
      radiusPositive := interval.upperPositive
      target_lt_square := interval.target_lt_upperSq
      square_le_factor_target := by
        calc
          interval.upper ^ 2 ≤ ((1 + gap) * interval.lower) ^ 2 :=
            upperSqLe
          _ = (1 + gap) ^ 2 * interval.lower ^ 2 := by rw [mul_pow]
          _ ≤ factor * target := productLe }

end RFAP.DyadicBracket
