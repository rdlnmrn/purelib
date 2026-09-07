import mathlib.Tactic.QuotientFreeRing
import CCL.Arithmetic.Enclosures

/-!
# Progressive finite enclosures for constructive CCL arithmetic

An arithmetic input is not a completed complex value.  It is a finite request
procedure: for each positive rational squared-error target it returns one
rational ball meeting that target.  A uniform rational bound on the squared
norm of the returned centres is carried explicitly.  This is the extra finite
side information needed by multiplication.

Division deliberately asks for one further side certificate: a fixed positive
lower bound for every realization of every requested denominator ball.  The
definitions below construct arbitrarily accurate output balls for all four
elementary operations.  Their error budgets are closed rational expressions,
so there is no unbounded search and no completed limit in the interface.
-/

namespace CCL.ProgressiveEnclosures

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev Ball := CCL.ArithmeticEnclosures.Ball

open RFAP.ConstructiveGaussian.Gaussian

/-- A finite-request squared-error oracle with an explicit centre bound. -/
structure Name where
  request : (target : Coordinate) → 0 < target → Ball
  accurate : ∀ (target : Coordinate) (positive : 0 < target),
    (request target positive).radiusSq < target
  centerBound : Coordinate
  centerBound_nonneg : 0 ≤ centerBound
  center_bounded : ∀ (target : Coordinate) (positive : 0 < target),
    normSq (request target positive).center ≤ centerBound

namespace Name

/-- Auxiliary zero-radius name used when a stateful process only needs the
closed request-budget formula associated with known centre bounds. -/
def centerOnly (center : Gaussian) (bound : Coordinate)
    (boundNonnegative : 0 ≤ bound) (bounded : normSq center ≤ bound) : Name where
  request _ _ :=
    { center := center
      radiusSq := 0
      radiusSq_nonneg := le_rfl }
  accurate _ positive := positive
  centerBound := bound
  centerBound_nonneg := boundNonnegative
  center_bounded _ _ := bounded

/-- A fixed positive denominator lower bound, uniformly valid for every
finite request.  It is stronger than centre non-vanishing and is precisely
what makes division constructively continuous on the supplied domain. -/
structure Apart (name : Name) where
  lowerSq : Coordinate
  positive : 0 < lowerSq
  lower : ∀ (target : Coordinate) (targetPositive : 0 < target)
      {value : Gaussian},
    (name.request target targetPositive).Contains value →
      lowerSq ≤ normSq value

namespace Apart

def atRequest {name : Name} (apart : Apart name)
    (target : Coordinate) (targetPositive : 0 < target) :
    CCL.ArithmeticEnclosures.Ball.Apart
      (name.request target targetPositive) :=
  { lowerSq := apart.lowerSq
    positive := apart.positive
    lower := apart.lower target targetPositive }

theorem center_lower {name : Name} (apart : Apart name)
    (target : Coordinate) (targetPositive : 0 < target) :
    apart.lowerSq ≤ normSq (name.request target targetPositive).center :=
  apart.lower target targetPositive
    (name.request target targetPositive).contains_center

end Apart

theorem quarter_pos {target : Coordinate} (positive : 0 < target) :
    0 < target / 4 :=
  RFAP.ConstructiveFraction.div_pos_direct positive (by decide)

/-- Operand accuracy used for addition and subtraction. -/
def additiveInputTarget (target : Coordinate) : Coordinate := target / 4

private theorem two_quarters (target : Coordinate) :
    target / 4 + target / 4 = target / 2 := by
  have twoAsQuotient : (2 / 1 : Coordinate) = 2 := by
    calc
      (2 / 1 : Coordinate) = (2 / 1) * 1 :=
        (RFAP.ConstructiveFraction.mul_one_direct _).symm
      _ = 2 :=
        RFAP.ConstructiveFraction.div_mul_cancel_of_ne 2 1 (by decide)
  calc
    target / 4 + target / 4 = (target / 4) * 2 := by ring1
    _ = (target / 4) * (2 / 1) := by rw [twoAsQuotient]
    _ = (target * 2) / (4 * 1) :=
      RFAP.ConstructiveFraction.div_mul_div_direct target 4 2 1
    _ = (2 * target) / (2 * 2) := by
      rw [RFAP.ConstructiveFraction.mul_comm target 2]
      apply congrArg (fun denominator : Coordinate =>
        (2 * target) / denominator)
      decide
    _ = target / 2 :=
      RFAP.ConstructiveFraction.mul_div_mul_left_direct 2 target 2
        (by decide)

theorem add_radius_lt (left right : Ball) {target : Coordinate}
    (leftSmall : left.radiusSq < additiveInputTarget target)
    (rightSmall : right.radiusSq < additiveInputTarget target) :
    (left.add right).radiusSq < target := by
  unfold additiveInputTarget at leftSmall rightSmall
  change 2 * (left.radiusSq + right.radiusSq) < target
  have sumSmall : left.radiusSq + right.radiusSq < target / 2 := by
    calc
      left.radiusSq + right.radiusSq < target / 4 + target / 4 :=
        RFAP.ConstructiveFraction.add_lt_add_direct leftSmall rightSmall
      _ = target / 2 := two_quarters target
  have scaled := RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
    (by decide : (0 : Coordinate) < 2) sumSmall
  calc
    2 * (left.radiusSq + right.radiusSq) < 2 * (target / 2) := scaled
    _ = target := by
      calc
        2 * (target / 2) = (target / 2) * 2 :=
          RFAP.ConstructiveFraction.mul_comm _ _
        _ = target :=
          RFAP.ConstructiveFraction.div_mul_cancel_of_ne target 2 (by decide)

/-- Progressive addition. -/
def add (left right : Name) : Name where
  request target positive :=
    let inputPositive := quarter_pos positive
    (left.request (additiveInputTarget target) inputPositive).add
      (right.request (additiveInputTarget target) inputPositive)
  accurate target positive := by
    apply add_radius_lt
    · exact left.accurate _ _
    · exact right.accurate _ _
  centerBound := 2 * (left.centerBound + right.centerBound)
  centerBound_nonneg :=
    RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
      (add_nonneg left.centerBound_nonneg right.centerBound_nonneg)
  center_bounded target positive := by
    dsimp only
    exact (normSq_add_le_two _ _).trans
      (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        (add_le_add (left.center_bounded _ _) (right.center_bounded _ _))
        (by decide))

/-- Progressive negation. -/
def neg (name : Name) : Name where
  request target positive := (name.request target positive).neg
  accurate target positive := name.accurate target positive
  centerBound := name.centerBound
  centerBound_nonneg := name.centerBound_nonneg
  center_bounded target positive := by
    change normSq (-(name.request target positive).center) ≤ name.centerBound
    rw [normSq_neg]
    exact name.center_bounded target positive

/-- Progressive subtraction. -/
def sub (left right : Name) : Name := left.add right.neg

/-- A strictly positive coefficient bounding the multiplication error after
both operand radii have been replaced by a common number below one. -/
def multiplicativeCoefficient (left right : Name) : Coordinate :=
  4 * (left.centerBound + right.centerBound) + 2

theorem multiplicativeCoefficient_pos (left right : Name) :
    0 < multiplicativeCoefficient left right := by
  unfold multiplicativeCoefficient
  have nonnegative : 0 ≤ 4 * (left.centerBound + right.centerBound) :=
    RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
      (add_nonneg left.centerBound_nonneg right.centerBound_nonneg)
  exact lt_of_lt_of_le (by decide : (0 : Coordinate) < 2)
    (le_add_of_nonneg_left nonnegative)

/-- Operand squared-error request used for multiplication.  The extra
`target` in the denominator makes this number strictly below one without a
minimum operation. -/
def multiplicativeInputTarget (left right : Name)
    (target : Coordinate) : Coordinate :=
  target / (target + multiplicativeCoefficient left right)

theorem multiplicativeInputTarget_pos (left right : Name)
    {target : Coordinate} (positive : 0 < target) :
    0 < multiplicativeInputTarget left right target := by
  apply RFAP.ConstructiveFraction.div_pos_direct positive
  exact add_pos positive (multiplicativeCoefficient_pos left right)

theorem multiplicativeInputTarget_lt_one (left right : Name)
    {target : Coordinate} (positive : 0 < target) :
    multiplicativeInputTarget left right target < 1 := by
  apply (RFAP.ConstructiveFraction.div_lt_iff_pos
    (add_pos positive (multiplicativeCoefficient_pos left right))).2
  calc
    target < target + multiplicativeCoefficient left right :=
      lt_add_of_pos_right target (multiplicativeCoefficient_pos left right)
    _ = 1 * (target + multiplicativeCoefficient left right) := by ring1

private theorem quotient_mul_reorder
    (numerator denominator factor : Coordinate) :
    numerator / denominator * factor =
      (numerator * factor) / denominator := by
  change (numerator * denominator⁻¹) * factor =
    (numerator * factor) * denominator⁻¹
  calc
    (numerator * denominator⁻¹) * factor =
        numerator * (denominator⁻¹ * factor) :=
      _root_.mul_assoc _ _ _
    _ = numerator * (factor * denominator⁻¹) := by
      rw [RFAP.ConstructiveFraction.mul_comm denominator⁻¹ factor]
    _ = (numerator * factor) * denominator⁻¹ :=
      (_root_.mul_assoc _ _ _).symm

theorem multiplicative_budget_lt (left right : Name)
    {target : Coordinate} (positive : 0 < target) :
    multiplicativeInputTarget left right target *
        multiplicativeCoefficient left right < target := by
  let coefficient := multiplicativeCoefficient left right
  have coefficientPositive : 0 < coefficient :=
    multiplicativeCoefficient_pos left right
  have denominatorPositive : 0 < target + coefficient :=
    add_pos positive coefficientPositive
  change target / (target + coefficient) * coefficient < target
  calc
    target / (target + coefficient) * coefficient =
        (target * coefficient) / (target + coefficient) := by
      exact quotient_mul_reorder _ _ _
    _ < target := by
      apply (RFAP.ConstructiveFraction.div_lt_iff_pos denominatorPositive).2
      have coefficientLt : coefficient < target + coefficient := by
        calc
          coefficient = 0 + coefficient := (zero_add coefficient).symm
          _ < target + coefficient :=
            RFAP.ConstructiveFraction.add_lt_add_right_direct positive
              coefficient
      have scaled := RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
        positive coefficientLt
      exact scaled

theorem mul_radius_lt (leftName rightName : Name) (left right : Ball)
    {target : Coordinate} (positive : 0 < target)
    (leftSmall :
      left.radiusSq < multiplicativeInputTarget leftName rightName target)
    (rightSmall :
      right.radiusSq < multiplicativeInputTarget leftName rightName target)
    (leftCenter : normSq left.center ≤ leftName.centerBound)
    (rightCenter : normSq right.center ≤ rightName.centerBound) :
    (left.mul right).radiusSq < target := by
  let epsilon := multiplicativeInputTarget leftName rightName target
  have epsilonPositive : 0 < epsilon :=
    multiplicativeInputTarget_pos leftName rightName positive
  have epsilonLtOne : epsilon < 1 :=
    multiplicativeInputTarget_lt_one leftName rightName positive
  have firstRight :
      normSq left.center * right.radiusSq ≤
        leftName.centerBound * epsilon := by
    calc
      normSq left.center * right.radiusSq ≤
          leftName.centerBound * right.radiusSq :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
          leftCenter right.radiusSq_nonneg
      _ ≤ leftName.centerBound * epsilon :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          rightSmall.le leftName.centerBound_nonneg
  have productError : left.radiusSq * right.radiusSq < epsilon * epsilon := by
    calc
      left.radiusSq * right.radiusSq ≤ left.radiusSq * epsilon :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          rightSmall.le left.radiusSq_nonneg
      _ < epsilon * epsilon :=
        RFAP.ConstructiveFraction.mul_lt_mul_of_pos_right_direct
          leftSmall epsilonPositive
  unfold CCL.ArithmeticEnclosures.Ball.mul
  have firstOrder :
      left.radiusSq * normSq right.center +
          normSq left.center * right.radiusSq ≤
        epsilon *
          (rightName.centerBound + leftName.centerBound) := by
    have firstLeft :
        left.radiusSq * normSq right.center ≤
          epsilon * rightName.centerBound := by
      calc
        left.radiusSq * normSq right.center ≤
            left.radiusSq * rightName.centerBound :=
          RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
            rightCenter left.radiusSq_nonneg
        _ ≤ epsilon * rightName.centerBound :=
          RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
            leftSmall.le rightName.centerBound_nonneg
    exact (add_le_add firstLeft firstRight).trans_eq (by ring1)
  have total :
      4 * (left.radiusSq * normSq right.center +
          normSq left.center * right.radiusSq) +
          2 * (left.radiusSq * right.radiusSq) <
        epsilon * multiplicativeCoefficient leftName rightName := by
    calc
      4 * (left.radiusSq * normSq right.center +
          normSq left.center * right.radiusSq) +
          2 * (left.radiusSq * right.radiusSq) <
          4 * (epsilon *
            (rightName.centerBound + leftName.centerBound)) +
            2 * (epsilon * epsilon) :=
        add_lt_add_of_le_of_lt
          (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
            firstOrder (by decide))
          (RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
            (by decide) productError)
      _ < epsilon * multiplicativeCoefficient leftName rightName := by
        unfold multiplicativeCoefficient
        have epsilonSqLt : epsilon * epsilon < epsilon * 1 :=
          RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
            epsilonPositive epsilonLtOne
        have scaledEpsilonSq :=
          RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
            (by decide : (0 : Coordinate) < 2) epsilonSqLt
        calc
          4 * (epsilon *
              (rightName.centerBound + leftName.centerBound)) +
              2 * (epsilon * epsilon) <
              4 * (epsilon *
                (rightName.centerBound + leftName.centerBound)) +
                2 * (epsilon * 1) :=
            add_lt_add_right scaledEpsilonSq _
          _ = epsilon *
              (4 * (leftName.centerBound + rightName.centerBound) + 2) := by
            ring1
  exact total.trans (multiplicative_budget_lt leftName rightName positive)

/-- Progressive multiplication. -/
def mul (left right : Name) : Name where
  request target positive :=
    let inputPositive := multiplicativeInputTarget_pos left right positive
    (left.request (multiplicativeInputTarget left right target) inputPositive).mul
      (right.request (multiplicativeInputTarget left right target) inputPositive)
  accurate target positive := by
    apply mul_radius_lt left right
    · exact positive
    · exact left.accurate _ _
    · exact right.accurate _ _
    · exact left.center_bounded _ _
    · exact right.center_bounded _ _
  centerBound := left.centerBound * right.centerBound
  centerBound_nonneg :=
    RFAP.ConstructiveFraction.mul_nonneg_direct left.centerBound_nonneg
      right.centerBound_nonneg
  center_bounded target positive := by
    change normSq
      ((left.request (multiplicativeInputTarget left right target) _).center *
        (right.request (multiplicativeInputTarget left right target) _).center) ≤
      left.centerBound * right.centerBound
    rw [normSq_mul]
    exact RFAP.ConstructiveFraction.mul_le_mul_direct
      (left.center_bounded _ _) (right.center_bounded _ _)
      (normSq_nonneg _) left.centerBound_nonneg

/-! ## Apartness-certified progressive division -/

/-- Common operand request used by division.  Its denominator deliberately
contains twice the coefficient actually needed, leaving a strict rational
margin in the final estimate. -/
def divisionInputTarget (left right : Name) (lowerSq : Coordinate)
    (target : Coordinate) : Coordinate :=
  (target * (lowerSq * lowerSq)) /
    (4 * (left.centerBound + right.centerBound + 1))

theorem divisionDenominator_pos (left right : Name) :
    0 < 4 * (left.centerBound + right.centerBound + 1) := by
  apply RFAP.ConstructiveFraction.mul_pos_direct (by decide)
  exact add_pos_of_nonneg_of_pos
    (add_nonneg left.centerBound_nonneg right.centerBound_nonneg) (by decide)

theorem divisionInputTarget_pos (left right : Name) (lowerSq : Coordinate)
    (lowerPositive : 0 < lowerSq) {target : Coordinate}
    (positive : 0 < target) :
    0 < divisionInputTarget left right lowerSq target := by
  apply RFAP.ConstructiveFraction.div_pos_direct
  · exact RFAP.ConstructiveFraction.mul_pos_direct positive
      (RFAP.ConstructiveFraction.mul_pos_direct lowerPositive lowerPositive)
  · exact divisionDenominator_pos left right

theorem division_budget_lt (left right : Name) (lowerSq : Coordinate)
    (lowerPositive : 0 < lowerSq) {target : Coordinate}
    (positive : 0 < target) :
    2 * divisionInputTarget left right lowerSq target *
        (left.centerBound + right.centerBound) <
      target * (lowerSq * lowerSq) := by
  let epsilon := divisionInputTarget left right lowerSq target
  let sumBound := left.centerBound + right.centerBound
  let denominator : Coordinate := 4 * (sumBound + 1)
  have epsilonPositive : 0 < epsilon :=
    divisionInputTarget_pos left right lowerSq lowerPositive positive
  have denominatorPositive : 0 < denominator := by
    exact divisionDenominator_pos left right
  have coefficientLt : 2 * sumBound < denominator := by
    dsimp only [denominator, sumBound]
    have sumNonnegative :
        0 ≤ left.centerBound + right.centerBound :=
      add_nonneg left.centerBound_nonneg right.centerBound_nonneg
    apply RFAP.ConstructiveFraction.lt_of_add_lt_add_right_direct
      (c := -(2 * (left.centerBound + right.centerBound)))
    calc
      2 * (left.centerBound + right.centerBound) +
          -(2 * (left.centerBound + right.centerBound)) = 0 := by ring1
      _ < 2 * (left.centerBound + right.centerBound) + 4 :=
        add_pos_of_nonneg_of_pos
          (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
            sumNonnegative)
          (by decide)
      _ = 4 * (left.centerBound + right.centerBound + 1) +
          -(2 * (left.centerBound + right.centerBound)) := by ring1
  have scaled := RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
    epsilonPositive coefficientLt
  calc
    2 * epsilon * sumBound = epsilon * (2 * sumBound) := by ring1
    _ < epsilon * denominator := scaled
    _ = target * (lowerSq * lowerSq) := by
      dsimp only [epsilon, denominator, sumBound, divisionInputTarget]
      exact RFAP.ConstructiveFraction.div_mul_cancel_of_ne _ _
        (divisionDenominator_pos left right).ne'

theorem div_radius_lt (leftName rightName : Name) (lowerSq : Coordinate)
    (lowerPositive : 0 < lowerSq) (left right : Ball)
    {target : Coordinate} (positive : 0 < target)
    (leftSmall :
      left.radiusSq <
        divisionInputTarget leftName rightName lowerSq target)
    (rightSmall :
      right.radiusSq <
        divisionInputTarget leftName rightName lowerSq target)
    (leftCenter : normSq left.center ≤ leftName.centerBound)
    (rightCenter : normSq right.center ≤ rightName.centerBound)
    (rightApart :
      CCL.ArithmeticEnclosures.Ball.Apart right)
    (sameLower : rightApart.lowerSq = lowerSq) :
    (left.div right rightApart).radiusSq < target := by
  let epsilon :=
    divisionInputTarget leftName rightName lowerSq target
  let centerNorm := normSq right.center
  let numerator :=
    2 * (left.radiusSq * centerNorm +
      normSq left.center * right.radiusSq)
  let lowerProduct := lowerSq * lowerSq
  have epsilonPositive : 0 < epsilon :=
    divisionInputTarget_pos leftName rightName lowerSq lowerPositive positive
  have rightCenterLower : lowerSq ≤ centerNorm := by
    rw [← sameLower]
    exact rightApart.lower right.contains_center
  have centerPositive : 0 < centerNorm :=
    lowerPositive.trans_le rightCenterLower
  have lowerProductPositive : 0 < lowerProduct :=
    RFAP.ConstructiveFraction.mul_pos_direct lowerPositive lowerPositive
  have numeratorNonnegative : 0 ≤ numerator := by
    exact RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
      (add_nonneg
        (RFAP.ConstructiveFraction.mul_nonneg_direct left.radiusSq_nonneg
          (normSq_nonneg right.center))
        (RFAP.ConstructiveFraction.mul_nonneg_direct
          (normSq_nonneg left.center) right.radiusSq_nonneg))
  have numeratorUpper : numerator ≤
      2 * epsilon * (leftName.centerBound + rightName.centerBound) := by
    dsimp only [numerator, centerNorm]
    have leftTerm : left.radiusSq * normSq right.center ≤
        epsilon * rightName.centerBound :=
      RFAP.ConstructiveFraction.mul_le_mul_direct leftSmall.le rightCenter
        (normSq_nonneg right.center) epsilonPositive.le
    have rightTerm : normSq left.center * right.radiusSq ≤
        leftName.centerBound * epsilon :=
      RFAP.ConstructiveFraction.mul_le_mul_direct leftCenter rightSmall.le
        right.radiusSq_nonneg leftName.centerBound_nonneg
    calc
      2 * (left.radiusSq * normSq right.center +
          normSq left.center * right.radiusSq) ≤
          2 * (epsilon * rightName.centerBound +
            leftName.centerBound * epsilon) :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          (add_le_add leftTerm rightTerm) (by decide)
      _ = 2 * epsilon *
          (leftName.centerBound + rightName.centerBound) := by ring1
  have numeratorStrict : numerator < target * lowerProduct :=
    numeratorUpper.trans_lt
      (division_budget_lt leftName rightName lowerSq lowerPositive positive)
  have denominatorLower : lowerProduct ≤
      lowerSq * centerNorm :=
    RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
      rightCenterLower lowerPositive.le
  have denominatorPositive : 0 < lowerSq * centerNorm :=
    RFAP.ConstructiveFraction.mul_pos_direct lowerPositive centerPositive
  change
    (2 * (left.radiusSq * normSq right.center +
      normSq left.center * right.radiusSq)) /
      (rightApart.lowerSq * normSq right.center) < target
  rw [sameLower]
  calc
    numerator / (lowerSq * centerNorm) ≤
        numerator / lowerProduct :=
      RFAP.ConstructiveFraction.div_le_div_of_nonneg_left_direct
        numeratorNonnegative lowerProductPositive denominatorLower
    _ < target :=
      (RFAP.ConstructiveFraction.div_lt_iff_pos lowerProductPositive).2
        numeratorStrict

/-- Progressive apartness-certified division. -/
def div (left right : Name) (apart : Apart right) : Name where
  request target positive :=
    let inputPositive := divisionInputTarget_pos left right apart.lowerSq
      apart.positive positive
    let leftBall :=
      left.request (divisionInputTarget left right apart.lowerSq target)
        inputPositive
    let rightBall :=
      right.request (divisionInputTarget left right apart.lowerSq target)
        inputPositive
    leftBall.div rightBall
      (apart.atRequest (divisionInputTarget left right apart.lowerSq target)
        inputPositive)
  accurate target positive := by
    apply div_radius_lt left right apart.lowerSq apart.positive
    · exact positive
    · exact left.accurate _ _
    · exact right.accurate _ _
    · exact left.center_bounded _ _
    · exact right.center_bounded _ _
    · rfl
  centerBound := left.centerBound / apart.lowerSq
  centerBound_nonneg :=
    RFAP.ConstructiveFraction.div_nonneg_direct left.centerBound_nonneg
      apart.positive.le
  center_bounded target positive := by
    let inputPositive := divisionInputTarget_pos left right apart.lowerSq
      apart.positive positive
    let leftBall :=
      left.request (divisionInputTarget left right apart.lowerSq target)
        inputPositive
    let rightBall :=
      right.request (divisionInputTarget left right apart.lowerSq target)
        inputPositive
    let rightApart := apart.atRequest
      (divisionInputTarget left right apart.lowerSq target) inputPositive
    have rightCenterLower : apart.lowerSq ≤ normSq rightBall.center :=
      apart.center_lower _ _
    have rightCenterPositive : 0 < normSq rightBall.center :=
      apart.positive.trans_le rightCenterLower
    have rightCenterNonzero : rightBall.center ≠ 0 := by
      intro centerZero
      rw [centerZero, normSq_zero] at rightCenterPositive
      exact (lt_irrefl _ rightCenterPositive).elim
    change normSq (leftBall.center / rightBall.center) ≤
      left.centerBound / apart.lowerSq
    rw [normSq_div _ _ rightCenterNonzero]
    calc
      normSq leftBall.center * (normSq rightBall.center)⁻¹ =
          normSq leftBall.center / normSq rightBall.center := rfl
      _ ≤ left.centerBound / normSq rightBall.center := by
        apply (RFAP.ConstructiveFraction.div_le_iff_pos
          rightCenterPositive).2
        calc
          normSq leftBall.center ≤ left.centerBound :=
            left.center_bounded _ _
          _ = (left.centerBound / normSq rightBall.center) *
              normSq rightBall.center :=
            (RFAP.ConstructiveFraction.div_mul_cancel_of_ne
              left.centerBound _ rightCenterPositive.ne').symm
      _ ≤ left.centerBound / apart.lowerSq :=
        RFAP.ConstructiveFraction.div_le_div_of_nonneg_left_direct
          left.centerBound_nonneg apart.positive rightCenterLower

/-! ## Request-level soundness -/

theorem request_contains_add (left right : Name) {target : Coordinate}
    (positive : 0 < target) {x y : Gaussian}
    (xInside :
      (left.request (additiveInputTarget target) (quarter_pos positive)).Contains x)
    (yInside :
      (right.request (additiveInputTarget target) (quarter_pos positive)).Contains y) :
    (left.add right).request target positive |>.Contains (x + y) :=
  CCL.ArithmeticEnclosures.Ball.contains_add xInside yInside

theorem request_contains_mul (left right : Name) {target : Coordinate}
    (positive : 0 < target) {x y : Gaussian}
    (xInside : (left.request (multiplicativeInputTarget left right target)
      (multiplicativeInputTarget_pos left right positive)).Contains x)
    (yInside : (right.request (multiplicativeInputTarget left right target)
      (multiplicativeInputTarget_pos left right positive)).Contains y) :
    (left.mul right).request target positive |>.Contains (x * y) :=
  CCL.ArithmeticEnclosures.Ball.contains_mul xInside yInside

theorem request_contains_div (left right : Name) (apart : Apart right)
    {target : Coordinate} (positive : 0 < target) {x y : Gaussian}
    (xInside : (left.request
      (divisionInputTarget left right apart.lowerSq target)
      (divisionInputTarget_pos left right apart.lowerSq apart.positive
        positive)).Contains x)
    (yInside : (right.request
      (divisionInputTarget left right apart.lowerSq target)
      (divisionInputTarget_pos left right apart.lowerSq apart.positive
        positive)).Contains y) :
    (left.div right apart).request target positive |>.Contains (x / y) :=
  CCL.ArithmeticEnclosures.Ball.contains_div
    (apart.atRequest _ _) xInside yInside

end Name

/-! ## Stateful progressive names

`Name` above isolates the quantitative calculation.  The stateful interface
below also records persistence.  Its `Possible` predicate is local to one
explicit finite state; it does not select a completed value.  Refinement only
has to prove that every later finite possibility was already an earlier one.
This is the invariant needed to keep previously emitted CCL digits valid.
-/

/-- A progressive finite enclosure process. -/
structure Process where
  State : Type
  ball : State → Ball
  Possible : State → Gaussian → Prop
  witness : (state : State) → { value : Gaussian // Possible state value }
  possible_inside : ∀ {state : State} {value : Gaussian},
    Possible state value → (ball state).Contains value
  refine : (state : State) → (target : Coordinate) → 0 < target → State
  refine_persists : ∀ (state : State) (target : Coordinate)
      (positive : 0 < target) {value : Gaussian},
    Possible (refine state target positive) value → Possible state value
  accurate : ∀ (state : State) (target : Coordinate)
      (positive : 0 < target),
    (ball (refine state target positive)).radiusSq < target
  centerBound : Coordinate
  centerBound_nonneg : 0 ≤ centerBound
  center_bounded : ∀ (state : State), normSq (ball state).center ≤ centerBound

namespace Process

/-- Uniform apartness of every finite denominator enclosure. -/
structure Apart (process : Process) where
  lowerSq : Coordinate
  positive : 0 < lowerSq
  lower : ∀ (state : process.State) {value : Gaussian},
    (process.ball state).Contains value → lowerSq ≤ normSq value

namespace Apart

def atState {process : Process} (apart : Apart process)
    (state : process.State) :
    CCL.ArithmeticEnclosures.Ball.Apart (process.ball state) :=
  { lowerSq := apart.lowerSq
    positive := apart.positive
    lower := apart.lower state }

end Apart

/-- A finite exact rational name.  This constructor is intentionally about a
displayed Gaussian rational, not an asserted non-rational completed root. -/
def exact (value : Gaussian) : Process where
  State := Unit
  ball _ :=
    { center := value
      radiusSq := 0
      radiusSq_nonneg := le_rfl }
  Possible _ candidate := candidate = value
  witness _ := ⟨value, rfl⟩
  possible_inside := by
    intro _state candidate equal
    subst candidate
    unfold CCL.ArithmeticEnclosures.Ball.Contains
    rw [RFAP.ConstructiveGaussian.Gaussian.sub_self, normSq_zero]
  refine _ _ _ := ()
  refine_persists := by
    intro _state _target _positive candidate equal
    exact equal
  accurate := by
    intro _state _target positive
    exact positive
  centerBound := normSq value
  centerBound_nonneg := normSq_nonneg value
  center_bounded := by intro _state; exact le_rfl

/-- Stateful progressive addition. -/
def add (left right : Process) : Process where
  State := left.State × right.State
  ball state := (left.ball state.1).add (right.ball state.2)
  Possible state value := ∃ x y : Gaussian,
    left.Possible state.1 x ∧ right.Possible state.2 y ∧ value = x + y
  witness state := by
    rcases left.witness state.1 with ⟨x, xPossible⟩
    rcases right.witness state.2 with ⟨y, yPossible⟩
    exact ⟨x + y, x, y, xPossible, yPossible, rfl⟩
  possible_inside := by
    rintro state value ⟨x, y, xPossible, yPossible, rfl⟩
    exact CCL.ArithmeticEnclosures.Ball.contains_add
      (left.possible_inside xPossible) (right.possible_inside yPossible)
  refine state target positive :=
    let inputPositive := Name.quarter_pos positive
    (left.refine state.1 (Name.additiveInputTarget target) inputPositive,
      right.refine state.2 (Name.additiveInputTarget target) inputPositive)
  refine_persists := by
    rintro state target positive value
      ⟨x, y, xPossible, yPossible, equal⟩
    exact ⟨x, y,
      left.refine_persists state.1 _ _ xPossible,
      right.refine_persists state.2 _ _ yPossible,
      equal⟩
  accurate := by
    intro state target positive
    apply Name.add_radius_lt
    · exact left.accurate state.1 _ _
    · exact right.accurate state.2 _ _
  centerBound := 2 * (left.centerBound + right.centerBound)
  centerBound_nonneg :=
    RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
      (add_nonneg left.centerBound_nonneg right.centerBound_nonneg)
  center_bounded := by
    intro state
    exact (normSq_add_le_two _ _).trans
      (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        (add_le_add (left.center_bounded state.1)
          (right.center_bounded state.2)) (by decide))

/-- Stateful progressive negation. -/
def neg (process : Process) : Process where
  State := process.State
  ball state := (process.ball state).neg
  Possible state value := ∃ source : Gaussian,
    process.Possible state source ∧ value = -source
  witness state := by
    rcases process.witness state with ⟨source, possible⟩
    exact ⟨-source, source, possible, rfl⟩
  possible_inside := by
    rintro state value ⟨source, possible, rfl⟩
    exact CCL.ArithmeticEnclosures.Ball.contains_neg
      (process.possible_inside possible)
  refine := process.refine
  refine_persists := by
    rintro state target positive value ⟨source, possible, equal⟩
    exact ⟨source, process.refine_persists state target positive possible, equal⟩
  accurate := process.accurate
  centerBound := process.centerBound
  centerBound_nonneg := process.centerBound_nonneg
  center_bounded := by
    intro state
    change normSq (-(process.ball state).center) ≤ process.centerBound
    rw [normSq_neg]
    exact process.center_bounded state

/-- Stateful progressive subtraction. -/
def sub (left right : Process) : Process := left.add right.neg

/-- Stateful progressive multiplication. -/
def mul (left right : Process) : Process where
  State := left.State × right.State
  ball state := (left.ball state.1).mul (right.ball state.2)
  Possible state value := ∃ x y : Gaussian,
    left.Possible state.1 x ∧ right.Possible state.2 y ∧ value = x * y
  witness state := by
    rcases left.witness state.1 with ⟨x, xPossible⟩
    rcases right.witness state.2 with ⟨y, yPossible⟩
    exact ⟨x * y, x, y, xPossible, yPossible, rfl⟩
  possible_inside := by
    rintro state value ⟨x, y, xPossible, yPossible, rfl⟩
    exact CCL.ArithmeticEnclosures.Ball.contains_mul
      (left.possible_inside xPossible) (right.possible_inside yPossible)
  refine state target positive :=
    -- The input target depends only on the stored global centre bounds.
    -- Zero-centred names avoid evaluating both current balls merely to
    -- discard their centres when that target is computed.
    let leftName := Name.centerOnly 0 left.centerBound
      left.centerBound_nonneg (by
        rw [normSq_zero]
        exact left.centerBound_nonneg)
    let rightName := Name.centerOnly 0 right.centerBound
      right.centerBound_nonneg (by
        rw [normSq_zero]
        exact right.centerBound_nonneg)
    let inputTarget := Name.multiplicativeInputTarget leftName rightName target
    let inputPositive := Name.multiplicativeInputTarget_pos
      leftName rightName positive
    (left.refine state.1 inputTarget inputPositive,
      right.refine state.2 inputTarget inputPositive)
  refine_persists := by
    rintro state target positive value
      ⟨x, y, xPossible, yPossible, equal⟩
    exact ⟨x, y,
      left.refine_persists state.1 _ _ xPossible,
      right.refine_persists state.2 _ _ yPossible,
      equal⟩
  accurate := by
    intro state target positive
    let leftName := Name.centerOnly (left.ball state.1).center
      left.centerBound left.centerBound_nonneg (left.center_bounded state.1)
    let rightName := Name.centerOnly (right.ball state.2).center
      right.centerBound right.centerBound_nonneg (right.center_bounded state.2)
    apply Name.mul_radius_lt leftName rightName
    · exact positive
    · exact left.accurate state.1 _ _
    · exact right.accurate state.2 _ _
    · exact left.center_bounded _
    · exact right.center_bounded _
  centerBound := left.centerBound * right.centerBound
  centerBound_nonneg :=
    RFAP.ConstructiveFraction.mul_nonneg_direct left.centerBound_nonneg
      right.centerBound_nonneg
  center_bounded := by
    intro state
    change normSq
      ((left.ball state.1).center * (right.ball state.2).center) ≤
      left.centerBound * right.centerBound
    rw [normSq_mul]
    exact RFAP.ConstructiveFraction.mul_le_mul_direct
      (left.center_bounded state.1) (right.center_bounded state.2)
      (normSq_nonneg _) left.centerBound_nonneg

/-- Stateful progressive division on an explicitly apart denominator. -/
def div (left right : Process) (apart : Apart right) : Process where
  State := left.State × right.State
  ball state := (left.ball state.1).div (right.ball state.2)
    (apart.atState state.2)
  Possible state value := ∃ x y : Gaussian,
    left.Possible state.1 x ∧ right.Possible state.2 y ∧ value = x / y
  witness state := by
    rcases left.witness state.1 with ⟨x, xPossible⟩
    rcases right.witness state.2 with ⟨y, yPossible⟩
    exact ⟨x / y, x, y, xPossible, yPossible, rfl⟩
  possible_inside := by
    rintro state value ⟨x, y, xPossible, yPossible, rfl⟩
    exact CCL.ArithmeticEnclosures.Ball.contains_div
      (apart.atState state.2) (left.possible_inside xPossible)
      (right.possible_inside yPossible)
  refine state target positive :=
    -- As for multiplication, the target uses only the global bounds, so
    -- evaluating the two current balls here would be redundant finite work.
    let leftName := Name.centerOnly 0 left.centerBound
      left.centerBound_nonneg (by
        rw [normSq_zero]
        exact left.centerBound_nonneg)
    let rightName := Name.centerOnly 0 right.centerBound
      right.centerBound_nonneg (by
        rw [normSq_zero]
        exact right.centerBound_nonneg)
    let inputTarget := Name.divisionInputTarget
      leftName rightName apart.lowerSq target
    let inputPositive := Name.divisionInputTarget_pos
      leftName rightName apart.lowerSq apart.positive positive
    (left.refine state.1 inputTarget inputPositive,
      right.refine state.2 inputTarget inputPositive)
  refine_persists := by
    rintro state target positive value
      ⟨x, y, xPossible, yPossible, equal⟩
    exact ⟨x, y,
      left.refine_persists state.1 _ _ xPossible,
      right.refine_persists state.2 _ _ yPossible,
      equal⟩
  accurate := by
    intro state target positive
    let leftName := Name.centerOnly (left.ball state.1).center
      left.centerBound left.centerBound_nonneg (left.center_bounded state.1)
    let rightName := Name.centerOnly (right.ball state.2).center
      right.centerBound right.centerBound_nonneg (right.center_bounded state.2)
    apply Name.div_radius_lt leftName rightName apart.lowerSq apart.positive
    · exact positive
    · exact left.accurate state.1 _ _
    · exact right.accurate state.2 _ _
    · exact left.center_bounded _
    · exact right.center_bounded _
    · rfl
  centerBound := left.centerBound / apart.lowerSq
  centerBound_nonneg :=
    RFAP.ConstructiveFraction.div_nonneg_direct left.centerBound_nonneg
      apart.positive.le
  center_bounded := by
    intro state
    have centerLower : apart.lowerSq ≤ normSq (right.ball state.2).center :=
      apart.lower state.2 (right.ball state.2).contains_center
    have centerPositive : 0 < normSq (right.ball state.2).center :=
      apart.positive.trans_le centerLower
    have centerNonzero : (right.ball state.2).center ≠ 0 := by
      intro centerZero
      rw [centerZero, normSq_zero] at centerPositive
      exact (lt_irrefl _ centerPositive).elim
    change normSq
      ((left.ball state.1).center / (right.ball state.2).center) ≤
      left.centerBound / apart.lowerSq
    rw [normSq_div _ _ centerNonzero]
    calc
      normSq (left.ball state.1).center *
          (normSq (right.ball state.2).center)⁻¹ =
          normSq (left.ball state.1).center /
            normSq (right.ball state.2).center := rfl
      _ ≤ left.centerBound / normSq (right.ball state.2).center := by
        apply (RFAP.ConstructiveFraction.div_le_iff_pos centerPositive).2
        calc
          normSq (left.ball state.1).center ≤ left.centerBound :=
            left.center_bounded state.1
          _ = (left.centerBound / normSq (right.ball state.2).center) *
              normSq (right.ball state.2).center :=
            (RFAP.ConstructiveFraction.div_mul_cancel_of_ne
              left.centerBound _ centerPositive.ne').symm
      _ ≤ left.centerBound / apart.lowerSq :=
        RFAP.ConstructiveFraction.div_le_div_of_nonneg_left_direct
          left.centerBound_nonneg apart.positive centerLower

end Process

end CCL.ProgressiveEnclosures
