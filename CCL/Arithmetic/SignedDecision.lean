import CCL.Arithmetic.ResidualDecision

/-!
# Finite signed imaginary-coordinate decisions

A prescribed squared error gives a positive, negative, or near-boundary
whole-ball certificate. All margins and comparisons are rational. The last
case is a tolerance-relative result, not equality with the real axis.
-/

namespace CCL.SignedDecision

abbrev Q := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev Ball := CCL.ArithmeticEnclosures.Ball

open RFAP.ConstructiveFraction

theorem quarter_positive {delta : Q} (positive : 0 < delta) : 0 < delta / 4 :=
  div_pos_direct positive (by decide)

theorem target_positive {delta : Q} (positive : 0 < delta) : 0 < delta ^ 2 / 16 :=
  div_pos_direct (pow_pos_direct positive 2) (by decide)

theorem quarter_square (delta : Q) : (delta / 4) ^ 2 = delta ^ 2 / 16 := by
  rw [pow_two, div_mul_div_direct, ← pow_two, show (4 : Q) * 4 = 16 by decide]

theorem half_eq_two_quarters (delta : Q) : delta / 2 = (delta / 4) * 2 := by
  apply mul_right_cancel_of_ne (c := (2 : Q)) (by decide)
  rw [div_mul_cancel_of_ne _ _ (by decide : (2 : Q) ≠ 0)]
  calc
    delta = (delta / 4) * 4 := (div_mul_cancel_of_ne _ _ (by decide : (4 : Q) ≠ 0)).symm
    _ = ((delta / 4) * 2) * 2 := by ring1

/-- The coordinate error is bounded without extracting a square root. -/
theorem deviation {ball : Ball} {delta : Q} (positive : 0 < delta)
    (fine : ball.radiusSq < delta ^ 2 / 16) {value : Gaussian}
    (inside : ball.Contains value) :
    -(delta / 4) ≤ value.im - ball.center.im ∧ value.im - ball.center.im ≤ delta / 4 := by
  change (value.re - ball.center.re) ^ 2 + (value.im - ball.center.im) ^ 2 ≤
    ball.radiusSq at inside
  have squareLe : (value.im - ball.center.im) ^ 2 ≤ ball.radiusSq :=
    (le_add_of_nonneg_left (sq_nonneg_direct (value.re - ball.center.re))).trans inside
  have bounded : (value.im - ball.center.im) ^ 2 ≤ (delta / 4) ^ 2 := by
    rw [quarter_square]
    exact (squareLe.trans_lt fine).le
  exact ⟨neg_le_of_sq_le_sq_direct (quarter_positive positive).le bounded,
    le_of_sq_le_sq_direct (quarter_positive positive).le bounded⟩

theorem positive_lower {ball : Ball} {delta : Q} (positive : 0 < delta)
    (fine : ball.radiusSq < delta ^ 2 / 16) (high : delta / 2 < ball.center.im)
    {value : Gaussian} (inside : ball.Contains value) : delta / 4 ≤ value.im := by
  have centerLower : (delta / 4) * 2 ≤ ball.center.im := by
    rw [← half_eq_two_quarters]
    exact high.le
  calc
    delta / 4 = -(delta / 4) + (delta / 4) * 2 := by ring1
    _ ≤ (value.im - ball.center.im) + ball.center.im :=
      add_le_add (deviation positive fine inside).1 centerLower
    _ = value.im := by ring1

theorem negative_upper {ball : Ball} {delta : Q} (positive : 0 < delta)
    (fine : ball.radiusSq < delta ^ 2 / 16) (low : ball.center.im < -(delta / 2))
    {value : Gaussian} (inside : ball.Contains value) : value.im ≤ -(delta / 4) := by
  have centerUpper : ball.center.im ≤ -((delta / 4) * 2) := by
    rw [← half_eq_two_quarters]
    exact low.le
  calc
    value.im = (value.im - ball.center.im) + ball.center.im := by ring1
    _ ≤ delta / 4 + -((delta / 4) * 2) :=
      add_le_add (deviation positive fine inside).2 centerUpper
    _ = -(delta / 4) := by ring1

theorem near_bounds {ball : Ball} {delta : Q} (positive : 0 < delta)
    (fine : ball.radiusSq < delta ^ 2 / 16)
    (notHigh : ¬ delta / 2 < ball.center.im) (notLow : ¬ ball.center.im < -(delta / 2))
    {value : Gaussian} (inside : ball.Contains value) : -delta < value.im ∧ value.im < delta := by
  have centerLower : -((delta / 4) * 2) ≤ ball.center.im := by
    rw [← half_eq_two_quarters]
    exact le_of_not_gt notLow
  have centerUpper : ball.center.im ≤ (delta / 4) * 2 := by
    rw [← half_eq_two_quarters]
    exact le_of_not_gt notHigh
  have tripleLess : (delta / 4) * 3 < delta := by
    calc
      (delta / 4) * 3 < (delta / 4) * 4 :=
        mul_lt_mul_of_pos_left_direct (quarter_positive positive) (by decide)
      _ = delta := div_mul_cancel_of_ne _ _ (by decide : (4 : Q) ≠ 0)
  constructor
  · apply (neg_lt_neg_direct tripleLess).trans_le
    calc
      -((delta / 4) * 3) = -(delta / 4) + -((delta / 4) * 2) := by ring1
      _ ≤ (value.im - ball.center.im) + ball.center.im :=
        add_le_add (deviation positive fine inside).1 centerLower
      _ = value.im := by ring1
  · apply lt_of_le_of_lt _ tripleLess
    calc
      value.im = (value.im - ball.center.im) + ball.center.im := by ring1
      _ ≤ delta / 4 + (delta / 4) * 2 :=
        add_le_add (deviation positive fine inside).2 centerUpper
      _ = (delta / 4) * 3 := by ring1

/-- Compatibility with the existing squared-half-height positivity test. -/
theorem positive_test {ball : Ball} {delta : Q} (positive : 0 < delta)
    (fine : ball.radiusSq < delta ^ 2 / 16) (high : delta / 2 < ball.center.im) :
    0 < ball.center.im ∧ ball.radiusSq < (ball.center.im / 2) ^ 2 := by
  have halfPositive : 0 < delta / 2 := div_pos_direct positive (by decide)
  have quarterLe : delta / 4 ≤ ball.center.im / 2 := by
    apply (le_div_iff_pos (by decide : (0 : Q) < 2)).2
    rw [← half_eq_two_quarters]
    exact high.le
  constructor
  · exact halfPositive.trans high
  · have squares := pow_le_pow_direct (quarter_positive positive).le quarterLe 2
    rw [quarter_square] at squares
    exact fine.trans_le squares

/-- All three cases carry whole-ball evidence. `near` is not a zero verdict. -/
inductive Decision (ball : Ball) (delta : Q) : Type
  | positive (high : delta / 2 < ball.center.im)
      (lower : ∀ {value : Gaussian}, ball.Contains value → delta / 4 ≤ value.im)
  | negative (low : ball.center.im < -(delta / 2))
      (upper : ∀ {value : Gaussian}, ball.Contains value → value.im ≤ -(delta / 4))
  | near (bounds : ∀ {value : Gaussian}, ball.Contains value →
      -delta < value.im ∧ value.im < delta)

def decide (ball : Ball) (delta : Q) (positive : 0 < delta)
    (fine : ball.radiusSq < delta ^ 2 / 16) : Decision ball delta :=
  if high : delta / 2 < ball.center.im then
    .positive high (positive_lower positive fine high)
  else if low : ball.center.im < -(delta / 2) then
    .negative low (negative_upper positive fine low)
  else .near (near_bounds positive fine high low)

/-- A small executable observation for regression clients. -/
def Decision.tag {ball : Ball} {delta : Q} : Decision ball delta → Nat
  | .positive _ _ => 1
  | .negative _ _ => 2
  | .near _ => 0

end CCL.SignedDecision
