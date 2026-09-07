import CCL.Arithmetic.ResidualDecision
import CCL.Transcendental.LogAnchorSeeds

/-!
# Decidable finite safety for anchored complex-log charts

For a rational chart factor and one displayed rational input ball, this module
computes conservative numerator and denominator balls for

`factor * z - 1` and `factor * z + 1`.

The denominator ball must pass the existing square-root-free centre-separation
test.  Dividing the two finite balls by that certificate must then pass an
indexed weighted norm bound strictly below `1/9`.  The weight increases along
the intended refinement schedule: its centre coefficient approaches one while
the shrinking enclosure error is still paid explicitly.  These exact rational
checks imply the target-side fields of `SafeOverlapExtension` after rebasing
the target process to the tested state.

Failure is deliberately only failure of this sufficient finite test.  It is
not evidence that no logarithm chart exists.
-/

namespace CCL.LogChartSafety

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev Ball := CCL.ArithmeticEnclosures.Ball
abbrev CoherentNamed := CCL.ProgressiveCoherence.CoherentNamed
abbrev AnchoredChart := CCL.LogBranchCalculus.AnchoredChart
abbrev OverlapWitness := CCL.LogBranchGeometry.OverlapWitness
abbrev SafeOverlapExtension := CCL.LogBranchGeometry.SafeOverlapExtension

open RFAP.ConstructiveGaussian.Gaussian

/-- The exact zero-radius enclosure of one Gaussian rational. -/
def exactBall (value : Gaussian) : Ball where
  center := value
  radiusSq := 0
  radiusSq_nonneg := le_rfl

theorem exactBall_contains (value : Gaussian) :
    (exactBall value).Contains value := by
  unfold CCL.ArithmeticEnclosures.Ball.Contains exactBall
  rw [RFAP.ConstructiveGaussian.Gaussian.sub_self, normSq_zero]

/-- Conservative enclosure of `factor * z`. -/
def scaledBall (factor : Gaussian) (input : Ball) : Ball :=
  (exactBall factor).mul input

/-- Conservative enclosure of `factor * z - 1`. -/
def numeratorBall (factor : Gaussian) (input : Ball) : Ball :=
  (scaledBall factor input).sub (exactBall 1)

/-- Conservative enclosure of `factor * z + 1`. -/
def denominatorBall (factor : Gaussian) (input : Ball) : Ball :=
  (scaledBall factor input).add (exactBall 1)

theorem scaledBall_contains {factor value : Gaussian} {input : Ball}
    (inside : input.Contains value) :
    (scaledBall factor input).Contains (factor * value) :=
  CCL.ArithmeticEnclosures.Ball.contains_mul
    (exactBall_contains factor) inside

theorem numeratorBall_contains {factor value : Gaussian} {input : Ball}
    (inside : input.Contains value) :
    (numeratorBall factor input).Contains (factor * value - 1) :=
  CCL.ArithmeticEnclosures.Ball.contains_sub
    (scaledBall_contains inside) (exactBall_contains 1)

theorem denominatorBall_contains {factor value : Gaussian} {input : Ball}
    (inside : input.Contains value) :
    (denominatorBall factor input).Contains (factor * value + 1) :=
  CCL.ArithmeticEnclosures.Ball.contains_add
    (scaledBall_contains inside) (exactBall_contains 1)

/-- Exact rational sufficient test for separating every transformed
denominator candidate from zero. -/
def DenominatorSeparated (factor : Gaussian) (input : Ball) : Prop :=
  2 * (denominatorBall factor input).radiusSq <
    normSq (denominatorBall factor input).center

instance denominatorSeparatedDecidable (factor : Gaussian) (input : Ball) :
    Decidable (DenominatorSeparated factor input) := by
  unfold DenominatorSeparated
  infer_instance

/-- The finite denominator certificate obtained from the rational separation
test. -/
def denominatorApart {factor : Gaussian} {input : Ball}
    (separated : DenominatorSeparated factor input) :
    CCL.ArithmeticEnclosures.Ball.Apart (denominatorBall factor input) :=
  CCL.ResidualDecision.apartOfCenter
    (denominatorBall factor input) separated

/-- Conservative enclosure of the reduced chart argument. -/
def reducedBall {factor : Gaussian} {input : Ball}
    (separated : DenominatorSeparated factor input) : Ball :=
  (numeratorBall factor input).div (denominatorBall factor input)
    (denominatorApart separated)

/-- Positive rational weight used by the indexed square-root-free triangle
bound.  Increasing the index makes the coefficient of the centre norm tend to
one. -/
def weight (index : Nat) : Coordinate := index + 1

theorem weight_positive (index : Nat) : 0 < weight index := by
  unfold weight
  simpa only [Nat.cast_add, Nat.cast_one] using
    (RFAP.ConstructiveFraction.natCast_pos_direct
      (n := index + 1) (Nat.zero_lt_succ index))

/-- General square-root-free weighted triangle inequality.  Multiplying the
difference by `scale` leaves exactly `normSq (scale * u - v)`. -/
theorem normSq_add_le_weighted (scale : Coordinate)
    (scalePositive : 0 < scale) (u v : Gaussian) :
    normSq (u + v) ≤
      (scale + 1) * normSq u + ((scale + 1) / scale) * normSq v := by
  let difference :=
    (scale + 1) * normSq u + ((scale + 1) / scale) * normSq v -
      normSq (u + v)
  have coefficient : scale * ((scale + 1) / scale) = scale + 1 := by
    calc
      scale * ((scale + 1) / scale) =
          ((scale + 1) / scale) * scale :=
        RFAP.ConstructiveFraction.mul_comm _ _
      _ = scale + 1 :=
        RFAP.ConstructiveFraction.div_mul_cancel_of_ne
          (scale + 1) scale scalePositive.ne'
  have scaledIdentity :
      scale * difference =
        (scale * u.re - v.re) ^ 2 + (scale * u.im - v.im) ^ 2 := by
    calc
      scale * difference =
          scale * (scale + 1) * normSq u +
            (scale * ((scale + 1) / scale)) * normSq v -
            scale * normSq (u + v) := by
        dsimp only [difference]
        ring1
      _ = scale * (scale + 1) * normSq u +
            (scale + 1) * normSq v - scale * normSq (u + v) := by
        rw [coefficient]
      _ = (scale * u.re - v.re) ^ 2 +
            (scale * u.im - v.im) ^ 2 := by
        simp only [normSq, add_re, add_im]
        ring1
  have scaledNonnegative : 0 ≤ scale * difference := by
    rw [scaledIdentity]
    exact add_nonneg
      (RFAP.ConstructiveFraction.sq_nonneg_direct _)
      (RFAP.ConstructiveFraction.sq_nonneg_direct _)
  have differenceNonnegative : 0 ≤ difference := by
    apply RFAP.ConstructiveFraction.le_of_mul_le_mul_right_direct
      (c := scale) _ scalePositive
    calc
      0 * scale = 0 := by ring1
      _ ≤ scale * difference := scaledNonnegative
      _ = difference * scale := RFAP.ConstructiveFraction.mul_comm _ _
  apply RFAP.ConstructiveFraction.le_of_add_le_add_right_direct
    (c := -normSq (u + v))
  calc
    normSq (u + v) + -normSq (u + v) = 0 := by ring1
    _ ≤ difference := differenceNonnegative
    _ = ((scale + 1) * normSq u +
          ((scale + 1) / scale) * normSq v) +
        -normSq (u + v) := by
      dsimp only [difference]
      ring1

/-- Executable upper norm-square bound for every point admitted by a ball. -/
def weightedUpper (index : Nat) (ball : Ball) : Coordinate :=
  (weight index + 1) * ball.radiusSq +
    ((weight index + 1) / weight index) * normSq ball.center

/-- Passing the indexed weighted bound places every admitted point strictly
inside the requested norm-square target. -/
theorem normSq_lt_of_weightedUpper {index : Nat} {ball : Ball}
    {target : Coordinate} (small : weightedUpper index ball < target)
    {value : Gaussian} (inside : ball.Contains value) :
    normSq value < target := by
  have decomposition : value = (value - ball.center) + ball.center := by
    apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
      simp only [sub_re, sub_im, add_re, add_im] <;> ring1
  rw [decomposition]
  exact (normSq_add_le_weighted (weight index) (weight_positive index)
      (value - ball.center) ball.center).trans_lt
    (lt_of_le_of_lt
      (add_le_add
        (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          inside
          (add_nonneg (weight_positive index).le (by decide)))
        le_rfl)
      small)

/-- Exact rational sufficient test for the reduced quotient ball at one
weight/refinement index. -/
def ReducedSmall {factor : Gaussian} {input : Ball}
    (separated : DenominatorSeparated factor input) (index : Nat) : Prop :=
  weightedUpper index (reducedBall separated) < 1 / 9

instance reducedSmallDecidable {factor : Gaussian} {input : Ball}
    (separated : DenominatorSeparated factor input) (index : Nat) :
    Decidable (ReducedSmall separated index) := by
  unfold ReducedSmall weightedUpper
  infer_instance

/-- Both rational conditions needed to build a safe chart on the refinement
future of the displayed ball. -/
structure Certificate (factor : Gaussian) (input : Ball) (index : Nat) : Prop where
  denominatorSeparated : DenominatorSeparated factor input
  reducedSmall : ReducedSmall denominatorSeparated index

instance certificateDecidable (factor : Gaussian) (input : Ball)
    (index : Nat) : Decidable (Certificate factor input index) := by
  by_cases separated : DenominatorSeparated factor input
  · by_cases small : ReducedSmall separated index
    · exact isTrue
        { denominatorSeparated := separated
          reducedSmall := small }
    · exact isFalse (fun certificate => small certificate.reducedSmall)
  · exact isFalse (fun certificate =>
      separated certificate.denominatorSeparated)

namespace Certificate

/-- The lower norm-square retained by the denominator certificate. -/
def lowerSq {factor : Gaussian} {input : Ball}
    {index : Nat} (certificate : Certificate factor input index) : Coordinate :=
  (denominatorApart certificate.denominatorSeparated).lowerSq

theorem lowerSq_positive {factor : Gaussian} {input : Ball}
    {index : Nat} (certificate : Certificate factor input index) :
    0 < certificate.lowerSq :=
  (denominatorApart certificate.denominatorSeparated).positive

/-- Every point in the tested input ball has a uniformly separated chart
denominator. -/
theorem denominator_lower {factor value : Gaussian} {input : Ball}
    {index : Nat} (certificate : Certificate factor input index)
    (inside : input.Contains value) :
    certificate.lowerSq ≤ normSq (factor * value + 1) :=
  (denominatorApart certificate.denominatorSeparated).lower
    (denominatorBall_contains inside)

/-- The reduced chart argument formed from any two independently admitted
input candidates lies in the required local logarithm disk. -/
theorem reduced_bound {factor numerator denominator : Gaussian} {input : Ball}
    {index : Nat} (certificate : Certificate factor input index)
    (numeratorInside : input.Contains numerator)
    (denominatorInside : input.Contains denominator) :
    normSq
        ((factor * numerator - 1) / (factor * denominator + 1)) ≤ 1 / 9 := by
  have inside :
      (reducedBall certificate.denominatorSeparated).Contains
        ((factor * numerator - 1) / (factor * denominator + 1)) :=
    CCL.ArithmeticEnclosures.Ball.contains_div
      (denominatorApart certificate.denominatorSeparated)
      (numeratorBall_contains numeratorInside)
      (denominatorBall_contains denominatorInside)
  exact (normSq_lt_of_weightedUpper certificate.reducedSmall inside).le

end Certificate

/-- The exact unit ball passes the executable safety test immediately. -/
theorem exactOne_certificate : Certificate 1 (exactBall 1) 0 := by
  decide

/-- A nontrivial exact point strictly inside the unit-factor local chart also
passes immediately.  The reduced argument is `1/5`, not zero. -/
theorem exactThreeHalves_certificate :
    Certificate 1 (exactBall (3 / 2)) 0 := by
  decide

/-- Turn a successful finite ball test and an exact overlap witness into the
existing safe anchored-chart transport datum over the target's based future. -/
def extensionOfBased
    (sourceInput targetInput : CoherentNamed)
    (source : AnchoredChart sourceInput)
    (base : targetInput.name.process.State)
    {index : Nat} (certificate : Certificate source.chart.factor
      (targetInput.name.process.ball base) index)
    (overlap : OverlapWitness sourceInput
      (CCL.ProgressiveCoherence.CoherentNamed.based targetInput base)) :
    SafeOverlapExtension sourceInput
      (CCL.ProgressiveCoherence.CoherentNamed.based targetInput base) source where
  overlap := overlap
  lowerSq := certificate.lowerSq
  lowerSq_positive := certificate.lowerSq_positive
  denominatorLower := by
    intro state value possible
    apply certificate.denominator_lower
    exact targetInput.name.process.possible_inside
      (state.persists possible)
  reducedBound := by
    intro numeratorSource denominatorSource numeratorPossible
      denominatorPossible
    apply certificate.reduced_bound
    · exact targetInput.name.process.possible_inside numeratorPossible
    · exact targetInput.name.process.possible_inside denominatorPossible

end CCL.LogChartSafety
