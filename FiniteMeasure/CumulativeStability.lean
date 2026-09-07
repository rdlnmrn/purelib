import FiniteMeasure.Cumulative
import FiniteMeasure.TotalVariationDistance

/-!
# Stability of finite cumulative laws

Total variation controls every executable lower-ray event, hence every exact
rational cumulative probability.  A displayed finite threshold grid packages
these pointwise bounds as the constructive finite replacement for a uniform
CDF comparison.  No supremum over all thresholds or limiting law is formed.
-/

namespace FiniteMeasure

namespace Distribution

/-- Exact maximum cumulative-probability discrepancy on a displayed finite
rational threshold grid.  The empty grid has distance zero. -/
def cumulativeGridDistance (left right : Distribution Coordinate) :
    List Coordinate → Coordinate
  | [] => 0
  | threshold :: remaining =>
      max (rationalSeparation (left.cumulative threshold)
        (right.cumulative threshold))
        (cumulativeGridDistance left right remaining)

theorem cumulativeGridDistance_nonnegative
  (left right : Distribution Coordinate) :
    ∀ thresholds, 0 ≤ left.cumulativeGridDistance right thresholds
  | [] => le_rfl
  | threshold :: _ =>
      (rationalSeparation_nonneg
        (left.cumulative threshold) (right.cumulative threshold)).trans
        (le_max_left _ _)

/-- Every grid member's exact CDF discrepancy is bounded by the computed
grid distance. -/
theorem cumulative_separation_le_cumulativeGridDistance
    (left right : Distribution Coordinate) (threshold : Coordinate) :
    ∀ {thresholds : List Coordinate}, threshold ∈ thresholds →
      rationalSeparation (left.cumulative threshold)
          (right.cumulative threshold) ≤
        left.cumulativeGridDistance right thresholds
  | [], member => (List.not_mem_nil member).elim
  | head :: remaining, member => by
      rcases List.mem_cons.mp member with equal | tailMember
      · subst threshold
        exact le_max_left _ _
      · exact (cumulative_separation_le_cumulativeGridDistance left right
          threshold tailMember).trans (le_max_right _ _)

/-- Least-upper-bound property of the computed grid distance. -/
theorem cumulativeGridDistance_le
    (left right : Distribution Coordinate)
    (thresholds : List Coordinate) (bound : Coordinate)
    (boundNonnegative : 0 ≤ bound)
    (pointwise : ∀ threshold, threshold ∈ thresholds →
      rationalSeparation (left.cumulative threshold)
        (right.cumulative threshold) ≤ bound) :
    left.cumulativeGridDistance right thresholds ≤ bound := by
  induction thresholds with
  | nil => exact boundNonnegative
  | cons threshold remaining inductionHypothesis =>
      unfold cumulativeGridDistance
      apply max_le
      · exact pointwise threshold List.mem_cons_self
      · apply inductionHypothesis
        intro candidate member
        exact pointwise candidate (List.mem_cons_of_mem threshold member)

/-- Displayed-grid CDF distance is symmetric. -/
theorem cumulativeGridDistance_symm
    (left right : Distribution Coordinate) :
    ∀ thresholds,
      left.cumulativeGridDistance right thresholds =
        right.cumulativeGridDistance left thresholds
  | [] => rfl
  | threshold :: remaining => by
      unfold cumulativeGridDistance
      rw [rationalSeparation_symm,
        cumulativeGridDistance_symm left right remaining]

@[simp] theorem cumulativeGridDistance_refl
    (distribution : Distribution Coordinate) (thresholds : List Coordinate) :
    distribution.cumulativeGridDistance distribution thresholds = 0 := by
  apply RFAP.ConstructiveFraction.le_antisymm
  · apply distribution.cumulativeGridDistance_le distribution thresholds 0
      le_rfl
    intro threshold member
    exact ((rationalSeparation_eq_zero_iff _ _).mpr rfl).le
  · exact distribution.cumulativeGridDistance_nonnegative distribution
      thresholds

/-- Triangle inequality for the exact displayed-grid CDF distance. -/
theorem cumulativeGridDistance_triangle
    (left middle right : Distribution Coordinate)
    (thresholds : List Coordinate) :
    left.cumulativeGridDistance right thresholds ≤
      left.cumulativeGridDistance middle thresholds +
        middle.cumulativeGridDistance right thresholds := by
  apply left.cumulativeGridDistance_le right thresholds
  · exact add_nonneg
      (left.cumulativeGridDistance_nonnegative middle thresholds)
      (middle.cumulativeGridDistance_nonnegative right thresholds)
  · intro threshold member
    calc
      rationalSeparation (left.cumulative threshold)
          (right.cumulative threshold) ≤
        rationalSeparation (left.cumulative threshold)
            (middle.cumulative threshold) +
          rationalSeparation (middle.cumulative threshold)
            (right.cumulative threshold) :=
        rationalSeparation_triangle _ _ _
      _ ≤ left.cumulativeGridDistance middle thresholds +
          middle.cumulativeGridDistance right thresholds :=
        add_le_add
          (left.cumulative_separation_le_cumulativeGridDistance middle
            threshold member)
          (middle.cumulative_separation_le_cumulativeGridDistance right
            threshold member)

/-- Common-weight rational mixing is convex for the displayed-grid CDF
distance. -/
theorem cumulativeGridDistance_mixture_le
    (leftFirst leftSecond rightFirst rightSecond :
      Distribution Coordinate)
    (weight : MixingWeight) (thresholds : List Coordinate) :
    (leftFirst.mixture leftSecond weight).cumulativeGridDistance
        (rightFirst.mixture rightSecond weight) thresholds ≤
      weight.coefficient *
          leftFirst.cumulativeGridDistance rightFirst thresholds +
        weight.complement *
          leftSecond.cumulativeGridDistance rightSecond thresholds := by
  apply (leftFirst.mixture leftSecond weight).cumulativeGridDistance_le
    (rightFirst.mixture rightSecond weight) thresholds
  · exact add_nonneg
      (RFAP.ConstructiveFraction.mul_nonneg_direct weight.nonnegative
        (leftFirst.cumulativeGridDistance_nonnegative rightFirst thresholds))
      (RFAP.ConstructiveFraction.mul_nonneg_direct
        weight.complement_nonnegative
        (leftSecond.cumulativeGridDistance_nonnegative rightSecond
          thresholds))
  · intro threshold member
    rw [leftFirst.cumulative_mixture leftSecond weight,
      rightFirst.cumulative_mixture rightSecond weight]
    calc
      rationalSeparation
          (weight.coefficient * leftFirst.cumulative threshold +
            weight.complement * leftSecond.cumulative threshold)
          (weight.coefficient * rightFirst.cumulative threshold +
            weight.complement * rightSecond.cumulative threshold) ≤
        rationalSeparation
            (weight.coefficient * leftFirst.cumulative threshold)
            (weight.coefficient * rightFirst.cumulative threshold) +
          rationalSeparation
            (weight.complement * leftSecond.cumulative threshold)
            (weight.complement * rightSecond.cumulative threshold) :=
        rationalSeparation_add_le _ _ _ _
      _ = weight.coefficient * rationalSeparation
            (leftFirst.cumulative threshold) (rightFirst.cumulative threshold) +
          weight.complement * rationalSeparation
            (leftSecond.cumulative threshold)
            (rightSecond.cumulative threshold) := by
        rw [rationalSeparation_scale, rationalSeparation_scale,
          rationalSeparation_zero_of_nonneg weight.nonnegative,
          rationalSeparation_zero_of_nonneg weight.complement_nonnegative]
      _ ≤ weight.coefficient *
            leftFirst.cumulativeGridDistance rightFirst thresholds +
          weight.complement *
            leftSecond.cumulativeGridDistance rightSecond thresholds :=
        add_le_add
          (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
            (leftFirst.cumulative_separation_le_cumulativeGridDistance
              rightFirst threshold member) weight.nonnegative)
          (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
            (leftSecond.cumulative_separation_le_cumulativeGridDistance
              rightSecond threshold member) weight.complement_nonnegative)

/-- Zero displayed-grid distance means equality of the two exact cumulative
probabilities at every supplied cut, and conversely. -/
theorem cumulativeGridDistance_eq_zero_iff
    (left right : Distribution Coordinate) (thresholds : List Coordinate) :
    left.cumulativeGridDistance right thresholds = 0 ↔
      ∀ threshold, threshold ∈ thresholds →
        left.cumulative threshold = right.cumulative threshold := by
  constructor
  · intro distanceZero threshold member
    apply (rationalSeparation_eq_zero_iff _ _).mp
    apply RFAP.ConstructiveFraction.le_antisymm
    · rw [← distanceZero]
      exact left.cumulative_separation_le_cumulativeGridDistance right
        threshold member
    · exact rationalSeparation_nonneg _ _
  · intro equal
    apply RFAP.ConstructiveFraction.le_antisymm
    · apply left.cumulativeGridDistance_le right thresholds 0 le_rfl
      intro threshold member
      exact ((rationalSeparation_eq_zero_iff _ _).mpr
        (equal threshold member)).le
    · exact left.cumulativeGridDistance_nonnegative right thresholds

/-- Total variation controls the discrepancy between two exact finite
cumulative probabilities at every supplied rational threshold. -/
theorem cumulative_separation_le_totalVariationDistance
    (left right : Distribution Coordinate) (threshold : Coordinate) :
    rationalSeparation (left.cumulative threshold)
        (right.cumulative threshold) ≤
      left.totalVariationDistance right :=
  left.probability_separation_le_totalVariationDistance right
    (atMostEvent threshold)

/-- Every threshold in one displayed rational grid has cumulative
discrepancy strictly below the supplied tolerance. -/
def CumulativeGridClose (left right : Distribution Coordinate)
    (thresholds : List Coordinate) (tolerance : Coordinate) : Prop :=
  ∀ threshold, threshold ∈ thresholds →
    rationalSeparation (left.cumulative threshold)
      (right.cumulative threshold) < tolerance

/-- Strict accuracy on every displayed cut is equivalent to one strict bound
on the computed finite-grid CDF distance. -/
theorem cumulativeGridDistance_lt_iff
    (left right : Distribution Coordinate)
    (thresholds : List Coordinate) (tolerance : Coordinate)
    (tolerancePositive : 0 < tolerance) :
    left.cumulativeGridDistance right thresholds < tolerance ↔
      CumulativeGridClose left right thresholds tolerance := by
  constructor
  · intro distanceSmall threshold member
    exact (left.cumulative_separation_le_cumulativeGridDistance right
      threshold member).trans_lt distanceSmall
  · intro close
    induction thresholds with
    | nil => exact tolerancePositive
    | cons threshold remaining inductionHypothesis =>
        unfold cumulativeGridDistance
        apply max_lt_iff.mpr
        exact ⟨close threshold List.mem_cons_self,
          inductionHypothesis (by
            intro candidate member
            exact close candidate
              (List.mem_cons_of_mem threshold member))⟩

/-- A strict total-variation budget gives simultaneous cumulative accuracy
on every member of a displayed finite threshold grid. -/
theorem cumulativeGridClose_of_totalVariationDistance_lt
    (left right : Distribution Coordinate)
    (thresholds : List Coordinate) (tolerance : Coordinate)
    (small : left.totalVariationDistance right < tolerance) :
    CumulativeGridClose left right thresholds tolerance := by
  intro threshold member
  exact (left.cumulative_separation_le_totalVariationDistance
    right threshold).trans_lt small

/-- Exact total variation bounds the computed CDF discrepancy on every
displayed finite threshold grid. -/
theorem cumulativeGridDistance_le_totalVariationDistance
    (left right : Distribution Coordinate)
    (thresholds : List Coordinate) :
    left.cumulativeGridDistance right thresholds ≤
      left.totalVariationDistance right := by
  apply left.cumulativeGridDistance_le right thresholds
  · exact left.totalVariationDistance_nonnegative right
  · intro threshold member
    exact left.cumulative_separation_le_totalVariationDistance right threshold

end Distribution

end FiniteMeasure
