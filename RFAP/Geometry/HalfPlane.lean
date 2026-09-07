import mathlib.Tactic.QuotientFreeRing
import RFAP.Cauchy.Partition
import RFAP.Geometry.BoxClearance

/-!
# Choice-free half-plane winding on constructive intervals

A positive real coordinate prevents a path from leaving the open right half
plane.  The proof below never selects a zero or invokes an intermediate-value
principle.  Instead, the finite Cauchy-event scanner resolves a fixed-depth
central-third partition, and a three-sign table turns every local event into
an endpoint jump.  Those endpoint jumps telescope exactly.
-/

namespace RFAP.HalfPlane

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Polynomial := RFAP.ComputablePolynomial.DensePolynomial Coordinate
abbrev Interval := RFAP.PathClearance.Interval
abbrev ClearanceCertificate := RFAP.PathClearance.Certificate

open RFAP.Sturm
open RFAP.PathClearance
open RFAP.IntervalSign
open RFAP.SafeCandidates
open RFAP.CauchyProductSigns
open RFAP.CauchyCells
open RFAP.CauchyResolution

/-- Endpoint-jump formula for a path whose real coordinate stays positive. -/
def Formula (R S : Polynomial) (a b : Coordinate) : Prop :=
  cauchyIndex2 R S a b =
    (signJump 1 (R.eval a * S.eval a) : Int) -
      signJump 1 (R.eval b * S.eval b)

theorem Formula.add {R S : Polynomial} {a b c : Coordinate}
    (left : Formula R S a b) (right : Formula R S b c) :
    Formula R S a c := by
  unfold Formula at left right ⊢
  rw [cauchyIndex2_add R S a b c, left, right]
  ring1

theorem Formula.reverse {R S : Polynomial} {a b : Coordinate}
    (formula : Formula R S a b) : Formula R S b a := by
  unfold Formula at formula ⊢
  rw [cauchyIndex2_reverse, formula]
  ring1

/-- With a fixed positive real sign, one formal Cauchy event is exactly the
change of the two endpoint quadrant jumps. -/
theorem finiteSign_eventIndex2_positive
    (center lower upper : FiniteSign)
    (lowerStable : FiniteSign.Stable center lower)
    (upperStable : FiniteSign.Stable center upper) :
    FiniteSign.eventIndex2 .positive center
        .positive lower .positive upper =
      (FiniteSign.jump .positive lower : Int) -
        FiniteSign.jump .positive upper := by
  cases center <;> cases lower <;> cases upper <;>
    simp_all [FiniteSign.Stable, FiniteSign.eventIndex2,
      FiniteSign.leftEndpointIndex2, FiniteSign.jump,
      FiniteSign.value, FiniteSign.mul]

private theorem jump_positive_eq_signJump_mul
    {r s : Coordinate} (positive : 0 < r) :
    FiniteSign.jump .positive (FiniteSign.ofCoordinate s) =
      signJump 1 (r * s) := by
  rw [← FiniteSign.jump_ofCoordinate]
  rw [FiniteSign.ofCoordinate_of_pos (by decide : (0 : Coordinate) < 1),
    FiniteSign.ofCoordinate_mul r s,
    FiniteSign.ofCoordinate_of_pos positive]
  cases FiniteSign.ofCoordinate s <;> rfl

/-- One resolved finite event in the open right half-plane has the exact
endpoint-jump formula. -/
theorem formula_of_event
    {R S : Polynomial} {interval : Interval}
    (event : CauchyEventSigns R S interval)
    (realPositive : ∀ x : Coordinate, interval.Contains x → 0 < R.eval x) :
    Formula R S interval.lower interval.upper := by
  have lowerPositive := realPositive interval.lower
    ⟨le_rfl, interval.valid⟩
  have upperPositive := realPositive interval.upper
    ⟨interval.valid, le_rfl⟩
  let centered := event.recenter .positive event.denominator
    (Or.inl (by decide))
    (Or.inr (FiniteSign.ofCoordinate_of_pos lowerPositive).symm)
    event.denominatorLowerStable
    (Or.inr (FiniteSign.ofCoordinate_of_pos upperPositive).symm)
    event.denominatorUpperStable
  have index := centered.index
  unfold Formula
  rw [index]
  dsimp only [centered, CauchyEventSigns.recenter]
  rw [FiniteSign.ofCoordinate_of_pos lowerPositive,
    FiniteSign.ofCoordinate_of_pos upperPositive]
  rw [finiteSign_eventIndex2_positive _ _ _
      event.denominatorLowerStable event.denominatorUpperStable,
    jump_positive_eq_signJump_mul lowerPositive,
    jump_positive_eq_signJump_mul upperPositive]

/-- A sufficiently narrow subinterval is resolved by the finite Cauchy-event
scanner and hence satisfies the right-half-plane formula. -/
theorem formula_of_refined_width
    {R S : Polynomial} {root interval : Interval}
    (clearance : ClearanceCertificate R S root)
    (refines : interval.Refines root)
    (proper : interval.lower < interval.upper)
    (widthSmall : interval.upper - interval.lower <
      min 1 (signedChainResolutionRadiusSq S R clearance.swap))
    (realPositive : ∀ x : Coordinate, root.Contains x → 0 < R.eval x) :
    Formula R S interval.lower interval.upper := by
  have radius : sampleRadiusSq interval interval.lower <
      signedChainResolutionRadiusSq S R clearance.swap :=
    RFAP.CauchyPartition.radius_lt_of_width_lt
      proper widthSmall
  let event := cauchyEventSignsOfRefinedRadiusSq clearance.swap refines radius
  apply formula_of_event event
  intro x inside
  exact realPositive x
    ⟨refines.1.trans inside.1, inside.2.trans refines.2⟩

/-- Fixed-depth central-third subdivision for the half-plane formula. -/
theorem formulaAtDepth
    {R S : Polynomial} {root : Interval}
    (clearance : ClearanceCertificate R S root)
    (realPositive : ∀ x : Coordinate, root.Contains x → 0 < R.eval x)
    (fuel : Nat) (interval : Interval)
    (refines : interval.Refines root)
    (proper : interval.lower < interval.upper)
    (sufficient : (2 / 3 : Coordinate) ^ fuel *
      (interval.upper - interval.lower) <
        min 1 (signedChainResolutionRadiusSq S R clearance.swap)) :
    Formula R S interval.lower interval.upper := by
  induction fuel generalizing interval with
  | zero =>
      apply formula_of_refined_width clearance refines proper
      · simpa only [pow_zero, one_mul] using sufficient
      · exact realPositive
  | succ fuel inductionHypothesis =>
      let cut := centralLower interval.lower interval.upper
      have bounds := centralBounds proper
      have cutLower : interval.lower < cut := by
        simpa only [cut] using bounds.1
      have cutUpper : cut < interval.upper := by
        exact (by simpa only [cut] using bounds.2.1.trans bounds.2.2)
      let leftInterval : Interval :=
        { lower := interval.lower
          upper := cut
          valid := cutLower.le }
      let rightInterval : Interval :=
        { lower := cut
          upper := interval.upper
          valid := cutUpper.le }
      have leftRefines : leftInterval.Refines root :=
        ⟨refines.1, cutUpper.le.trans refines.2⟩
      have rightRefines : rightInterval.Refines root :=
        ⟨refines.1.trans cutLower.le, refines.2⟩
      have widthPositive : 0 < interval.upper - interval.lower :=
        RFAP.ConstructiveFraction.sub_pos_direct proper
      have leftContraction :
          leftInterval.upper - leftInterval.lower ≤
            (2 / 3 : Coordinate) *
              (interval.upper - interval.lower) := by
        dsimp only [leftInterval, cut]
        simp only [centralLower,
          RFAP.NormalizedFraction.normalizedAdd_eq,
          RFAP.NormalizedFraction.normalizedDiv_eq,
          RFAP.NormalizedFraction.normalizedSub_eq]
        have scaled :=
          RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
            (show (1 / 3 : Coordinate) ≤ 2 / 3 by decide)
            widthPositive.le
        calc
          interval.lower + (interval.upper - interval.lower) / 3 -
                interval.lower =
              (1 / 3 : Coordinate) *
                (interval.upper - interval.lower) := by
            rw [add_sub_cancel_left]
            rw [RFAP.ExplicitField.div_eq_mul_inv,
              RFAP.ExplicitField.div_eq_mul_inv]
            ring1
          _ ≤ (2 / 3 : Coordinate) *
                (interval.upper - interval.lower) := scaled
      have rightContraction :
          rightInterval.upper - rightInterval.lower =
            (2 / 3 : Coordinate) *
              (interval.upper - interval.lower) := by
        dsimp only [rightInterval, cut]
        simp only [centralLower,
          RFAP.NormalizedFraction.normalizedAdd_eq,
          RFAP.NormalizedFraction.normalizedDiv_eq,
          RFAP.NormalizedFraction.normalizedSub_eq]
        have scaled : (3 : Coordinate) *
            ((interval.upper - interval.lower) / 3) =
              interval.upper - interval.lower := by
          rw [RFAP.ConstructiveFraction.mul_comm]
          exact RFAP.ConstructiveFraction.div_mul_cancel_of_ne
            (interval.upper - interval.lower) 3 (by decide)
        rw [sub_add_eq_twice_of_three_mul interval.lower interval.upper
          ((interval.upper - interval.lower) / 3) scaled]
        rw [RFAP.ExplicitField.div_eq_mul_inv,
          RFAP.ExplicitField.div_eq_mul_inv]
        ring1
      have powerNonnegative : 0 ≤ (2 / 3 : Coordinate) ^ fuel :=
        RFAP.ConstructiveFraction.pow_nonneg_direct (by decide) fuel
      have leftSufficient : (2 / 3 : Coordinate) ^ fuel *
          (leftInterval.upper - leftInterval.lower) <
            min 1 (signedChainResolutionRadiusSq S R clearance.swap) := by
        calc
          (2 / 3 : Coordinate) ^ fuel *
              (leftInterval.upper - leftInterval.lower) ≤
              (2 / 3 : Coordinate) ^ fuel *
                ((2 / 3 : Coordinate) *
                  (interval.upper - interval.lower)) :=
            RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
              leftContraction powerNonnegative
          _ = (2 / 3 : Coordinate) ^ Nat.succ fuel *
              (interval.upper - interval.lower) := by
            rw [pow_succ]
            ring1
          _ < min 1 (signedChainResolutionRadiusSq S R clearance.swap) :=
            sufficient
      have rightSufficient : (2 / 3 : Coordinate) ^ fuel *
          (rightInterval.upper - rightInterval.lower) <
            min 1 (signedChainResolutionRadiusSq S R clearance.swap) := by
        rw [rightContraction]
        calc
          (2 / 3 : Coordinate) ^ fuel *
              ((2 / 3 : Coordinate) *
                (interval.upper - interval.lower)) =
              (2 / 3 : Coordinate) ^ Nat.succ fuel *
                (interval.upper - interval.lower) := by
            rw [pow_succ]
            ring1
          _ < min 1 (signedChainResolutionRadiusSq S R clearance.swap) :=
            sufficient
      exact (inductionHypothesis leftInterval leftRefines cutLower
        leftSufficient).add
        (inductionHypothesis rightInterval rightRefines cutUpper
          rightSufficient)

/-- Complete choice-free half-plane formula on a proper constructive
interval. -/
theorem formula_of_positive_real
    {R S : Polynomial} {root : Interval}
    (clearance : ClearanceCertificate R S root)
    (proper : root.lower < root.upper)
    (realPositive : ∀ x : Coordinate, root.Contains x → 0 < R.eval x) :
    Formula R S root.lower root.upper := by
  let leafWidth := min 1 (signedChainResolutionRadiusSq S R clearance.swap)
  have leafWidthPositive : 0 < leafWidth :=
    lt_min (by decide)
      (signedChainResolutionRadiusSq_pos S R clearance.swap)
  let depth := geometricDepth (root.upper - root.lower) (leafWidth / 2)
  have geometric : (2 / 3 : Coordinate) ^ depth *
      (root.upper - root.lower) ≤ leafWidth / 2 := by
    simpa only [depth] using geometricDepth_sufficient
      (width := root.upper - root.lower) (epsilon := leafWidth / 2)
      (RFAP.ConstructiveFraction.sub_pos_direct proper).le
      (RFAP.ConstructiveFraction.div_pos_direct leafWidthPositive (by decide))
  have halfBelow : leafWidth / 2 < leafWidth := by
    have scaled := RFAP.ConstructiveFraction.mul_lt_mul_of_pos_right_direct
      (show (1 / 2 : Coordinate) < 1 by decide) leafWidthPositive
    rw [RFAP.ExplicitField.div_eq_mul_inv]
    have halfInverse : (2 : Coordinate)⁻¹ = 1 / 2 := by
      rw [RFAP.ExplicitField.div_eq_mul_inv]
      exact (RFAP.ConstructiveFraction.one_mul _).symm
    rw [halfInverse]
    simpa only [RFAP.ConstructiveFraction.mul_comm, one_mul] using scaled
  apply formulaAtDepth clearance realPositive depth root
    ⟨le_rfl, le_rfl⟩ proper
  simpa only [leafWidth] using geometric.trans_lt halfBelow

/-- A polynomial path contained in the open right half-plane has zero raw
winding around a positively oriented constructive box. -/
theorem quadrupledBoxWinding_eq_zero_of_positive_real
    (p : RFAP.Winding.GaussianPolynomial)
    (box : RFAP.Boxes.Box)
    (proper : box.Proper)
    (clearance : RFAP.BoxClearance.BoundaryClearance p box)
    (realPositive : ∀ z : RFAP.ConstructiveGaussian.Gaussian,
      RFAP.BoxClearance.OnBoxBoundary box z →
        0 < (p.eval z).re) :
    RFAP.Winding.quadrupledBoxWinding p box = 0 := by
  open RFAP.Winding in
  have bottom := formula_of_positive_real
    (RFAP.BoxClearance.bottomOfBoundary
      clearance).toPathCertificate proper.1 (by
        intro x inside
        rw [RFAP.PathPolynomial.eval_pathReal, line_horizontal]
        exact realPositive (point x box.yLower)
          ⟨⟨inside.1, inside.2, le_rfl, box.y_valid⟩,
            Or.inr (Or.inr (Or.inl rfl))⟩)
  open RFAP.Winding in
  have right := formula_of_positive_real
    (RFAP.BoxClearance.rightOfBoundary
      clearance).toPathCertificate proper.2 (by
        intro y inside
        rw [RFAP.PathPolynomial.eval_pathReal, line_vertical]
        exact realPositive (point box.xUpper y)
          ⟨⟨box.x_valid, le_rfl, inside.1, inside.2⟩,
            Or.inr (Or.inl rfl)⟩)
  open RFAP.Winding in
  have topIncreasing := formula_of_positive_real
    (RFAP.BoxClearance.topOfBoundary
      clearance).toPathCertificate proper.1 (by
        intro x inside
        rw [RFAP.PathPolynomial.eval_pathReal, line_horizontal]
        exact realPositive (point x box.yUpper)
          ⟨⟨inside.1, inside.2, box.y_valid, le_rfl⟩,
            Or.inr (Or.inr (Or.inr rfl))⟩)
  open RFAP.Winding in
  have leftIncreasing := formula_of_positive_real
    (RFAP.BoxClearance.leftOfBoundary
      clearance).toPathCertificate proper.2 (by
        intro y inside
        rw [RFAP.PathPolynomial.eval_pathReal, line_vertical]
        exact realPositive (point box.xLower y)
          ⟨⟨le_rfl, box.x_valid, inside.1, inside.2⟩, Or.inl rfl⟩)
  have top := topIncreasing.reverse
  have left := leftIncreasing.reverse
  unfold Formula at bottom right top left
  open RFAP.Winding in
  simp only [RFAP.PathPolynomial.eval_pathReal,
    RFAP.PathPolynomial.eval_pathImag,
    line_horizontal] at bottom top
  open RFAP.Winding in
  simp only [RFAP.PathPolynomial.eval_pathReal,
    RFAP.PathPolynomial.eval_pathImag,
    line_vertical] at right left
  open RFAP.Winding in
  rw [quadrupledBoxWinding_eq]
  open RFAP.Winding in
  simp only [horizontalEdge, verticalEdge,
    PolynomialEdge.doubledWinding, PolynomialEdge.ofLine]
  rw [bottom, right, top, left]
  ring1

end RFAP.HalfPlane
