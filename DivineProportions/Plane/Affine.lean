import mathlib.Tactic.QuotientFreeRing
import DivineProportions.Plane.Incidence

/-!
# Divine Proportions, §§3.7–3.8: affine combinations

All parameters and witnesses are field elements.  Membership and uniqueness
are proved by finite coordinate algebra, with the nonzero coordinate selected
by decidable equality rather than by choice.
-/

namespace DivineProportions

variable {K : Type*} [RFAP.ExplicitField K]

/-- The displayed two-point affine combination. -/
def affineCombination (leftWeight : K) (left : Point K)
    (rightWeight : K) (right : Point K) : Point K :=
  ⟨leftWeight * left.x + rightWeight * right.x,
    leftWeight * left.y + rightWeight * right.y⟩

/-- A displayed affine combination of three points. -/
def affineCombinationThree
    (firstWeight : K) (first : Point K)
    (secondWeight : K) (second : Point K)
    (thirdWeight : K) (third : Point K) : Point K :=
  ⟨firstWeight * first.x + secondWeight * second.x +
      thirdWeight * third.x,
    firstWeight * first.y + secondWeight * second.y +
      thirdWeight * third.y⟩

@[simp] theorem affineCombinationThree_x
    (firstWeight : K) (first : Point K)
    (secondWeight : K) (second : Point K)
    (thirdWeight : K) (third : Point K) :
    (affineCombinationThree firstWeight first secondWeight second
      thirdWeight third).x =
      firstWeight * first.x + secondWeight * second.x +
        thirdWeight * third.x := rfl

@[simp] theorem affineCombinationThree_y
    (firstWeight : K) (first : Point K)
    (secondWeight : K) (second : Point K)
    (thirdWeight : K) (third : Point K) :
    (affineCombinationThree firstWeight first secondWeight second
      thirdWeight third).y =
      firstWeight * first.y + secondWeight * second.y +
        thirdWeight * third.y := rfl

@[simp] theorem affineCombination_x (leftWeight : K) (left : Point K)
    (rightWeight : K) (right : Point K) :
    (affineCombination leftWeight left rightWeight right).x =
      leftWeight * left.x + rightWeight * right.x := rfl

@[simp] theorem affineCombination_y (leftWeight : K) (left : Point K)
    (rightWeight : K) (right : Point K) :
    (affineCombination leftWeight left rightWeight right).y =
      leftWeight * left.y + rightWeight * right.y := rfl

private theorem sub_ne_zero_of_ne {a b : K} (different : a ≠ b) : a - b ≠ 0 := by
  intro differenceZero
  apply different
  calc
    a = (a - b) + b := by ring1
    _ = 0 + b := by rw [differenceZero]
    _ = b := zero_add b

private theorem eq_zero_of_mul_eq_zero_right [DecidableEq K]
    {left right : K} (rightNonzero : right ≠ 0) (productZero : left * right = 0) :
    left = 0 := by
  by_cases leftZero : left = 0
  · exact leftZero
  · exact False.elim
      ((RFAP.ExplicitField.mul_ne_zero leftZero rightNonzero) productZero)

/-- Barycentric weights relative to three non-collinear points are unique.
This is the finite coordinate fact needed to read geometric triangle
membership back into the displayed affine weights. -/
theorem affineCombinationThree_weights_unique [Nontrivial K] [DecidableEq K]
    (first second third : Point K)
    (notCollinear : ¬ Collinear first second third)
    {firstWeight secondWeight thirdWeight : K}
    {otherFirstWeight otherSecondWeight otherThirdWeight : K}
    (weightsSum : firstWeight + secondWeight + thirdWeight = 1)
    (otherWeightsSum :
      otherFirstWeight + otherSecondWeight + otherThirdWeight = 1)
    (pointsEqual :
      affineCombinationThree firstWeight first secondWeight second
          thirdWeight third =
        affineCombinationThree otherFirstWeight first otherSecondWeight second
          otherThirdWeight third) :
    firstWeight = otherFirstWeight ∧
      secondWeight = otherSecondWeight ∧
      thirdWeight = otherThirdWeight := by
  let firstDifference := firstWeight - otherFirstWeight
  let secondDifference := secondWeight - otherSecondWeight
  let thirdDifference := thirdWeight - otherThirdWeight
  have differenceSum :
      firstDifference + secondDifference + thirdDifference = 0 := by
    unfold firstDifference secondDifference thirdDifference
    calc
      (firstWeight - otherFirstWeight) +
            (secondWeight - otherSecondWeight) +
            (thirdWeight - otherThirdWeight) =
          (firstWeight + secondWeight + thirdWeight) -
            (otherFirstWeight + otherSecondWeight + otherThirdWeight) := by
              ring1
      _ = 0 := by rw [weightsSum, otherWeightsSum]; ring1
  have xDifference :
      firstDifference * first.x + secondDifference * second.x +
          thirdDifference * third.x = 0 := by
    have coordinateEquality := congrArg Point.x pointsEqual
    simp only [affineCombinationThree_x] at coordinateEquality
    unfold firstDifference secondDifference thirdDifference
    calc
      (firstWeight - otherFirstWeight) * first.x +
            (secondWeight - otherSecondWeight) * second.x +
            (thirdWeight - otherThirdWeight) * third.x =
          (firstWeight * first.x + secondWeight * second.x +
              thirdWeight * third.x) -
            (otherFirstWeight * first.x + otherSecondWeight * second.x +
              otherThirdWeight * third.x) := by ring1
      _ = 0 := by rw [coordinateEquality]; ring1
  have yDifference :
      firstDifference * first.y + secondDifference * second.y +
          thirdDifference * third.y = 0 := by
    have coordinateEquality := congrArg Point.y pointsEqual
    simp only [affineCombinationThree_y] at coordinateEquality
    unfold firstDifference secondDifference thirdDifference
    calc
      (firstWeight - otherFirstWeight) * first.y +
            (secondWeight - otherSecondWeight) * second.y +
            (thirdWeight - otherThirdWeight) * third.y =
          (firstWeight * first.y + secondWeight * second.y +
              thirdWeight * third.y) -
            (otherFirstWeight * first.y + otherSecondWeight * second.y +
              otherThirdWeight * third.y) := by ring1
      _ = 0 := by rw [coordinateEquality]; ring1
  have xReduced :
      firstDifference * (first.x - third.x) +
          secondDifference * (second.x - third.x) = 0 := by
    calc
      firstDifference * (first.x - third.x) +
            secondDifference * (second.x - third.x) =
          (firstDifference * first.x + secondDifference * second.x +
              thirdDifference * third.x) -
            (firstDifference + secondDifference + thirdDifference) *
              third.x := by ring1
      _ = 0 := by rw [xDifference, differenceSum]; ring1
  have yReduced :
      firstDifference * (first.y - third.y) +
          secondDifference * (second.y - third.y) = 0 := by
    calc
      firstDifference * (first.y - third.y) +
            secondDifference * (second.y - third.y) =
          (firstDifference * first.y + secondDifference * second.y +
              thirdDifference * third.y) -
            (firstDifference + secondDifference + thirdDifference) *
              third.y := by ring1
      _ = 0 := by rw [yDifference, differenceSum]; ring1
  have determinantNonzero : pointDeterminant first second third ≠ 0 := by
    intro determinantZero
    exact notCollinear
      ((collinear_iff_pointDeterminant_eq_zero first second third).2
        determinantZero)
  have firstProduct :
      firstDifference * pointDeterminant first second third = 0 := by
    calc
      firstDifference * pointDeterminant first second third =
          (firstDifference * (first.x - third.x) +
              secondDifference * (second.x - third.x)) *
              (second.y - third.y) -
            (firstDifference * (first.y - third.y) +
              secondDifference * (second.y - third.y)) *
              (second.x - third.x) := by
                unfold pointDeterminant
                ring1
      _ = 0 := by rw [xReduced, yReduced]; ring1
  have secondProduct :
      secondDifference * pointDeterminant first second third = 0 := by
    calc
      secondDifference * pointDeterminant first second third =
          (firstDifference * (first.y - third.y) +
              secondDifference * (second.y - third.y)) *
              (first.x - third.x) -
            (firstDifference * (first.x - third.x) +
              secondDifference * (second.x - third.x)) *
              (first.y - third.y) := by
                unfold pointDeterminant
                ring1
      _ = 0 := by rw [xReduced, yReduced]; ring1
  have firstDifferenceZero : firstDifference = 0 :=
    eq_zero_of_mul_eq_zero_right determinantNonzero firstProduct
  have secondDifferenceZero : secondDifference = 0 :=
    eq_zero_of_mul_eq_zero_right determinantNonzero secondProduct
  have thirdDifferenceZero : thirdDifference = 0 := by
    calc
      thirdDifference =
          firstDifference + secondDifference + thirdDifference := by
            rw [firstDifferenceZero, secondDifferenceZero]
            ring1
      _ = 0 := differenceSum
  exact ⟨sub_eq_zero.mp firstDifferenceZero,
    sub_eq_zero.mp secondDifferenceZero,
    sub_eq_zero.mp thirdDifferenceZero⟩

/-- The easy direction of Theorem 9: weights summing to one produce a point
on the line through the two source points. -/
theorem affineCombination_on_line [DecidableEq K]
    (first second : Point K) (distinct : first ≠ second)
    (leftWeight rightWeight : K) (weights : leftWeight + rightWeight = 1) :
    (lineThrough first second distinct).Contains
      (affineCombination leftWeight first rightWeight second) := by
  unfold Line.Contains lineThrough affineCombination
  calc
    (first.y - second.y) *
          (leftWeight * first.x + rightWeight * second.x) +
        (second.x - first.x) *
          (leftWeight * first.y + rightWeight * second.y) +
        (first.x * second.y - second.x * first.y) =
      (leftWeight + rightWeight - 1) *
        (second.x * first.y - first.x * second.y) := by ring1
    _ = 0 := by rw [weights]; ring1

/-- Construct the affine weights of an arbitrary point on a line. -/
theorem affineWeights_exist [DecidableEq K]
    (first second point : Point K) (distinct : first ≠ second)
    (onLine : (lineThrough first second distinct).Contains point) :
    ∃ leftWeight rightWeight : K,
      leftWeight + rightWeight = 1 ∧
      affineCombination leftWeight first rightWeight second = point := by
  unfold Line.Contains lineThrough at onLine
  change (first.y - second.y) * point.x +
      (second.x - first.x) * point.y +
      (first.x * second.y - second.x * first.y) = 0 at onLine
  have onLineExpanded :
      (first.y - second.y) * point.x +
        (second.x - first.x) * point.y +
        first.x * second.y - second.x * first.y = 0 := by
    calc
      (first.y - second.y) * point.x +
          (second.x - first.x) * point.y +
          first.x * second.y - second.x * first.y =
        (first.y - second.y) * point.x +
          (second.x - first.x) * point.y +
          (first.x * second.y - second.x * first.y) := by ring1
      _ = 0 := onLine
  by_cases sameX : first.x = second.x
  · have differentY : first.y ≠ second.y := by
      intro sameY
      apply distinct
      exact Point.ext sameX sameY
    let denominator := first.y - second.y
    have denominatorNonzero : denominator ≠ 0 := sub_ne_zero_of_ne differentY
    have inverseCancel : denominator⁻¹ * denominator = (1 : K) := by
      calc
        denominator⁻¹ * denominator = denominator * denominator⁻¹ := by ring1
        _ = 1 := RFAP.ExplicitField.mul_inv_cancel denominator denominatorNonzero
    let leftWeight := (point.y - second.y) / denominator
    let rightWeight := 1 - leftWeight
    refine ⟨leftWeight, rightWeight, by unfold rightWeight; ring1, ?_⟩
    apply Point.ext
    · have clearedX :
          denominator * (point.x - second.x) =
            (first.x - second.x) * (point.y - second.y) := by
        unfold denominator
        calc
          (first.y - second.y) * (point.x - second.x) =
              (first.x - second.x) * (point.y - second.y) +
                ((first.y - second.y) * point.x +
                  (second.x - first.x) * point.y +
                  first.x * second.y - second.x * first.y) := by ring1
          _ = (first.x - second.x) * (point.y - second.y) := by
            rw [onLineExpanded]
            ring1
      dsimp only [affineCombination, leftWeight, rightWeight]
      simp only [RFAP.ExplicitField.div_eq_mul_inv]
      calc
        (point.y - second.y) * denominator⁻¹ * first.x +
            (1 - (point.y - second.y) * denominator⁻¹) * second.x =
          second.x + denominator⁻¹ *
            ((first.x - second.x) * (point.y - second.y)) := by ring1
        _ = second.x + denominator⁻¹ *
            (denominator * (point.x - second.x)) := by rw [clearedX]
        _ = point.x := by
          rw [← mul_assoc, inverseCancel]
          ring1
    · dsimp only [affineCombination, leftWeight, rightWeight]
      simp only [RFAP.ExplicitField.div_eq_mul_inv]
      calc
        (point.y - second.y) * denominator⁻¹ * first.y +
            (1 - (point.y - second.y) * denominator⁻¹) * second.y =
          second.y + denominator⁻¹ *
            (denominator * (point.y - second.y)) := by
          unfold denominator
          ring1
        _ = point.y := by
          rw [← mul_assoc, inverseCancel]
          ring1
  · let denominator := first.x - second.x
    have denominatorNonzero : denominator ≠ 0 := sub_ne_zero_of_ne sameX
    have inverseCancel : denominator⁻¹ * denominator = (1 : K) := by
      calc
        denominator⁻¹ * denominator = denominator * denominator⁻¹ := by ring1
        _ = 1 := RFAP.ExplicitField.mul_inv_cancel denominator denominatorNonzero
    let leftWeight := (point.x - second.x) / denominator
    let rightWeight := 1 - leftWeight
    refine ⟨leftWeight, rightWeight, by unfold rightWeight; ring1, ?_⟩
    apply Point.ext
    · dsimp only [affineCombination, leftWeight, rightWeight]
      simp only [RFAP.ExplicitField.div_eq_mul_inv]
      calc
        (point.x - second.x) * denominator⁻¹ * first.x +
            (1 - (point.x - second.x) * denominator⁻¹) * second.x =
          second.x + denominator⁻¹ *
            (denominator * (point.x - second.x)) := by
          unfold denominator
          ring1
        _ = point.x := by
          rw [← mul_assoc, inverseCancel]
          ring1
    · have clearedY :
          denominator * (point.y - second.y) =
            (first.y - second.y) * (point.x - second.x) := by
        unfold denominator
        calc
          (first.x - second.x) * (point.y - second.y) =
              (first.y - second.y) * (point.x - second.x) -
                ((first.y - second.y) * point.x +
                  (second.x - first.x) * point.y +
                  first.x * second.y - second.x * first.y) := by ring1
          _ = (first.y - second.y) * (point.x - second.x) := by
            rw [onLineExpanded]
            ring1
      dsimp only [affineCombination, leftWeight, rightWeight]
      simp only [RFAP.ExplicitField.div_eq_mul_inv]
      calc
        (point.x - second.x) * denominator⁻¹ * first.y +
            (1 - (point.x - second.x) * denominator⁻¹) * second.y =
          second.y + denominator⁻¹ *
            ((first.y - second.y) * (point.x - second.x)) := by ring1
        _ = second.y + denominator⁻¹ *
            (denominator * (point.y - second.y)) := by rw [clearedY]
        _ = point.y := by
          rw [← mul_assoc, inverseCancel]
          ring1

/-- The weights in Theorem 9 are unique. -/
theorem affineWeights_unique [DecidableEq K]
    (first second : Point K) (distinct : first ≠ second)
    {leftWeight rightWeight otherLeftWeight otherRightWeight : K}
    (weights : leftWeight + rightWeight = 1)
    (otherWeights : otherLeftWeight + otherRightWeight = 1)
    (samePoint :
      affineCombination leftWeight first rightWeight second =
        affineCombination otherLeftWeight first otherRightWeight second) :
    leftWeight = otherLeftWeight ∧ rightWeight = otherRightWeight := by
  have rightFormula : rightWeight = 1 - leftWeight := by
    calc
      rightWeight = (leftWeight + rightWeight) - leftWeight := by ring1
      _ = 1 - leftWeight := by rw [weights]
  have otherRightFormula : otherRightWeight = 1 - otherLeftWeight := by
    calc
      otherRightWeight =
          (otherLeftWeight + otherRightWeight) - otherLeftWeight := by ring1
      _ = 1 - otherLeftWeight := by rw [otherWeights]
  have sameX := congrArg Point.x samePoint
  have sameY := congrArg Point.y samePoint
  simp only [affineCombination_x, rightFormula, otherRightFormula] at sameX
  simp only [affineCombination_y, rightFormula, otherRightFormula] at sameY
  have xProductZero :
      (leftWeight - otherLeftWeight) * (first.x - second.x) = 0 := by
    calc
      (leftWeight - otherLeftWeight) * (first.x - second.x) =
          (leftWeight * first.x + (1 - leftWeight) * second.x) -
            (otherLeftWeight * first.x +
              (1 - otherLeftWeight) * second.x) := by ring1
      _ = 0 := by rw [sameX]; ring1
  have yProductZero :
      (leftWeight - otherLeftWeight) * (first.y - second.y) = 0 := by
    calc
      (leftWeight - otherLeftWeight) * (first.y - second.y) =
          (leftWeight * first.y + (1 - leftWeight) * second.y) -
            (otherLeftWeight * first.y +
              (1 - otherLeftWeight) * second.y) := by ring1
      _ = 0 := by rw [sameY]; ring1
  have leftEqual : leftWeight = otherLeftWeight := by
    by_cases sameXCoordinate : first.x = second.x
    · have differentY : first.y ≠ second.y := by
        intro sameYCoordinate
        exact distinct (Point.ext sameXCoordinate sameYCoordinate)
      have differenceZero := eq_zero_of_mul_eq_zero_right
        (sub_ne_zero_of_ne differentY) yProductZero
      calc
        leftWeight = (leftWeight - otherLeftWeight) + otherLeftWeight := by ring1
        _ = otherLeftWeight := by rw [differenceZero]; ring1
    · have differenceZero := eq_zero_of_mul_eq_zero_right
        (sub_ne_zero_of_ne sameXCoordinate) xProductZero
      calc
        leftWeight = (leftWeight - otherLeftWeight) + otherLeftWeight := by ring1
        _ = otherLeftWeight := by rw [differenceZero]; ring1
  exact ⟨leftEqual, by rw [rightFormula, otherRightFormula, leftEqual]⟩

/-- Theorem 9 (Affine combination), packaged with existence and uniqueness. -/
theorem affineCombination_iff_on_line [DecidableEq K]
    (first second point : Point K) (distinct : first ≠ second) :
    (lineThrough first second distinct).Contains point ↔
      ∃ leftWeight rightWeight : K,
        leftWeight + rightWeight = 1 ∧
        affineCombination leftWeight first rightWeight second = point := by
  constructor
  · exact affineWeights_exist first second point distinct
  · rintro ⟨leftWeight, rightWeight, weights, rfl⟩
    exact affineCombination_on_line first second distinct leftWeight rightWeight weights

/-- The point a fraction `scale` of the way from `origin` to `target`. -/
def thalesPoint (scale : K) (origin target : Point K) : Point K :=
  affineCombination (1 - scale) origin scale target

private theorem thales_points_distinct [DecidableEq K]
    (scale : K) (origin second third : Point K)
    (scaleNonzero : scale ≠ 0) (secondThirdDistinct : second ≠ third) :
    thalesPoint scale origin second ≠ thalesPoint scale origin third := by
  intro equalPoints
  have equalX := congrArg Point.x equalPoints
  have equalY := congrArg Point.y equalPoints
  change (1 - scale) * origin.x + scale * second.x =
    (1 - scale) * origin.x + scale * third.x at equalX
  change (1 - scale) * origin.y + scale * second.y =
    (1 - scale) * origin.y + scale * third.y at equalY
  have xProductZero : scale * (second.x - third.x) = 0 := by
    calc
      scale * (second.x - third.x) =
          ((1 - scale) * origin.x + scale * second.x) -
            ((1 - scale) * origin.x + scale * third.x) := by ring1
      _ = 0 := by rw [equalX]; ring1
  have yProductZero : scale * (second.y - third.y) = 0 := by
    calc
      scale * (second.y - third.y) =
          ((1 - scale) * origin.y + scale * second.y) -
            ((1 - scale) * origin.y + scale * third.y) := by ring1
      _ = 0 := by rw [equalY]; ring1
  by_cases sameX : second.x = third.x
  · have differentY : second.y ≠ third.y := by
      intro sameY
      exact secondThirdDistinct (Point.ext sameX sameY)
    exact (RFAP.ExplicitField.mul_ne_zero scaleNonzero
      (sub_ne_zero_of_ne differentY)) yProductZero
  · exact (RFAP.ExplicitField.mul_ne_zero scaleNonzero
      (sub_ne_zero_of_ne sameX)) xProductZero

/-- Theorem 10 (Thales): corresponding affine points determine a line parallel
to the line through the two targets. -/
theorem thales_parallel [DecidableEq K]
    (scale : K) (origin second third : Point K)
    (scaleNonzero : scale ≠ 0) (secondThirdDistinct : second ≠ third) :
    (lineThrough (thalesPoint scale origin second)
        (thalesPoint scale origin third)
        (thales_points_distinct scale origin second third scaleNonzero
          secondThirdDistinct)).Parallel
      (lineThrough second third secondThirdDistinct) := by
  unfold Line.Parallel lineThrough thalesPoint affineCombination
  ring1

/-- The two coordinate determinant equations saying that opposite sides of
`A₁A₂A₃A₄` are parallel. -/
def ParallelogramSideConditions
    (first second third fourth : Point K) : Prop :=
  (first.y - second.y) * (fourth.x - third.x) -
      (third.y - fourth.y) * (second.x - first.x) = 0 ∧
    (second.y - third.y) * (first.x - fourth.x) -
      (fourth.y - first.y) * (third.x - second.x) = 0

/-- Midpoint of two displayed points.  Theorems using its geometric meaning
carry the source's explicit `2 ≠ 0` hypothesis. -/
def midpoint (first second : Point K) : Point K :=
  ⟨(first.x + second.x) / 2, (first.y + second.y) / 2⟩

/-- Theorem 11 (Parallelogram center): the exact two parallel-side equations,
together with the source's noncollinearity determinant, force the two diagonal
midpoints to coincide. -/
theorem parallelogram_center [DecidableEq K]
    (first second third fourth : Point K)
    (_twoNonzero : (2 : K) ≠ 0)
    (determinantNonzero : pointDeterminant first second third ≠ 0)
    (parallelSides : ParallelogramSideConditions first second third fourth) :
    midpoint first third = midpoint second fourth := by
  rcases parallelSides with ⟨firstParallel, secondParallel⟩
  let errorX := fourth.x - (first.x - second.x + third.x)
  let errorY := fourth.y - (first.y - second.y + third.y)
  have firstLinear :
      (first.y - second.y) * errorX +
        (second.x - first.x) * errorY = 0 := by
    unfold errorX errorY
    calc
      (first.y - second.y) *
            (fourth.x - (first.x - second.x + third.x)) +
          (second.x - first.x) *
            (fourth.y - (first.y - second.y + third.y)) =
        (first.y - second.y) * (fourth.x - third.x) -
          (third.y - fourth.y) * (second.x - first.x) := by ring1
      _ = 0 := firstParallel
  have secondLinear :
      (third.y - second.y) * errorX +
        (second.x - third.x) * errorY = 0 := by
    unfold errorX errorY
    calc
      (third.y - second.y) *
            (fourth.x - (first.x - second.x + third.x)) +
          (second.x - third.x) *
            (fourth.y - (first.y - second.y + third.y)) =
        (second.y - third.y) * (first.x - fourth.x) -
          (fourth.y - first.y) * (third.x - second.x) := by ring1
      _ = 0 := secondParallel
  have xProduct : errorX * pointDeterminant first second third = 0 := by
    unfold pointDeterminant
    calc
      errorX *
          (first.x * second.y - first.x * third.y +
            second.x * third.y - third.x * second.y +
            third.x * first.y - second.x * first.y) =
        -((second.x - third.x) *
              ((first.y - second.y) * errorX +
                (second.x - first.x) * errorY) -
            (second.x - first.x) *
              ((third.y - second.y) * errorX +
                (second.x - third.x) * errorY)) := by ring1
      _ = 0 := by rw [firstLinear, secondLinear]; ring1
  have yProduct : errorY * pointDeterminant first second third = 0 := by
    unfold pointDeterminant
    calc
      errorY *
          (first.x * second.y - first.x * third.y +
            second.x * third.y - third.x * second.y +
            third.x * first.y - second.x * first.y) =
        -((first.y - second.y) *
              ((third.y - second.y) * errorX +
                (second.x - third.x) * errorY) -
            (third.y - second.y) *
              ((first.y - second.y) * errorX +
                (second.x - first.x) * errorY)) := by ring1
      _ = 0 := by rw [firstLinear, secondLinear]; ring1
  have errorXZero : errorX = 0 :=
    eq_zero_of_mul_eq_zero_right determinantNonzero xProduct
  have errorYZero : errorY = 0 :=
    eq_zero_of_mul_eq_zero_right determinantNonzero yProduct
  have fourthX : fourth.x = first.x - second.x + third.x := by
    calc
      fourth.x = errorX + (first.x - second.x + third.x) := by
        unfold errorX
        ring1
      _ = first.x - second.x + third.x := by rw [errorXZero]; ring1
  have fourthY : fourth.y = first.y - second.y + third.y := by
    calc
      fourth.y = errorY + (first.y - second.y + third.y) := by
        unfold errorY
        ring1
      _ = first.y - second.y + third.y := by rw [errorYZero]; ring1
  apply Point.ext
  · change (first.x + third.x) / 2 = (second.x + fourth.x) / 2
    rw [fourthX]
    simp only [RFAP.ExplicitField.div_eq_mul_inv]
    ring1
  · change (first.y + third.y) / 2 = (second.y + fourth.y) / 2
    rw [fourthY]
    simp only [RFAP.ExplicitField.div_eq_mul_inv]
    ring1

/-- The coordinate-sum form of the Parallelogram center theorem.  It is the
finite equality used in the source's proof of Theorem 21 and Exercises
5.4--5.6. -/
theorem parallelogram_coordinate_sums [DecidableEq K]
    (first second third fourth : Point K)
    (twoNonzero : (2 : K) ≠ 0)
    (determinantNonzero : pointDeterminant first second third ≠ 0)
    (parallelSides : ParallelogramSideConditions first second third fourth) :
    first.x + third.x = second.x + fourth.x ∧
      first.y + third.y = second.y + fourth.y := by
  have centersEqual := parallelogram_center first second third fourth
    twoNonzero determinantNonzero parallelSides
  have centerX := congrArg Point.x centersEqual
  have centerY := congrArg Point.y centersEqual
  change (first.x + third.x) / 2 = (second.x + fourth.x) / 2 at centerX
  change (first.y + third.y) / 2 = (second.y + fourth.y) / 2 at centerY
  constructor
  · calc
      first.x + third.x = ((first.x + third.x) / 2) * 2 := by
        rw [RFAP.ExplicitField.div_mul_cancel _ twoNonzero]
      _ = ((second.x + fourth.x) / 2) * 2 := by rw [centerX]
      _ = second.x + fourth.x :=
        RFAP.ExplicitField.div_mul_cancel _ twoNonzero
  · calc
      first.y + third.y = ((first.y + third.y) / 2) * 2 := by
        rw [RFAP.ExplicitField.div_mul_cancel _ twoNonzero]
      _ = ((second.y + fourth.y) / 2) * 2 := by rw [centerY]
      _ = second.y + fourth.y :=
        RFAP.ExplicitField.div_mul_cancel _ twoNonzero

/-- The displayed perpendicular bisector from Theorem 12. -/
def perpendicularBisector [DecidableEq K]
    (first second : Point K) (distinct : first ≠ second) : Line K where
  a := first.x - second.x
  b := first.y - second.y
  c := (second.x ^ 2 - first.x ^ 2 + second.y ^ 2 - first.y ^ 2) / 2
  direction_nonzero := by
    by_cases sameX : first.x = second.x
    · right
      apply sub_ne_zero_of_ne
      intro sameY
      exact distinct (Point.ext sameX sameY)
    · exact Or.inl (sub_ne_zero_of_ne sameX)

/-- Theorem 12: the displayed bisector passes through the midpoint. -/
theorem perpendicularBisector_contains_midpoint [DecidableEq K]
    (first second : Point K) (distinct : first ≠ second) :
    (perpendicularBisector first second distinct).Contains (midpoint first second) := by
  unfold perpendicularBisector midpoint Line.Contains
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  ring1

/-- Theorem 12: the displayed bisector is perpendicular to the side line. -/
theorem perpendicularBisector_perpendicular [DecidableEq K]
    (first second : Point K) (distinct : first ≠ second) :
    (perpendicularBisector first second distinct).Perpendicular
      (lineThrough first second distinct) := by
  unfold perpendicularBisector lineThrough Line.Perpendicular
  ring1

/-- Example 3.8: the source's one-third/two-thirds combination has the printed
coordinate formula. -/
theorem example_3_8 (first second : Point K) :
    affineCombination ((1 : K) / 3) first (2 / 3) second =
      ⟨first.x / 3 + 2 * second.x / 3,
        first.y / 3 + 2 * second.y / 3⟩ := by
  apply Point.ext <;>
    simp only [affineCombination, RFAP.ExplicitField.div_eq_mul_inv] <;>
    ring1

private theorem nestedAffineCombination_eq_three
    (firstWeight secondWeight thirdWeight : K)
    (first second third : Point K)
    (firstNotOne : firstWeight ≠ 1) :
    affineCombination firstWeight first (1 - firstWeight)
        (affineCombination (secondWeight / (1 - firstWeight)) second
          (thirdWeight / (1 - firstWeight)) third) =
      affineCombinationThree firstWeight first secondWeight second
        thirdWeight third := by
  have denominatorNonzero : 1 - firstWeight ≠ 0 := by
    intro denominatorZero
    apply firstNotOne
    calc
      firstWeight = 1 - (1 - firstWeight) := by ring1
      _ = 1 := by rw [denominatorZero]; ring1
  have denominatorCancel :
      (1 - firstWeight) * (1 - firstWeight)⁻¹ = (1 : K) :=
    RFAP.ExplicitField.mul_inv_cancel _ denominatorNonzero
  apply Point.ext
  · unfold affineCombination affineCombinationThree
    simp only [RFAP.ExplicitField.div_eq_mul_inv]
    calc
      firstWeight * first.x +
          (1 - firstWeight) *
            (secondWeight * (1 - firstWeight)⁻¹ * second.x +
              thirdWeight * (1 - firstWeight)⁻¹ * third.x) =
        firstWeight * first.x +
          ((1 - firstWeight) * (1 - firstWeight)⁻¹) *
            (secondWeight * second.x + thirdWeight * third.x) := by
              ring1
      _ = firstWeight * first.x + secondWeight * second.x +
          thirdWeight * third.x := by
            rw [denominatorCancel]
            ring1
  · unfold affineCombination affineCombinationThree
    simp only [RFAP.ExplicitField.div_eq_mul_inv]
    calc
      firstWeight * first.y +
          (1 - firstWeight) *
            (secondWeight * (1 - firstWeight)⁻¹ * second.y +
              thirdWeight * (1 - firstWeight)⁻¹ * third.y) =
        firstWeight * first.y +
          ((1 - firstWeight) * (1 - firstWeight)⁻¹) *
            (secondWeight * second.y + thirdWeight * third.y) := by
              ring1
      _ = firstWeight * first.y + secondWeight * second.y +
          thirdWeight * third.y := by
            rw [denominatorCancel]
            ring1

private theorem nestedAffineWeights_sum
    (firstWeight secondWeight thirdWeight : K)
    (weightsSum : firstWeight + secondWeight + thirdWeight = 1)
    (firstNotOne : firstWeight ≠ 1) :
    secondWeight / (1 - firstWeight) +
        thirdWeight / (1 - firstWeight) = 1 := by
  have denominatorNonzero : 1 - firstWeight ≠ 0 := by
    intro denominatorZero
    apply firstNotOne
    calc
      firstWeight = 1 - (1 - firstWeight) := by ring1
      _ = 1 := by rw [denominatorZero]; ring1
  have denominatorCancel :
      (1 - firstWeight) * (1 - firstWeight)⁻¹ = (1 : K) :=
    RFAP.ExplicitField.mul_inv_cancel _ denominatorNonzero
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  have remainingWeights :
      secondWeight + thirdWeight = 1 - firstWeight := by
    calc
      secondWeight + thirdWeight =
          (firstWeight + secondWeight + thirdWeight) - firstWeight := by
            ring1
      _ = 1 - firstWeight := by rw [weightsSum]
  calc
    secondWeight * (1 - firstWeight)⁻¹ +
        thirdWeight * (1 - firstWeight)⁻¹ =
      (secondWeight + thirdWeight) * (1 - firstWeight)⁻¹ := by
        ring1
    _ = (1 - firstWeight) * (1 - firstWeight)⁻¹ := by
      rw [remainingWeights]
    _ = 1 := denominatorCancel

/-- Exercise 3.15: all three cyclic nestings of a three-point affine
combination have normalized inner weights and evaluate to the same explicit
three-point combination. -/
theorem exercise_3_15
    (firstWeight secondWeight thirdWeight : K)
    (first second third : Point K)
    (weightsSum : firstWeight + secondWeight + thirdWeight = 1)
    (firstNotOne : firstWeight ≠ 1)
    (secondNotOne : secondWeight ≠ 1)
    (thirdNotOne : thirdWeight ≠ 1) :
    (secondWeight / (1 - firstWeight) +
        thirdWeight / (1 - firstWeight) = 1) ∧
      (thirdWeight / (1 - secondWeight) +
        firstWeight / (1 - secondWeight) = 1) ∧
      (firstWeight / (1 - thirdWeight) +
        secondWeight / (1 - thirdWeight) = 1) ∧
      affineCombination firstWeight first (1 - firstWeight)
          (affineCombination (secondWeight / (1 - firstWeight)) second
            (thirdWeight / (1 - firstWeight)) third) =
        affineCombinationThree firstWeight first secondWeight second
          thirdWeight third ∧
      affineCombination secondWeight second (1 - secondWeight)
          (affineCombination (thirdWeight / (1 - secondWeight)) third
            (firstWeight / (1 - secondWeight)) first) =
        affineCombinationThree firstWeight first secondWeight second
          thirdWeight third ∧
      affineCombination thirdWeight third (1 - thirdWeight)
          (affineCombination (firstWeight / (1 - thirdWeight)) first
            (secondWeight / (1 - thirdWeight)) second) =
        affineCombinationThree firstWeight first secondWeight second
          thirdWeight third := by
  have secondCyclicSum :
      secondWeight + thirdWeight + firstWeight = 1 := by
    calc
      secondWeight + thirdWeight + firstWeight =
          firstWeight + secondWeight + thirdWeight := by ring1
      _ = 1 := weightsSum
  have thirdCyclicSum :
      thirdWeight + firstWeight + secondWeight = 1 := by
    calc
      thirdWeight + firstWeight + secondWeight =
          firstWeight + secondWeight + thirdWeight := by ring1
      _ = 1 := weightsSum
  exact ⟨
    nestedAffineWeights_sum firstWeight secondWeight thirdWeight
      weightsSum firstNotOne,
    nestedAffineWeights_sum secondWeight thirdWeight firstWeight
      secondCyclicSum secondNotOne,
    nestedAffineWeights_sum thirdWeight firstWeight secondWeight
      thirdCyclicSum thirdNotOne,
    nestedAffineCombination_eq_three firstWeight secondWeight thirdWeight
      first second third firstNotOne,
    by
      have cyclic := nestedAffineCombination_eq_three
        secondWeight thirdWeight firstWeight second third first
        secondNotOne
      exact cyclic.trans (by
        apply Point.ext <;>
          unfold affineCombinationThree <;>
          ring1),
    by
      have cyclic := nestedAffineCombination_eq_three
        thirdWeight firstWeight secondWeight third first second
        thirdNotOne
      exact cyclic.trans (by
        apply Point.ext <;>
          unfold affineCombinationThree <;>
          ring1)⟩

/-- The midpoint quadrilateral has parallel opposite sides for any four
displayed points.  This is the division-free core of Exercise 3.17 (often
called Varignon's theorem). -/
theorem midpoint_quadrilateral_side_conditions
    (first second third fourth : Point K) :
    ParallelogramSideConditions
      (midpoint first second) (midpoint second third)
      (midpoint third fourth) (midpoint first fourth) := by
  unfold ParallelogramSideConditions midpoint
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  constructor <;> ring1

/-- If the two diagonal midpoints of four points agree, then the two diagonal
midpoints of their side-midpoint quadrilateral agree with that same point. -/
theorem midpoint_quadrilateral_same_center
    (first second third fourth : Point K)
    (twoNonzero : (2 : K) ≠ 0)
    (originalCenter : midpoint first third = midpoint second fourth) :
    midpoint (midpoint first second) (midpoint third fourth) =
        midpoint first third ∧
      midpoint (midpoint second third) (midpoint first fourth) =
        midpoint first third := by
  have twoInverse : (2 : K) * (2 : K)⁻¹ = 1 :=
    RFAP.ExplicitField.mul_inv_cancel 2 twoNonzero
  have centerX := congrArg Point.x originalCenter
  have centerY := congrArg Point.y originalCenter
  simp only [midpoint, RFAP.ExplicitField.div_eq_mul_inv] at centerX centerY
  constructor
  · apply Point.ext
    · simp only [midpoint, RFAP.ExplicitField.div_eq_mul_inv]
      calc
        ((first.x + second.x) * (2 : K)⁻¹ +
              (third.x + fourth.x) * (2 : K)⁻¹) * (2 : K)⁻¹ =
            ((first.x + third.x) * (2 : K)⁻¹ +
              (second.x + fourth.x) * (2 : K)⁻¹) * (2 : K)⁻¹ := by
                ring1
        _ = ((first.x + third.x) * (2 : K)⁻¹ +
              (first.x + third.x) * (2 : K)⁻¹) * (2 : K)⁻¹ := by
                rw [← centerX]
        _ = (first.x + third.x) * (2 : K)⁻¹ := by
          calc
            ((first.x + third.x) * (2 : K)⁻¹ +
                  (first.x + third.x) * (2 : K)⁻¹) * (2 : K)⁻¹ =
                (first.x + third.x) * (2 : K)⁻¹ *
                  (2 * (2 : K)⁻¹) := by
                    ring1
            _ = (first.x + third.x) * (2 : K)⁻¹ := by
              rw [twoInverse]
              ring1
    · simp only [midpoint, RFAP.ExplicitField.div_eq_mul_inv]
      calc
        ((first.y + second.y) * (2 : K)⁻¹ +
              (third.y + fourth.y) * (2 : K)⁻¹) * (2 : K)⁻¹ =
            ((first.y + third.y) * (2 : K)⁻¹ +
              (second.y + fourth.y) * (2 : K)⁻¹) * (2 : K)⁻¹ := by
                ring1
        _ = ((first.y + third.y) * (2 : K)⁻¹ +
              (first.y + third.y) * (2 : K)⁻¹) * (2 : K)⁻¹ := by
                rw [← centerY]
        _ = (first.y + third.y) * (2 : K)⁻¹ := by
          calc
            ((first.y + third.y) * (2 : K)⁻¹ +
                  (first.y + third.y) * (2 : K)⁻¹) * (2 : K)⁻¹ =
                (first.y + third.y) * (2 : K)⁻¹ *
                  (2 * (2 : K)⁻¹) := by
                    ring1
            _ = (first.y + third.y) * (2 : K)⁻¹ := by
              rw [twoInverse]
              ring1
  · apply Point.ext
    · simp only [midpoint, RFAP.ExplicitField.div_eq_mul_inv]
      calc
        ((second.x + third.x) * (2 : K)⁻¹ +
              (first.x + fourth.x) * (2 : K)⁻¹) * (2 : K)⁻¹ =
            ((first.x + third.x) * (2 : K)⁻¹ +
              (second.x + fourth.x) * (2 : K)⁻¹) * (2 : K)⁻¹ := by
                ring1
        _ = ((first.x + third.x) * (2 : K)⁻¹ +
              (first.x + third.x) * (2 : K)⁻¹) * (2 : K)⁻¹ := by
                rw [← centerX]
        _ = (first.x + third.x) * (2 : K)⁻¹ := by
          calc
            ((first.x + third.x) * (2 : K)⁻¹ +
                  (first.x + third.x) * (2 : K)⁻¹) * (2 : K)⁻¹ =
                (first.x + third.x) * (2 : K)⁻¹ *
                  (2 * (2 : K)⁻¹) := by
                    ring1
            _ = (first.x + third.x) * (2 : K)⁻¹ := by
              rw [twoInverse]
              ring1
    · simp only [midpoint, RFAP.ExplicitField.div_eq_mul_inv]
      calc
        ((second.y + third.y) * (2 : K)⁻¹ +
              (first.y + fourth.y) * (2 : K)⁻¹) * (2 : K)⁻¹ =
            ((first.y + third.y) * (2 : K)⁻¹ +
              (second.y + fourth.y) * (2 : K)⁻¹) * (2 : K)⁻¹ := by
                ring1
        _ = ((first.y + third.y) * (2 : K)⁻¹ +
              (first.y + third.y) * (2 : K)⁻¹) * (2 : K)⁻¹ := by
                rw [← centerY]
        _ = (first.y + third.y) * (2 : K)⁻¹ := by
          calc
            ((first.y + third.y) * (2 : K)⁻¹ +
                  (first.y + third.y) * (2 : K)⁻¹) * (2 : K)⁻¹ =
                (first.y + third.y) * (2 : K)⁻¹ *
                  (2 * (2 : K)⁻¹) := by
                    ring1
            _ = (first.y + third.y) * (2 : K)⁻¹ := by
              rw [twoInverse]
              ring1

/-- A nondegenerate parallelogram has a nondegenerate side-midpoint
parallelogram.  The new first-three-point determinant is one half of the
original determinant; the proof retains that relation in multiplied form. -/
theorem midpoint_quadrilateral_determinant_ne_zero [DecidableEq K]
    (first second third fourth : Point K)
    (twoNonzero : (2 : K) ≠ 0)
    (determinantNonzero : pointDeterminant first second third ≠ 0)
    (parallelSides : ParallelogramSideConditions first second third fourth) :
    pointDeterminant
      (midpoint first second) (midpoint second third)
      (midpoint third fourth) ≠ 0 := by
  have originalCenter := parallelogram_center first second third fourth
    twoNonzero determinantNonzero parallelSides
  have centerX := congrArg Point.x originalCenter
  have centerY := congrArg Point.y originalCenter
  change (first.x + third.x) / 2 = (second.x + fourth.x) / 2 at centerX
  change (first.y + third.y) / 2 = (second.y + fourth.y) / 2 at centerY
  have xSums : first.x + third.x = second.x + fourth.x := by
    calc
      first.x + third.x = ((first.x + third.x) / 2) * 2 := by
        rw [RFAP.ExplicitField.div_mul_cancel _ twoNonzero]
      _ = ((second.x + fourth.x) / 2) * 2 := by rw [centerX]
      _ = second.x + fourth.x :=
        RFAP.ExplicitField.div_mul_cancel _ twoNonzero
  have ySums : first.y + third.y = second.y + fourth.y := by
    calc
      first.y + third.y = ((first.y + third.y) / 2) * 2 := by
        rw [RFAP.ExplicitField.div_mul_cancel _ twoNonzero]
      _ = ((second.y + fourth.y) / 2) * 2 := by rw [centerY]
      _ = second.y + fourth.y :=
        RFAP.ExplicitField.div_mul_cancel _ twoNonzero
  have fourthX : fourth.x = first.x - second.x + third.x := by
    calc
      fourth.x = first.x + third.x - second.x := by
        rw [xSums]
        ring1
      _ = first.x - second.x + third.x := by ring1
  have fourthY : fourth.y = first.y - second.y + third.y := by
    calc
      fourth.y = first.y + third.y - second.y := by
        rw [ySums]
        ring1
      _ = first.y - second.y + third.y := by ring1
  have twoInverse : (2 : K) * (2 : K)⁻¹ = 1 :=
    RFAP.ExplicitField.mul_inv_cancel 2 twoNonzero
  have determinantFormula :
      pointDeterminant
          (midpoint first second) (midpoint second third)
          (midpoint third fourth) * 2 =
        pointDeterminant first second third := by
    calc
      pointDeterminant
            (midpoint first second) (midpoint second third)
            (midpoint third fourth) * 2 =
          pointDeterminant first second third *
            ((2 * (2 : K)⁻¹) * (2 * (2 : K)⁻¹)) := by
              unfold pointDeterminant midpoint
              simp only [RFAP.ExplicitField.div_eq_mul_inv]
              rw [fourthX, fourthY]
              ring1
      _ = pointDeterminant first second third := by
        rw [twoInverse]
        ring1
  intro midpointDeterminantZero
  apply determinantNonzero
  calc
    pointDeterminant first second third =
        pointDeterminant
          (midpoint first second) (midpoint second third)
          (midpoint third fourth) * 2 := determinantFormula.symm
    _ = 0 := by rw [midpointDeterminantZero]; ring1

/-- Exercise 3.17: the four side midpoints of a nondegenerate parallelogram
again satisfy the finite parallelogram certificate, and both of its diagonal
midpoints are the original parallelogram center. -/
theorem exercise_3_17 [DecidableEq K]
    (first second third fourth : Point K)
    (twoNonzero : (2 : K) ≠ 0)
    (determinantNonzero : pointDeterminant first second third ≠ 0)
    (parallelSides : ParallelogramSideConditions first second third fourth) :
    pointDeterminant
        (midpoint first second) (midpoint second third)
        (midpoint third fourth) ≠ 0 ∧
      ParallelogramSideConditions
        (midpoint first second) (midpoint second third)
        (midpoint third fourth) (midpoint first fourth) ∧
      midpoint (midpoint first second) (midpoint third fourth) =
          midpoint first third ∧
        midpoint (midpoint second third) (midpoint first fourth) =
          midpoint first third := by
  have originalCenter := parallelogram_center first second third fourth
    twoNonzero determinantNonzero parallelSides
  exact ⟨
    midpoint_quadrilateral_determinant_ne_zero first second third fourth
      twoNonzero determinantNonzero parallelSides,
    midpoint_quadrilateral_side_conditions first second third fourth,
    midpoint_quadrilateral_same_center first second third fourth
      twoNonzero originalCenter⟩

end DivineProportions
