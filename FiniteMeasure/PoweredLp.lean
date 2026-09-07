import mathlib.Tactic.QuotientFreeRing
import FiniteMeasure.L1
import FiniteMeasure.ContentIntegral

/-!
# Root-free finite Lp bounds

Square roots of rational second moments need not be rational.  The primitive
L2 quantity here is therefore the exact powered norm `integral (f^2)`.  Its
Cauchy--Schwarz inequality is stated after squaring, and so remains wholly
rational and executable.
-/

namespace FiniteMeasure

/-- Algebraic Cauchy--Schwarz from nonnegativity of every displayed rational
quadratic combination. -/
theorem quadratic_cauchy_sq_le
    (leftSq rightSq mixed : Coordinate)
    (leftNonnegative : 0 ≤ leftSq)
    (rightNonnegative : 0 ≤ rightSq)
    (quadraticNonnegative : ∀ leftFactor rightFactor : Coordinate,
      0 ≤ leftFactor ^ 2 * leftSq + rightFactor ^ 2 * rightSq +
        2 * leftFactor * rightFactor * mixed) :
    mixed ^ 2 ≤ leftSq * rightSq := by
  by_cases rightZero : rightSq = 0
  · by_cases leftZero : leftSq = 0
    · have plusNonnegative := quadraticNonnegative 1 1
      have minusNonnegative := quadraticNonnegative 1 (-1)
      rw [leftZero, rightZero] at plusNonnegative minusNonnegative
      have plusFormula :
          (1 : Coordinate) ^ 2 * 0 + 1 ^ 2 * 0 +
              2 * 1 * 1 * mixed = 2 * mixed := by
        ring1
      have minusFormula :
          (1 : Coordinate) ^ 2 * 0 + (-1) ^ 2 * 0 +
              2 * 1 * (-1) * mixed = -2 * mixed := by
        ring1
      rw [plusFormula] at plusNonnegative
      rw [minusFormula] at minusNonnegative
      have mixedNonnegative : 0 ≤ mixed := by
        apply RFAP.ConstructiveFraction.le_of_mul_le_mul_right_direct
          (c := (2 : Coordinate))
        · calc
            0 * 2 = 0 := by ring1
            _ ≤ 2 * mixed := plusNonnegative
            _ = mixed * 2 := by ring1
        · decide
      have mixedNonpositive : mixed ≤ 0 := by
        apply RFAP.ConstructiveFraction.le_of_mul_le_mul_right_direct
          (c := (2 : Coordinate))
        · have doubledNonpositive : 2 * mixed ≤ 0 :=
            RFAP.ConstructiveFraction.le_of_sub_nonneg_direct (by
              calc
                0 ≤ -2 * mixed := minusNonnegative
                _ = 0 - 2 * mixed := by ring1)
          calc
            mixed * 2 = 2 * mixed := by ring1
            _ ≤ 0 := doubledNonpositive
            _ = 0 * 2 := by ring1
        · decide
      have mixedZero : mixed = 0 :=
        RFAP.ConstructiveFraction.le_antisymm _ _
          mixedNonpositive mixedNonnegative
      rw [mixedZero, leftZero, rightZero]
      exact le_rfl
    · have leftPositive : 0 < leftSq :=
        lt_of_le_of_ne leftNonnegative (Ne.symm leftZero)
      have combinationNonnegative := quadraticNonnegative (-mixed) leftSq
      have factored :
          (-mixed) ^ 2 * leftSq + leftSq ^ 2 * rightSq +
                2 * (-mixed) * leftSq * mixed =
            (leftSq * rightSq - mixed ^ 2) * leftSq := by
        ring1
      rw [factored] at combinationNonnegative
      have differenceNonnegative :
          0 ≤ leftSq * rightSq - mixed ^ 2 := by
        apply RFAP.ConstructiveFraction.le_of_mul_le_mul_right_direct
          (c := leftSq)
        · simpa only [zero_mul] using combinationNonnegative
        · exact leftPositive
      exact RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
        differenceNonnegative
  · have rightPositive : 0 < rightSq :=
      lt_of_le_of_ne rightNonnegative (Ne.symm rightZero)
    have combinationNonnegative := quadraticNonnegative rightSq (-mixed)
    have factored :
        rightSq ^ 2 * leftSq + (-mixed) ^ 2 * rightSq +
              2 * rightSq * (-mixed) * mixed =
          (leftSq * rightSq - mixed ^ 2) * rightSq := by
      ring1
    rw [factored] at combinationNonnegative
    have differenceNonnegative :
        0 ≤ leftSq * rightSq - mixed ^ 2 := by
      apply RFAP.ConstructiveFraction.le_of_mul_le_mul_right_direct
        (c := rightSq)
      · simpa only [zero_mul] using combinationNonnegative
      · exact rightPositive
    exact RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
      differenceNonnegative

namespace FiniteContent

/-- Exact rational square of the would-be finite L2 norm. -/
def poweredL2 {α : Type} (content : FiniteContent α)
    (value : α → Coordinate) : Coordinate :=
  content.integral fun item => value item ^ 2

/-- Pointwise-equal observables have the same exact powered-L2 value. -/
theorem poweredL2_congr {α : Type} (content : FiniteContent α)
    (left right : α → Coordinate)
    (pointwise : ∀ item, left item = right item) :
    content.poweredL2 left = content.poweredL2 right := by
  unfold poweredL2
  exact content.integral_congr _ _ (fun item =>
    congrArg (fun value => value ^ 2) (pointwise item))

/-- Exact finite bilinear integral. -/
def productIntegral {α : Type} (content : FiniteContent α)
    (left right : α → Coordinate) : Coordinate :=
  content.integral fun item => left item * right item

theorem poweredL2_nonnegative {α : Type} (content : FiniteContent α)
    (value : α → Coordinate) :
    0 ≤ content.poweredL2 value := by
  apply content.integral_nonneg
  intro atom member
  exact RFAP.ConstructiveFraction.sq_nonneg_direct _

@[simp] theorem poweredL2_zero {α : Type} (content : FiniteContent α) :
    content.poweredL2 (fun _ => 0) = 0 := by
  unfold poweredL2
  calc
    content.integral (fun _ : α => (0 : Coordinate) ^ 2) =
        content.integral (fun _ => (0 : Coordinate)) :=
      content.integral_congr _ _ (fun item => by ring1)
    _ = content.total * 0 := content.integral_constant 0
    _ = 0 := mul_zero _

theorem poweredL2_scale {α : Type} (content : FiniteContent α)
    (factor : Coordinate) (value : α → Coordinate) :
    content.poweredL2 (fun item => factor * value item) =
      factor ^ 2 * content.poweredL2 value := by
  unfold poweredL2
  calc
    content.integral (fun item => (factor * value item) ^ 2) =
        content.integral (fun item => factor ^ 2 * value item ^ 2) :=
      content.integral_congr _ _ (fun item => by ring1)
    _ = factor ^ 2 * content.integral (fun item => value item ^ 2) :=
      content.integral_scale _ _

theorem productIntegral_symm {α : Type} (content : FiniteContent α)
    (left right : α → Coordinate) :
    content.productIntegral left right =
      content.productIntegral right left := by
  unfold productIntegral
  exact content.integral_congr _ _ (fun item => by ring1)

/-- Exact quadratic expansion for rational linear combinations. -/
theorem poweredL2_linearCombination {α : Type}
    (content : FiniteContent α) (leftFactor rightFactor : Coordinate)
    (left right : α → Coordinate) :
    content.poweredL2 (fun item =>
        leftFactor * left item + rightFactor * right item) =
      leftFactor ^ 2 * content.poweredL2 left +
        rightFactor ^ 2 * content.poweredL2 right +
        2 * leftFactor * rightFactor *
          content.productIntegral left right := by
  unfold poweredL2 productIntegral
  calc
    content.integral (fun item =>
        (leftFactor * left item + rightFactor * right item) ^ 2) =
        content.integral (fun item =>
          leftFactor ^ 2 * left item ^ 2 +
            rightFactor ^ 2 * right item ^ 2 +
            (2 * leftFactor * rightFactor) *
              (left item * right item)) :=
      content.integral_congr _ _ (fun item => by ring1)
    _ = leftFactor ^ 2 * content.integral (fun item => left item ^ 2) +
          rightFactor ^ 2 * content.integral (fun item => right item ^ 2) +
          2 * leftFactor * rightFactor *
            content.integral (fun item => left item * right item) := by
      rw [content.integral_add, content.integral_add,
        content.integral_scale, content.integral_scale,
        content.integral_scale]

/-- Root-free finite weighted Cauchy--Schwarz, equivalently the p=q=2
Hölder inequality without taking irrational square roots. -/
theorem productIntegral_sq_le_poweredL2_mul {α : Type}
    (content : FiniteContent α) (left right : α → Coordinate) :
    content.productIntegral left right ^ 2 ≤
      content.poweredL2 left * content.poweredL2 right := by
  apply quadratic_cauchy_sq_le
  · exact content.poweredL2_nonnegative left
  · exact content.poweredL2_nonnegative right
  · intro leftFactor rightFactor
    rw [← content.poweredL2_linearCombination leftFactor rightFactor
      left right]
    exact content.poweredL2_nonnegative _

/-- Exact powered-L2 addition formula. -/
theorem poweredL2_add {α : Type} (content : FiniteContent α)
    (left right : α → Coordinate) :
    content.poweredL2 (fun item => left item + right item) =
      content.poweredL2 left + content.poweredL2 right +
        2 * content.productIntegral left right := by
  have formula := content.poweredL2_linearCombination 1 1 left right
  calc
    content.poweredL2 (fun item => left item + right item) =
        content.poweredL2 (fun item =>
          1 * left item + 1 * right item) :=
      content.poweredL2_congr _ _ (fun item => by ring1)
    _ =
        1 ^ 2 * content.poweredL2 left +
          1 ^ 2 * content.poweredL2 right +
          2 * 1 * 1 * content.productIntegral left right := formula
    _ = content.poweredL2 left + content.poweredL2 right +
          2 * content.productIntegral left right := by
      ring1

/-- Constructive Minkowski with displayed rational radius certificates.  No
square root is selected: callers provide rational upper radii for the two
powered L2 quantities. -/
theorem poweredL2_add_le_radius_add_sq {α : Type}
    (content : FiniteContent α) (left right : α → Coordinate)
    (leftRadius rightRadius : Coordinate)
    (leftRadiusNonnegative : 0 ≤ leftRadius)
    (rightRadiusNonnegative : 0 ≤ rightRadius)
    (leftBound : content.poweredL2 left ≤ leftRadius ^ 2)
    (rightBound : content.poweredL2 right ≤ rightRadius ^ 2) :
    content.poweredL2 (fun item => left item + right item) ≤
      (leftRadius + rightRadius) ^ 2 := by
  have rightPowerNonnegative := content.poweredL2_nonnegative right
  have radiusProductNonnegative : 0 ≤ leftRadius * rightRadius :=
    RFAP.ConstructiveFraction.mul_nonneg_direct
      leftRadiusNonnegative rightRadiusNonnegative
  have productSquares := content.productIntegral_sq_le_poweredL2_mul
    left right
  have momentProductBound :
      content.poweredL2 left * content.poweredL2 right ≤
        leftRadius ^ 2 * rightRadius ^ 2 := by
    calc
      content.poweredL2 left * content.poweredL2 right ≤
          leftRadius ^ 2 * content.poweredL2 right :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
          leftBound rightPowerNonnegative
      _ ≤ leftRadius ^ 2 * rightRadius ^ 2 :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          rightBound (RFAP.ConstructiveFraction.sq_nonneg_direct leftRadius)
  have mixedSquareBound :
      content.productIntegral left right ^ 2 ≤
        (leftRadius * rightRadius) ^ 2 := by
    calc
      content.productIntegral left right ^ 2 ≤
          content.poweredL2 left * content.poweredL2 right := productSquares
      _ ≤ leftRadius ^ 2 * rightRadius ^ 2 := momentProductBound
      _ = (leftRadius * rightRadius) ^ 2 := by ring1
  have mixedBound : content.productIntegral left right ≤
      leftRadius * rightRadius :=
    RFAP.ConstructiveFraction.le_of_sq_le_sq_direct
      radiusProductNonnegative mixedSquareBound
  rw [content.poweredL2_add]
  calc
    content.poweredL2 left + content.poweredL2 right +
          2 * content.productIntegral left right ≤
        leftRadius ^ 2 + rightRadius ^ 2 +
          2 * (leftRadius * rightRadius) := by
      exact add_le_add (add_le_add leftBound rightBound)
        (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          mixedBound (by decide))
    _ = (leftRadius + rightRadius) ^ 2 := by ring1

/-- Squared L2 separation, retained as a rational powered distance. -/
def poweredL2Distance {α : Type} (content : FiniteContent α)
    (left right : α → Coordinate) : Coordinate :=
  content.poweredL2 fun item => left item - right item

theorem poweredL2Distance_nonnegative {α : Type}
    (content : FiniteContent α) (left right : α → Coordinate) :
    0 ≤ content.poweredL2Distance left right :=
  content.poweredL2_nonnegative _

@[simp] theorem poweredL2Distance_refl {α : Type}
    (content : FiniteContent α) (value : α → Coordinate) :
    content.poweredL2Distance value value = 0 := by
  unfold poweredL2Distance poweredL2
  calc
    content.integral (fun item => (value item - value item) ^ 2) =
        content.integral (fun _ => (0 : Coordinate)) :=
      content.integral_congr _ _ (fun item => by ring1)
    _ = content.total * 0 := content.integral_constant 0
    _ = 0 := mul_zero _

theorem poweredL2Distance_symm {α : Type} (content : FiniteContent α)
    (left right : α → Coordinate) :
    content.poweredL2Distance left right =
      content.poweredL2Distance right left := by
  unfold poweredL2Distance poweredL2
  exact content.integral_congr _ _ (fun item => by ring1)

theorem poweredL2Distance_scale {α : Type}
    (content : FiniteContent α) (factor : Coordinate)
    (left right : α → Coordinate) :
    content.poweredL2Distance
        (fun item => factor * left item)
        (fun item => factor * right item) =
      factor ^ 2 * content.poweredL2Distance left right := by
  unfold poweredL2Distance
  calc
    content.poweredL2 (fun item =>
        factor * left item - factor * right item) =
        content.poweredL2 (fun item => factor * (left item - right item)) :=
      content.poweredL2_congr _ _ (fun item => by ring1)
    _ = factor ^ 2 * content.poweredL2 (fun item =>
          left item - right item) :=
      content.poweredL2_scale factor _

/-- Root-free triangle certificate for powered L2 distance.  The supplied
radii bound the two legs; the conclusion bounds the third by the square of
their sum. -/
theorem poweredL2Distance_le_radius_add_sq {α : Type}
    (content : FiniteContent α) (left middle right : α → Coordinate)
    (leftRadius rightRadius : Coordinate)
    (leftRadiusNonnegative : 0 ≤ leftRadius)
    (rightRadiusNonnegative : 0 ≤ rightRadius)
    (leftBound : content.poweredL2Distance left middle ≤ leftRadius ^ 2)
    (rightBound : content.poweredL2Distance middle right ≤ rightRadius ^ 2) :
    content.poweredL2Distance left right ≤
      (leftRadius + rightRadius) ^ 2 := by
  have bound := content.poweredL2_add_le_radius_add_sq
    (fun item => left item - middle item)
    (fun item => middle item - right item)
    leftRadius rightRadius leftRadiusNonnegative rightRadiusNonnegative
    leftBound rightBound
  calc
    content.poweredL2Distance left right =
        content.poweredL2 (fun item =>
          (left item - middle item) + (middle item - right item)) := by
      unfold poweredL2Distance
      exact content.poweredL2_congr _ _ (fun item => by ring1)
    _ ≤ (leftRadius + rightRadius) ^ 2 := bound

/-- The L1 powered norm, kept rational by using rational separation from
zero rather than an ambient absolute-value completion. -/
def poweredL1 {α : Type} (content : FiniteContent α)
    (value : α → Coordinate) : Coordinate :=
  content.integral fun item => rationalSeparation (value item) 0

/-- Pointwise-equal observables have the same exact powered-L1 value. -/
theorem poweredL1_congr {α : Type} (content : FiniteContent α)
    (left right : α → Coordinate)
    (pointwise : ∀ item, left item = right item) :
    content.poweredL1 left = content.poweredL1 right := by
  unfold poweredL1
  exact content.integral_congr _ _ (fun item =>
    congrArg (fun value => rationalSeparation value 0) (pointwise item))

theorem poweredL1_nonnegative {α : Type} (content : FiniteContent α)
    (value : α → Coordinate) :
    0 ≤ content.poweredL1 value := by
  apply content.integral_nonneg
  intro atom member
  exact rationalSeparation_nonneg _ _

theorem poweredL1_zero {α : Type} (content : FiniteContent α) :
    content.poweredL1 (fun _ => 0) = 0 := by
  unfold poweredL1
  calc
    content.integral (fun _ : α => rationalSeparation 0 0) =
        content.integral (fun _ => (0 : Coordinate)) :=
      content.integral_congr _ _ (fun item => rfl)
    _ = content.total * 0 := content.integral_constant 0
    _ = 0 := mul_zero _

theorem poweredL1_constant {α : Type} (content : FiniteContent α)
    (constant : Coordinate) :
    content.poweredL1 (fun _ => constant) =
      content.total * rationalSeparation constant 0 := by
  unfold poweredL1
  exact content.integral_constant _

/-- Exact rational homogeneity of finite powered L1. -/
theorem poweredL1_scale {α : Type} (content : FiniteContent α)
    (factor : Coordinate) (value : α → Coordinate) :
    content.poweredL1 (fun item => factor * value item) =
      rationalSeparation factor 0 * content.poweredL1 value := by
  unfold poweredL1
  calc
    content.integral (fun item =>
        rationalSeparation (factor * value item) 0) =
        content.integral (fun item => rationalSeparation factor 0 *
          rationalSeparation (value item) 0) :=
      content.integral_congr _ _ (fun item =>
        rationalSeparation_mul_zero factor (value item))
    _ = rationalSeparation factor 0 * content.integral (fun item =>
          rationalSeparation (value item) 0) :=
      content.integral_scale _ _

theorem poweredL1_neg {α : Type} (content : FiniteContent α)
    (value : α → Coordinate) :
    content.poweredL1 (fun item => -value item) =
      content.poweredL1 value := by
  have scaled := content.poweredL1_scale (-1) value
  calc
    content.poweredL1 (fun item => -value item) =
        content.poweredL1 (fun item => (-1) * value item) :=
      content.poweredL1_congr _ _ (fun item => by ring1)
    _ = rationalSeparation (-1) 0 * content.poweredL1 value := scaled
    _ = content.poweredL1 value := by
      rw [show rationalSeparation (-1) 0 = 1 by decide, one_mul]

/-- Minkowski's inequality in the root-free finite L1 case. -/
theorem poweredL1_add_le {α : Type} (content : FiniteContent α)
    (left right : α → Coordinate) :
    content.poweredL1 (fun item => left item + right item) ≤
      content.poweredL1 left + content.poweredL1 right := by
  unfold poweredL1
  calc
    content.integral (fun item =>
          rationalSeparation (left item + right item) 0) ≤
        content.integral (fun item =>
          rationalSeparation (left item) 0 +
            rationalSeparation (right item) 0) := by
      apply content.integral_mono
      intro atom member
      exact rationalSeparation_add_zero_le
        (left atom.item) (right atom.item)
    _ = content.integral (fun item => rationalSeparation (left item) 0) +
          content.integral (fun item => rationalSeparation (right item) 0) :=
      content.integral_add _ _

theorem poweredL1_sub_le {α : Type} (content : FiniteContent α)
    (left right : α → Coordinate) :
    content.poweredL1 (fun item => left item - right item) ≤
      content.poweredL1 left + content.poweredL1 right := by
  have bound := content.poweredL1_add_le left (fun item => -right item)
  rw [content.poweredL1_neg] at bound
  calc
    content.poweredL1 (fun item => left item - right item) =
        content.poweredL1 (fun item => left item + -right item) :=
      content.poweredL1_congr _ _ (fun item => by ring1)
    _ ≤ content.poweredL1 left + content.poweredL1 right := bound

theorem poweredL1_eq_l1Distance_zero {α : Type}
    (content : FiniteContent α) (value : α → Coordinate) :
    content.poweredL1 value = content.l1Distance value (fun _ => 0) := rfl

/-- Reverse triangle stability of finite powered-L1 magnitudes. -/
theorem poweredL1_separation_le_l1Distance {α : Type}
    (content : FiniteContent α) (left right : α → Coordinate) :
    rationalSeparation (content.poweredL1 left) (content.poweredL1 right) ≤
      content.l1Distance left right := by
  rw [content.poweredL1_eq_l1Distance_zero,
    content.poweredL1_eq_l1Distance_zero]
  exact content.l1Distance_reverse_triangle left right (fun _ => 0)

/-- The powered L1 norm of an explicit difference is its finite L1
distance. -/
theorem poweredL1_sub_eq_l1Distance {α : Type}
    (content : FiniteContent α) (left right : α → Coordinate) :
    content.poweredL1 (fun item => left item - right item) =
      content.l1Distance left right := by
  unfold poweredL1 l1Distance
  exact content.integral_congr _ _ (fun item =>
    (rationalSeparation_eq_sub_zero (left item) (right item)).symm)

/-- Root-free L1--L-infinity Hölder: a displayed pointwise ceiling controls
the L1 size of a product. -/
theorem poweredL1_mul_le_of_right_bounded {α : Type}
    (content : FiniteContent α) (left right : α → Coordinate)
    (ceiling : Coordinate) (_ceilingNonnegative : 0 ≤ ceiling)
    (bounded : ∀ atom, atom ∈ content.atoms →
      rationalSeparation (right atom.item) 0 ≤ ceiling) :
    content.poweredL1 (fun item => left item * right item) ≤
      ceiling * content.poweredL1 left := by
  unfold poweredL1
  calc
    content.integral (fun item =>
          rationalSeparation (left item * right item) 0) =
        content.integral (fun item =>
          rationalSeparation (left item) 0 *
            rationalSeparation (right item) 0) := by
      exact content.integral_congr _ _ (fun item =>
        rationalSeparation_mul_zero (left item) (right item))
    _ ≤ content.integral (fun item =>
          rationalSeparation (left item) 0 * ceiling) := by
      apply content.integral_mono
      intro atom member
      exact RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        (bounded atom member) (rationalSeparation_nonneg _ _)
    _ = ceiling * content.integral (fun item =>
          rationalSeparation (left item) 0) := by
      calc
        content.integral (fun item =>
            rationalSeparation (left item) 0 * ceiling) =
            content.integral (fun item =>
              ceiling * rationalSeparation (left item) 0) :=
          content.integral_congr _ _ (fun item => by ring1)
        _ = ceiling * content.integral (fun item =>
              rationalSeparation (left item) 0) :=
          content.integral_scale _ _

end FiniteContent

namespace Distribution

def poweredL2 {α : Type} (distribution : Distribution α)
    (value : α → Coordinate) : Coordinate :=
  distribution.toFiniteContent.poweredL2 value

theorem poweredL2_nonnegative {α : Type}
    (distribution : Distribution α) (value : α → Coordinate) :
    0 ≤ distribution.poweredL2 value :=
  distribution.toFiniteContent.poweredL2_nonnegative value

@[simp] theorem poweredL2_zero {α : Type}
    (distribution : Distribution α) :
    distribution.poweredL2 (fun _ => 0) = 0 :=
  distribution.toFiniteContent.poweredL2_zero

theorem poweredL2_scale {α : Type} (distribution : Distribution α)
    (factor : Coordinate) (value : α → Coordinate) :
    distribution.poweredL2 (fun item => factor * value item) =
      factor ^ 2 * distribution.poweredL2 value :=
  distribution.toFiniteContent.poweredL2_scale factor value

def poweredL1 {α : Type} (distribution : Distribution α)
    (value : α → Coordinate) : Coordinate :=
  distribution.toFiniteContent.poweredL1 value

theorem poweredL1_nonnegative {α : Type}
    (distribution : Distribution α) (value : α → Coordinate) :
    0 ≤ distribution.poweredL1 value :=
  distribution.toFiniteContent.poweredL1_nonnegative value

theorem poweredL1_zero {α : Type} (distribution : Distribution α) :
    distribution.poweredL1 (fun _ => 0) = 0 :=
  distribution.toFiniteContent.poweredL1_zero

theorem poweredL1_constant {α : Type} (distribution : Distribution α)
    (constant : Coordinate) :
    distribution.poweredL1 (fun _ => constant) =
      rationalSeparation constant 0 := by
  change distribution.toFiniteContent.poweredL1 (fun _ => constant) = _
  rw [distribution.toFiniteContent.poweredL1_constant,
    distribution.toFiniteContent_total, one_mul]

theorem poweredL1_scale {α : Type} (distribution : Distribution α)
    (factor : Coordinate) (value : α → Coordinate) :
    distribution.poweredL1 (fun item => factor * value item) =
      rationalSeparation factor 0 * distribution.poweredL1 value :=
  distribution.toFiniteContent.poweredL1_scale factor value

theorem poweredL1_neg {α : Type} (distribution : Distribution α)
    (value : α → Coordinate) :
    distribution.poweredL1 (fun item => -value item) =
      distribution.poweredL1 value :=
  distribution.toFiniteContent.poweredL1_neg value

theorem poweredL1_add_le {α : Type} (distribution : Distribution α)
    (left right : α → Coordinate) :
    distribution.poweredL1 (fun item => left item + right item) ≤
      distribution.poweredL1 left + distribution.poweredL1 right :=
  distribution.toFiniteContent.poweredL1_add_le left right

theorem poweredL1_sub_le {α : Type} (distribution : Distribution α)
    (left right : α → Coordinate) :
    distribution.poweredL1 (fun item => left item - right item) ≤
      distribution.poweredL1 left + distribution.poweredL1 right :=
  distribution.toFiniteContent.poweredL1_sub_le left right

/-- Distributional powered L1 of a difference is exactly L1 distance. -/
theorem poweredL1_sub_eq_l1Distance {α : Type}
    (distribution : Distribution α) (left right : α → Coordinate) :
    distribution.poweredL1 (fun item => left item - right item) =
      distribution.l1Distance left right :=
  distribution.toFiniteContent.poweredL1_sub_eq_l1Distance left right

/-- Reverse triangle stability of normalized finite powered-L1
magnitudes. -/
theorem poweredL1_separation_le_l1Distance {α : Type}
    (distribution : Distribution α) (left right : α → Coordinate) :
    rationalSeparation (distribution.poweredL1 left)
        (distribution.poweredL1 right) ≤
      distribution.l1Distance left right :=
  distribution.toFiniteContent.poweredL1_separation_le_l1Distance left right

theorem productExpectation_sq_le_poweredL2_mul {α : Type}
    (distribution : Distribution α) (left right : α → Coordinate) :
    distribution.expectation (fun item => left item * right item) ^ 2 ≤
      distribution.poweredL2 left * distribution.poweredL2 right :=
  distribution.toFiniteContent.productIntegral_sq_le_poweredL2_mul left right

def poweredL2Distance {α : Type} (distribution : Distribution α)
    (left right : α → Coordinate) : Coordinate :=
  distribution.toFiniteContent.poweredL2Distance left right

theorem poweredL2Distance_nonnegative {α : Type}
    (distribution : Distribution α) (left right : α → Coordinate) :
    0 ≤ distribution.poweredL2Distance left right :=
  distribution.toFiniteContent.poweredL2Distance_nonnegative left right

@[simp] theorem poweredL2Distance_refl {α : Type}
    (distribution : Distribution α) (value : α → Coordinate) :
    distribution.poweredL2Distance value value = 0 :=
  distribution.toFiniteContent.poweredL2Distance_refl value

theorem poweredL2Distance_symm {α : Type}
    (distribution : Distribution α) (left right : α → Coordinate) :
    distribution.poweredL2Distance left right =
      distribution.poweredL2Distance right left :=
  distribution.toFiniteContent.poweredL2Distance_symm left right

theorem poweredL2Distance_scale {α : Type}
    (distribution : Distribution α) (factor : Coordinate)
    (left right : α → Coordinate) :
    distribution.poweredL2Distance
        (fun item => factor * left item)
        (fun item => factor * right item) =
      factor ^ 2 * distribution.poweredL2Distance left right :=
  distribution.toFiniteContent.poweredL2Distance_scale factor left right

theorem poweredL2Distance_le_radius_add_sq {α : Type}
    (distribution : Distribution α) (left middle right : α → Coordinate)
    (leftRadius rightRadius : Coordinate)
    (leftRadiusNonnegative : 0 ≤ leftRadius)
    (rightRadiusNonnegative : 0 ≤ rightRadius)
    (leftBound : distribution.poweredL2Distance left middle ≤
      leftRadius ^ 2)
    (rightBound : distribution.poweredL2Distance middle right ≤
      rightRadius ^ 2) :
    distribution.poweredL2Distance left right ≤
      (leftRadius + rightRadius) ^ 2 :=
  distribution.toFiniteContent.poweredL2Distance_le_radius_add_sq
    left middle right leftRadius rightRadius leftRadiusNonnegative
    rightRadiusNonnegative leftBound rightBound

end Distribution

end FiniteMeasure
