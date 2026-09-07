import mathlib.Data.ConstructiveList
import mathlib.Tactic.QuotientFreeRing
import RFAP.Cauchy.Product

/-!
# Executable constructive Cauchy-product cells

Three independently certified finite Cauchy events are coordinated by an
explicit search through the `3^4` possible factor-center sign records.  The
search carrier is a displayed finite list; there is no `Fintype`, root set,
or choice of an intermediate parameter.
-/

namespace RFAP.CauchyProductCells

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Polynomial := RFAP.ComputablePolynomial.DensePolynomial Coordinate
abbrev Interval := RFAP.PathClearance.Interval

open RFAP.ComputablePolynomial.DensePolynomial
open RFAP.CauchyProductSigns
open RFAP.CauchyCells
open RFAP.CauchyProduct

namespace FiniteTurn

/-- Finite quadrant transition forced by a small nonzero complex turn. -/
def SmallTurnCompatible
    (Aₗ Bₗ Aᵣ Bᵣ turn : FiniteSign) : Prop :=
  Aₗ ≠ .zero ∧ Bₗ ≠ .zero ∧ Aᵣ ≠ .zero ∧ Bᵣ ≠ .zero ∧
    if Aₗ = Aᵣ then
      if Bₗ = Bᵣ then True
      else turn = FiniteSign.neg (FiniteSign.mul Aₗ Bₗ)
    else Bₗ = Bᵣ ∧ turn = FiniteSign.mul Aₗ Bₗ

instance (Aₗ Bₗ Aᵣ Bᵣ turn : FiniteSign) :
    Decidable (SmallTurnCompatible Aₗ Bₗ Aᵣ Bᵣ turn) := by
  unfold SmallTurnCompatible
  infer_instance

inductive SmallTurnShape where
  | same
  | realChange
  | imagChange
deriving DecidableEq, Repr

def applySmallTurnShape
    (shape : SmallTurnShape) (real imag : FiniteSign) :
    FiniteSign × FiniteSign :=
  match shape with
  | .same => (real, imag)
  | .realChange => (FiniteSign.neg real, imag)
  | .imagChange => (real, FiniteSign.neg imag)

def smallTurnShape
    (realLeft imagLeft realRight imagRight : FiniteSign) : SmallTurnShape :=
  if realLeft = realRight then
    if imagLeft = imagRight then .same else .imagChange
  else .realChange

theorem apply_smallTurnShape_eq_of_compatible
    (Aₗ Bₗ Aᵣ Bᵣ turn : FiniteSign)
    (compatible : SmallTurnCompatible Aₗ Bₗ Aᵣ Bᵣ turn) :
    applySmallTurnShape (smallTurnShape Aₗ Bₗ Aᵣ Bᵣ) Aₗ Bₗ =
      (Aᵣ, Bᵣ) := by
  cases Aₗ <;> cases Bₗ <;> cases Aᵣ <;> cases Bᵣ <;> cases turn <;>
    simp_all [SmallTurnCompatible, smallTurnShape, applySmallTurnShape,
      FiniteSign.neg, FiniteSign.mul]

theorem ofCoordinate_eq_of_mul_pos {x y : Coordinate}
    (positive : 0 < x * y) :
    FiniteSign.ofCoordinate x = FiniteSign.ofCoordinate y := by
  apply FiniteSign.value_injective
  rw [FiniteSign.value_ofCoordinate, FiniteSign.value_ofCoordinate]
  exact RFAP.Sturm.sign_eq_of_mul_pos positive

theorem ofCoordinate_ne_of_mul_neg {x y : Coordinate}
    (negative : x * y < 0) :
    FiniteSign.ofCoordinate x ≠ FiniteSign.ofCoordinate y := by
  intro equal
  have values := congrArg FiniteSign.value equal
  rw [FiniteSign.value_ofCoordinate, FiniteSign.value_ofCoordinate] at values
  have jumpZero : RFAP.Sturm.signJump x y = 0 := by
    simp only [RFAP.Sturm.signJump, values, sub_self,
      Int.natAbs_zero]
  have jumpTwo := RFAP.Sturm.signJump_eq_two_of_mul_neg negative
  exact ((by decide : (0 : Nat) ≠ 2) (jumpZero.symm.trans jumpTwo)).elim

private theorem sq_pos_of_ne_zero {x : Coordinate} (nonzero : x ≠ 0) :
    0 < x ^ 2 := by
  have squareNonzero : x ^ 2 ≠ 0 := by
    intro zero
    exact nonzero ((RFAP.ConstructiveFraction.sq_eq_zero_direct x).mp zero)
  exact lt_of_le_of_ne (RFAP.ConstructiveFraction.sq_nonneg_direct x)
    (Ne.symm squareNonzero)

/-- A positive endpoint dot product fixes the finite quadrant transition;
the exact cross-product sign records which coordinate changes. -/
theorem smallTurnCompatible_of_dot_pos
    {Aₗ Bₗ Aᵣ Bᵣ : Coordinate}
    (AₗNonzero : Aₗ ≠ 0) (BₗNonzero : Bₗ ≠ 0)
    (AᵣNonzero : Aᵣ ≠ 0) (BᵣNonzero : Bᵣ ≠ 0)
    (dotPositive : 0 < Aₗ * Aᵣ + Bₗ * Bᵣ) :
    SmallTurnCompatible
      (FiniteSign.ofCoordinate Aₗ) (FiniteSign.ofCoordinate Bₗ)
      (FiniteSign.ofCoordinate Aᵣ) (FiniteSign.ofCoordinate Bᵣ)
      (FiniteSign.ofCoordinate (Aₗ * Bᵣ - Bₗ * Aᵣ)) := by
  let cross := Aₗ * Bᵣ - Bₗ * Aᵣ
  have AProductNonzero : Aₗ * Aᵣ ≠ 0 :=
    RFAP.ConstructiveFraction.mul_ne_zero_direct AₗNonzero AᵣNonzero
  have BProductNonzero : Bₗ * Bᵣ ≠ 0 :=
    RFAP.ConstructiveFraction.mul_ne_zero_direct BₗNonzero BᵣNonzero
  have AₗSign : FiniteSign.ofCoordinate Aₗ ≠ .zero := by
    simpa only [FiniteSign.ofCoordinate_ne_zero_iff] using AₗNonzero
  have BₗSign : FiniteSign.ofCoordinate Bₗ ≠ .zero := by
    simpa only [FiniteSign.ofCoordinate_ne_zero_iff] using BₗNonzero
  have AᵣSign : FiniteSign.ofCoordinate Aᵣ ≠ .zero := by
    simpa only [FiniteSign.ofCoordinate_ne_zero_iff] using AᵣNonzero
  have BᵣSign : FiniteSign.ofCoordinate Bᵣ ≠ .zero := by
    simpa only [FiniteSign.ofCoordinate_ne_zero_iff] using BᵣNonzero
  refine ⟨AₗSign, BₗSign, AᵣSign, BᵣSign, ?_⟩
  rcases lt_trichotomy (Aₗ * Aᵣ) 0 with
      AProductNegative | AProductZero | AProductPositive
  · rcases lt_trichotomy (Bₗ * Bᵣ) 0 with
        BProductNegative | BProductZero | BProductPositive
    · exact ((not_lt_of_ge
        (add_nonpos AProductNegative.le BProductNegative.le))
          dotPositive).elim
    · exact (BProductNonzero BProductZero).elim
    · have ASignsDiffer := ofCoordinate_ne_of_mul_neg AProductNegative
      have BSignsEqual := ofCoordinate_eq_of_mul_pos BProductPositive
      have firstPositive :
          0 < Aₗ ^ 2 * (Bₗ * Bᵣ) :=
        RFAP.ConstructiveFraction.mul_pos_direct
          (sq_pos_of_ne_zero AₗNonzero) BProductPositive
      have secondNegative :
          Bₗ ^ 2 * (Aₗ * Aᵣ) < 0 :=
        RFAP.ConstructiveFraction.mul_neg_of_pos_of_neg_direct
          (sq_pos_of_ne_zero BₗNonzero) AProductNegative
      have crossProductPositive : 0 < cross * (Aₗ * Bₗ) := by
        calc
          0 < Aₗ ^ 2 * (Bₗ * Bᵣ) -
              Bₗ ^ 2 * (Aₗ * Aᵣ) :=
            RFAP.ConstructiveFraction.sub_pos_direct
              (secondNegative.trans firstPositive)
          _ = cross * (Aₗ * Bₗ) := by
            dsimp only [cross]
            ring1
      have turn : FiniteSign.ofCoordinate cross =
          FiniteSign.mul (FiniteSign.ofCoordinate Aₗ)
            (FiniteSign.ofCoordinate Bₗ) := by
        simpa only [FiniteSign.ofCoordinate_mul] using
          ofCoordinate_eq_of_mul_pos crossProductPositive
      rw [if_neg ASignsDiffer]
      exact ⟨BSignsEqual, by simpa only [cross] using turn⟩
  · exact (AProductNonzero AProductZero).elim
  · rcases lt_trichotomy (Bₗ * Bᵣ) 0 with
        BProductNegative | BProductZero | BProductPositive
    · have ASignsEqual := ofCoordinate_eq_of_mul_pos AProductPositive
      have BSignsDiffer := ofCoordinate_ne_of_mul_neg BProductNegative
      have firstNegative :
          Aₗ ^ 2 * (Bₗ * Bᵣ) < 0 :=
        RFAP.ConstructiveFraction.mul_neg_of_pos_of_neg_direct
          (sq_pos_of_ne_zero AₗNonzero) BProductNegative
      have secondPositive :
          0 < Bₗ ^ 2 * (Aₗ * Aᵣ) :=
        RFAP.ConstructiveFraction.mul_pos_direct
          (sq_pos_of_ne_zero BₗNonzero) AProductPositive
      have crossProductPositive : 0 < cross * (-(Aₗ * Bₗ)) := by
        calc
          0 < Bₗ ^ 2 * (Aₗ * Aᵣ) -
              Aₗ ^ 2 * (Bₗ * Bᵣ) :=
            RFAP.ConstructiveFraction.sub_pos_direct
              (firstNegative.trans secondPositive)
          _ = cross * (-(Aₗ * Bₗ)) := by
            dsimp only [cross]
            ring1
      have turn : FiniteSign.ofCoordinate cross =
          FiniteSign.neg (FiniteSign.mul
            (FiniteSign.ofCoordinate Aₗ)
            (FiniteSign.ofCoordinate Bₗ)) := by
        simpa only [FiniteSign.ofCoordinate_neg,
          FiniteSign.ofCoordinate_mul] using
          ofCoordinate_eq_of_mul_pos crossProductPositive
      rw [if_pos ASignsEqual, if_neg BSignsDiffer]
      simpa only [cross] using turn
    · exact (BProductNonzero BProductZero).elim
    · have ASignsEqual := ofCoordinate_eq_of_mul_pos AProductPositive
      have BSignsEqual := ofCoordinate_eq_of_mul_pos BProductPositive
      rw [if_pos ASignsEqual, if_pos BSignsEqual]
      trivial

end FiniteTurn

/-- Square-root-free quantitative small turn for two nonzero complex endpoint
vectors. -/
def NarrowComplexTurn
    (Aₗ Bₗ Aᵣ Bᵣ : Coordinate) : Prop :=
  3 * |Aₗ * Bᵣ - Bₗ * Aᵣ| < Aₗ * Aᵣ + Bₗ * Bᵣ

theorem complexDot_pos_of_narrowComplexTurn
    {Aₗ Bₗ Aᵣ Bᵣ : Coordinate}
    (narrow : NarrowComplexTurn Aₗ Bₗ Aᵣ Bᵣ) :
    0 < Aₗ * Aᵣ + Bₗ * Bᵣ := by
  have nonnegative : 0 ≤ 3 * |Aₗ * Bᵣ - Bₗ * Aᵣ| :=
    RFAP.ConstructiveFraction.mul_nonneg_direct (by decide) (RFAP.ConstructiveFraction.abs_nonneg_direct _)
  exact nonnegative.trans_lt narrow

private theorem abs_mul_direct (x y : Coordinate) :
    |x * y| = |x| * |y| := by
  rcases lt_trichotomy x 0 with xNegative | rfl | xPositive <;>
    rcases lt_trichotomy y 0 with yNegative | rfl | yPositive
  · have productPositive :=
      RFAP.ConstructiveFraction.mul_pos_of_neg_of_neg_direct
        xNegative yNegative
    rw [abs_of_pos productPositive, abs_of_neg xNegative,
      abs_of_neg yNegative]
    ring1
  · simp
  · have productNegative :=
      RFAP.ConstructiveFraction.mul_neg_of_neg_of_pos_direct
        xNegative yPositive
    rw [abs_of_neg productNegative, abs_of_neg xNegative,
      abs_of_pos yPositive]
    ring1
  · simp
  · simp
  · simp
  · have productNegative :=
      RFAP.ConstructiveFraction.mul_neg_of_pos_of_neg_direct
        xPositive yNegative
    rw [abs_of_neg productNegative, abs_of_pos xPositive,
      abs_of_neg yNegative]
    ring1
  · simp
  · have productPositive := RFAP.ConstructiveFraction.mul_pos_direct
      xPositive yPositive
    rw [abs_of_pos productPositive, abs_of_pos xPositive,
      abs_of_pos yPositive]

private theorem abs_ne_zero_direct {x : Coordinate} (nonzero : x ≠ 0) :
    |x| ≠ 0 := by
  rcases lt_trichotomy x 0 with negative | rfl | positive
  · rw [abs_of_neg negative]
    intro negatedZero
    apply nonzero
    calc
      x = -(-x) := by ring1
      _ = -0 := by rw [negatedZero]
      _ = 0 := by ring1
  · exact (nonzero rfl).elim
  · simpa only [abs_of_pos positive] using nonzero

/-- Two slope-`1/3` factor turns make the product endpoint vectors have
positive dot product. -/
theorem productComplexDot_pos_of_narrowTurns
    {Aₗ Bₗ Cₗ Dₗ Aᵣ Bᵣ Cᵣ Dᵣ : Coordinate}
    (left : NarrowComplexTurn Aₗ Bₗ Aᵣ Bᵣ)
    (right : NarrowComplexTurn Cₗ Dₗ Cᵣ Dᵣ) :
    0 <
      (Aₗ * Cₗ - Bₗ * Dₗ) * (Aᵣ * Cᵣ - Bᵣ * Dᵣ) +
      (Aₗ * Dₗ + Bₗ * Cₗ) * (Aᵣ * Dᵣ + Bᵣ * Cᵣ) := by
  let leftDot := Aₗ * Aᵣ + Bₗ * Bᵣ
  let leftCross := Aₗ * Bᵣ - Bₗ * Aᵣ
  let rightDot := Cₗ * Cᵣ + Dₗ * Dᵣ
  let rightCross := Cₗ * Dᵣ - Dₗ * Cᵣ
  have leftDotPositive : 0 < leftDot :=
    complexDot_pos_of_narrowComplexTurn left
  have rightDotPositive : 0 < rightDot :=
    complexDot_pos_of_narrowComplexTurn right
  have leftBound : 3 * |leftCross| < leftDot := by
    simpa only [leftCross, leftDot, NarrowComplexTurn] using left
  have rightBound : 3 * |rightCross| < rightDot := by
    simpa only [rightCross, rightDot, NarrowComplexTurn] using right
  have crossProductLess : leftCross * rightCross < leftDot * rightDot := by
    by_cases leftCrossZero : leftCross = 0
    ·
      rw [leftCrossZero, zero_mul]
      exact RFAP.ConstructiveFraction.mul_pos_direct
        leftDotPositive rightDotPositive
    · by_cases rightCrossZero : rightCross = 0
      ·
        rw [rightCrossZero, mul_zero]
        exact RFAP.ConstructiveFraction.mul_pos_direct
          leftDotPositive rightDotPositive
      · have leftAbsPositive : 0 < |leftCross| :=
          lt_of_le_of_ne (RFAP.ConstructiveFraction.abs_nonneg_direct _)
            (Ne.symm (abs_ne_zero_direct leftCrossZero))
        have rightAbsPositive : 0 < |rightCross| :=
          lt_of_le_of_ne (RFAP.ConstructiveFraction.abs_nonneg_direct _)
            (Ne.symm (abs_ne_zero_direct rightCrossZero))
        have absProductPositive : 0 < |leftCross| * |rightCross| :=
          RFAP.ConstructiveFraction.mul_pos_direct
            leftAbsPositive rightAbsPositive
        have threeRightPositive : 0 < 3 * |rightCross| :=
          RFAP.ConstructiveFraction.mul_pos_direct (by decide)
            rightAbsPositive
        calc
          leftCross * rightCross ≤ |leftCross * rightCross| := le_abs_self _
          _ = |leftCross| * |rightCross| :=
            abs_mul_direct leftCross rightCross
          _ = 1 * (|leftCross| * |rightCross|) := by ring1
          _ < 9 * (|leftCross| * |rightCross|) :=
            RFAP.ConstructiveFraction.mul_lt_mul_of_pos_right_direct
              (by decide) absProductPositive
          _ = (3 * |leftCross|) * (3 * |rightCross|) := by ring1
          _ < leftDot * (3 * |rightCross|) :=
            RFAP.ConstructiveFraction.mul_lt_mul_of_pos_right_direct
              leftBound threeRightPositive
          _ < leftDot * rightDot :=
            RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
              leftDotPositive rightBound
  have identity :
      (Aₗ * Cₗ - Bₗ * Dₗ) * (Aᵣ * Cᵣ - Bᵣ * Dᵣ) +
          (Aₗ * Dₗ + Bₗ * Cₗ) * (Aᵣ * Dᵣ + Bᵣ * Cᵣ) =
        leftDot * rightDot - leftCross * rightCross := by
    dsimp only [leftDot, leftCross, rightDot, rightCross]
    ring1
  rw [identity]
  exact RFAP.ConstructiveFraction.sub_pos_direct crossProductLess

/-- The oriented product turn is the sign-compatible sum of the two factor
turns; the positive dot factors do not alter either sign. -/
theorem productTurn_sumCompatible_of_narrowTurns
    {Aₗ Bₗ Cₗ Dₗ Aᵣ Bᵣ Cᵣ Dᵣ : Coordinate}
    (left : NarrowComplexTurn Aₗ Bₗ Aᵣ Bᵣ)
    (right : NarrowComplexTurn Cₗ Dₗ Cᵣ Dᵣ) :
    FiniteSign.SumCompatible
      (FiniteSign.ofCoordinate (Aₗ * Bᵣ - Bₗ * Aᵣ))
      (FiniteSign.ofCoordinate (Cₗ * Dᵣ - Dₗ * Cᵣ))
      (FiniteSign.ofCoordinate
        ((Aₗ * Cₗ - Bₗ * Dₗ) * (Aᵣ * Dᵣ + Bᵣ * Cᵣ) -
          (Aₗ * Dₗ + Bₗ * Cₗ) * (Aᵣ * Cᵣ - Bᵣ * Dᵣ))) := by
  let leftDot := Aₗ * Aᵣ + Bₗ * Bᵣ
  let leftCross := Aₗ * Bᵣ - Bₗ * Aᵣ
  let rightDot := Cₗ * Cᵣ + Dₗ * Dᵣ
  let rightCross := Cₗ * Dᵣ - Dₗ * Cᵣ
  have leftDotPositive : 0 < leftDot :=
    complexDot_pos_of_narrowComplexTurn left
  have rightDotPositive : 0 < rightDot :=
    complexDot_pos_of_narrowComplexTurn right
  have sum := FiniteSign.sumCompatible_ofCoordinate
    (leftCross * rightDot) (leftDot * rightCross)
  have leftScale : FiniteSign.ofCoordinate (leftCross * rightDot) =
      FiniteSign.ofCoordinate leftCross := by
    rw [FiniteSign.ofCoordinate_mul,
      FiniteSign.ofCoordinate_of_pos rightDotPositive]
    cases FiniteSign.ofCoordinate leftCross <;> rfl
  have rightScale : FiniteSign.ofCoordinate (leftDot * rightCross) =
      FiniteSign.ofCoordinate rightCross := by
    rw [FiniteSign.ofCoordinate_mul,
      FiniteSign.ofCoordinate_of_pos leftDotPositive]
    cases FiniteSign.ofCoordinate rightCross <;> rfl
  have crossIdentity : leftCross * rightDot + leftDot * rightCross =
      (Aₗ * Cₗ - Bₗ * Dₗ) * (Aᵣ * Dᵣ + Bᵣ * Cᵣ) -
        (Aₗ * Dₗ + Bₗ * Cₗ) * (Aᵣ * Cᵣ - Bᵣ * Dᵣ) := by
    dsimp only [leftDot, leftCross, rightDot, rightCross]
    ring1
  rw [leftScale, rightScale, crossIdentity] at sum
  exact sum

structure ProductCenterSigns where
  factorLeftReal : FiniteSign
  factorLeftImag : FiniteSign
  factorRightReal : FiniteSign
  factorRightImag : FiniteSign
deriving DecidableEq, Repr

namespace ProductCenterSigns

def productReal (centers : ProductCenterSigns) : FiniteSign :=
  FiniteSign.productRealChoice
    centers.factorLeftReal centers.factorLeftImag
    centers.factorRightReal centers.factorRightImag

def productImag (centers : ProductCenterSigns) : FiniteSign :=
  FiniteSign.productImagChoice
    centers.factorLeftReal centers.factorLeftImag
    centers.factorRightReal centers.factorRightImag

/-- Direct center selected from the three finite endpoint-transition shapes. -/
private def coordinatedCenter
    (leftShape rightShape productShape : FiniteTurn.SmallTurnShape)
    (A B C D : FiniteSign) : ProductCenterSigns :=
  match leftShape, rightShape, productShape with
  | .imagChange, .imagChange, _ => ⟨A, .zero, C, .zero⟩
  | .imagChange, .realChange, _ => ⟨A, .zero, .zero, D⟩
  | .imagChange, .same, .realChange => ⟨A, .zero, .zero, D⟩
  | .imagChange, .same, _ => ⟨A, .zero, C, .zero⟩
  | .realChange, .imagChange, _ => ⟨.zero, B, C, .zero⟩
  | .realChange, .realChange, _ => ⟨.zero, B, .zero, D⟩
  | .realChange, .same, .realChange => ⟨.zero, B, C, .zero⟩
  | .realChange, .same, _ => ⟨.zero, B, .zero, D⟩
  | .same, .imagChange, .realChange => ⟨.zero, B, C, .zero⟩
  | .same, .imagChange, _ => ⟨A, .zero, C, .zero⟩
  | .same, .realChange, .realChange => ⟨A, .zero, .zero, D⟩
  | .same, .realChange, _ => ⟨.zero, B, .zero, D⟩
  | .same, .same, .imagChange => ⟨A, .zero, C, .zero⟩
  | .same, .same, .realChange => ⟨.zero, B, C, .zero⟩
  | .same, .same, .same => ⟨A, B, C, D⟩

def AdmissibleSigns
    (centers : ProductCenterSigns)
    (Aₗ Bₗ Cₗ Dₗ Eₗ Hₗ Aᵣ Bᵣ Cᵣ Dᵣ Eᵣ Hᵣ : FiniteSign) : Prop :=
  FiniteSign.EventCenterAdmissible
      centers.factorLeftReal centers.factorLeftImag Aₗ Bₗ Aᵣ Bᵣ ∧
    FiniteSign.EventCenterAdmissible
      centers.factorRightReal centers.factorRightImag Cₗ Dₗ Cᵣ Dᵣ ∧
    FiniteSign.EventCenterAdmissible
      centers.productReal centers.productImag Eₗ Hₗ Eᵣ Hᵣ

instance
    (centers : ProductCenterSigns)
    (Aₗ Bₗ Cₗ Dₗ Eₗ Hₗ Aᵣ Bᵣ Cᵣ Dᵣ Eᵣ Hᵣ : FiniteSign) :
    Decidable (centers.AdmissibleSigns
      Aₗ Bₗ Cₗ Dₗ Eₗ Hₗ Aᵣ Bᵣ Cᵣ Dᵣ Eᵣ Hᵣ) := by
  unfold AdmissibleSigns
  infer_instance

private def CoordinatedCenterRow
    (leftShape rightShape productShape : FiniteTurn.SmallTurnShape)
    (A B C D E H leftTurn rightTurn productTurn : FiniteSign) : Prop :=
  FiniteTurn.SmallTurnCompatible A B
      (FiniteTurn.applySmallTurnShape leftShape A B).1
      (FiniteTurn.applySmallTurnShape leftShape A B).2 leftTurn →
    FiniteTurn.SmallTurnCompatible C D
      (FiniteTurn.applySmallTurnShape rightShape C D).1
      (FiniteTurn.applySmallTurnShape rightShape C D).2 rightTurn →
    FiniteTurn.SmallTurnCompatible E H
      (FiniteTurn.applySmallTurnShape productShape E H).1
      (FiniteTurn.applySmallTurnShape productShape E H).2 productTurn →
    FiniteSign.SumCompatible leftTurn rightTurn productTurn →
    FiniteSign.ComplexProductCompatible A B C D E H →
    FiniteSign.ComplexProductCompatible
      (FiniteTurn.applySmallTurnShape leftShape A B).1
      (FiniteTurn.applySmallTurnShape leftShape A B).2
      (FiniteTurn.applySmallTurnShape rightShape C D).1
      (FiniteTurn.applySmallTurnShape rightShape C D).2
      (FiniteTurn.applySmallTurnShape productShape E H).1
      (FiniteTurn.applySmallTurnShape productShape E H).2 →
    (coordinatedCenter leftShape rightShape productShape A B C D).AdmissibleSigns
      A B C D E H
      (FiniteTurn.applySmallTurnShape leftShape A B).1
      (FiniteTurn.applySmallTurnShape leftShape A B).2
      (FiniteTurn.applySmallTurnShape rightShape C D).1
      (FiniteTurn.applySmallTurnShape rightShape C D).2
      (FiniteTurn.applySmallTurnShape productShape E H).1
      (FiniteTurn.applySmallTurnShape productShape E H).2

private instance
    (leftShape rightShape productShape : FiniteTurn.SmallTurnShape)
    (A B C D E H leftTurn rightTurn productTurn : FiniteSign) :
    Decidable (CoordinatedCenterRow leftShape rightShape productShape
      A B C D E H leftTurn rightTurn productTurn) := by
  unfold CoordinatedCenterRow
  infer_instance

private def finiteSignOfBool : Bool → FiniteSign
  | false => .negative
  | true => .positive

private def boolOfFiniteSign : FiniteSign → Bool
  | .negative => false
  | .zero => false
  | .positive => true

private theorem finiteSignOfBool_boolOfFiniteSign
    (sign : FiniteSign) (nonzero : sign ≠ .zero) :
    finiteSignOfBool (boolOfFiniteSign sign) = sign := by
  cases sign <;> simp_all [finiteSignOfBool, boolOfFiniteSign]

private theorem coordinated_strict_same_same :
    ∀ productShape (A B C D E H : Bool) leftTurn rightTurn productTurn,
      CoordinatedCenterRow .same .same productShape
        (finiteSignOfBool A) (finiteSignOfBool B)
        (finiteSignOfBool C) (finiteSignOfBool D)
        (finiteSignOfBool E) (finiteSignOfBool H)
        leftTurn rightTurn productTurn := by
  intro productShape A B C D E H leftTurn rightTurn productTurn
  cases productShape <;> cases A <;> cases B <;> cases C <;> cases D <;>
    cases E <;> cases H <;> cases leftTurn <;> cases rightTurn <;>
    cases productTurn <;> decide

private theorem coordinated_strict_same_realChange :
    ∀ productShape (A B C D E H : Bool) leftTurn rightTurn productTurn,
      CoordinatedCenterRow .same .realChange productShape
        (finiteSignOfBool A) (finiteSignOfBool B)
        (finiteSignOfBool C) (finiteSignOfBool D)
        (finiteSignOfBool E) (finiteSignOfBool H)
        leftTurn rightTurn productTurn := by
  intro productShape A B C D E H leftTurn rightTurn productTurn
  cases productShape <;> cases A <;> cases B <;> cases C <;> cases D <;>
    cases E <;> cases H <;> cases leftTurn <;> cases rightTurn <;>
    cases productTurn <;> decide

private theorem coordinated_strict_same_imagChange :
    ∀ productShape (A B C D E H : Bool) leftTurn rightTurn productTurn,
      CoordinatedCenterRow .same .imagChange productShape
        (finiteSignOfBool A) (finiteSignOfBool B)
        (finiteSignOfBool C) (finiteSignOfBool D)
        (finiteSignOfBool E) (finiteSignOfBool H)
        leftTurn rightTurn productTurn := by
  intro productShape A B C D E H leftTurn rightTurn productTurn
  cases productShape <;> cases A <;> cases B <;> cases C <;> cases D <;>
    cases E <;> cases H <;> cases leftTurn <;> cases rightTurn <;>
    cases productTurn <;> decide

private theorem coordinated_strict_realChange_same :
    ∀ productShape (A B C D E H : Bool) leftTurn rightTurn productTurn,
      CoordinatedCenterRow .realChange .same productShape
        (finiteSignOfBool A) (finiteSignOfBool B)
        (finiteSignOfBool C) (finiteSignOfBool D)
        (finiteSignOfBool E) (finiteSignOfBool H)
        leftTurn rightTurn productTurn := by
  intro productShape A B C D E H leftTurn rightTurn productTurn
  cases productShape <;> cases A <;> cases B <;> cases C <;> cases D <;>
    cases E <;> cases H <;> cases leftTurn <;> cases rightTurn <;>
    cases productTurn <;> decide

private theorem coordinated_strict_realChange_realChange :
    ∀ productShape (A B C D E H : Bool) leftTurn rightTurn productTurn,
      CoordinatedCenterRow .realChange .realChange productShape
        (finiteSignOfBool A) (finiteSignOfBool B)
        (finiteSignOfBool C) (finiteSignOfBool D)
        (finiteSignOfBool E) (finiteSignOfBool H)
        leftTurn rightTurn productTurn := by
  intro productShape A B C D E H leftTurn rightTurn productTurn
  cases productShape <;> cases A <;> cases B <;> cases C <;> cases D <;>
    cases E <;> cases H <;> cases leftTurn <;> cases rightTurn <;>
    cases productTurn <;> decide

private theorem coordinated_strict_realChange_imagChange :
    ∀ productShape (A B C D E H : Bool) leftTurn rightTurn productTurn,
      CoordinatedCenterRow .realChange .imagChange productShape
        (finiteSignOfBool A) (finiteSignOfBool B)
        (finiteSignOfBool C) (finiteSignOfBool D)
        (finiteSignOfBool E) (finiteSignOfBool H)
        leftTurn rightTurn productTurn := by
  intro productShape A B C D E H leftTurn rightTurn productTurn
  cases productShape <;> cases A <;> cases B <;> cases C <;> cases D <;>
    cases E <;> cases H <;> cases leftTurn <;> cases rightTurn <;>
    cases productTurn <;> decide

private theorem coordinated_strict_imagChange_same :
    ∀ productShape (A B C D E H : Bool) leftTurn rightTurn productTurn,
      CoordinatedCenterRow .imagChange .same productShape
        (finiteSignOfBool A) (finiteSignOfBool B)
        (finiteSignOfBool C) (finiteSignOfBool D)
        (finiteSignOfBool E) (finiteSignOfBool H)
        leftTurn rightTurn productTurn := by
  intro productShape A B C D E H leftTurn rightTurn productTurn
  cases productShape <;> cases A <;> cases B <;> cases C <;> cases D <;>
    cases E <;> cases H <;> cases leftTurn <;> cases rightTurn <;>
    cases productTurn <;> decide

private theorem coordinated_strict_imagChange_realChange :
    ∀ productShape (A B C D E H : Bool) leftTurn rightTurn productTurn,
      CoordinatedCenterRow .imagChange .realChange productShape
        (finiteSignOfBool A) (finiteSignOfBool B)
        (finiteSignOfBool C) (finiteSignOfBool D)
        (finiteSignOfBool E) (finiteSignOfBool H)
        leftTurn rightTurn productTurn := by
  intro productShape A B C D E H leftTurn rightTurn productTurn
  cases productShape <;> cases A <;> cases B <;> cases C <;> cases D <;>
    cases E <;> cases H <;> cases leftTurn <;> cases rightTurn <;>
    cases productTurn <;> decide

private theorem coordinated_strict_imagChange_imagChange :
    ∀ productShape (A B C D E H : Bool) leftTurn rightTurn productTurn,
      CoordinatedCenterRow .imagChange .imagChange productShape
        (finiteSignOfBool A) (finiteSignOfBool B)
        (finiteSignOfBool C) (finiteSignOfBool D)
        (finiteSignOfBool E) (finiteSignOfBool H)
        leftTurn rightTurn productTurn := by
  intro productShape A B C D E H leftTurn rightTurn productTurn
  cases productShape <;> cases A <;> cases B <;> cases C <;> cases D <;>
    cases E <;> cases H <;> cases leftTurn <;> cases rightTurn <;>
    cases productTurn <;> decide

private theorem coordinatedCenter_admissible_strict
    (leftShape rightShape productShape : FiniteTurn.SmallTurnShape)
    (A B C D E H : Bool)
    (leftTurn rightTurn productTurn : FiniteSign) :
    CoordinatedCenterRow leftShape rightShape productShape
      (finiteSignOfBool A) (finiteSignOfBool B)
      (finiteSignOfBool C) (finiteSignOfBool D)
      (finiteSignOfBool E) (finiteSignOfBool H)
      leftTurn rightTurn productTurn := by
  cases leftShape <;> cases rightShape
  · exact coordinated_strict_same_same productShape A B C D E H
      leftTurn rightTurn productTurn
  · exact coordinated_strict_same_realChange productShape A B C D E H
      leftTurn rightTurn productTurn
  · exact coordinated_strict_same_imagChange productShape A B C D E H
      leftTurn rightTurn productTurn
  · exact coordinated_strict_realChange_same productShape A B C D E H
      leftTurn rightTurn productTurn
  · exact coordinated_strict_realChange_realChange productShape A B C D E H
      leftTurn rightTurn productTurn
  · exact coordinated_strict_realChange_imagChange productShape A B C D E H
      leftTurn rightTurn productTurn
  · exact coordinated_strict_imagChange_same productShape A B C D E H
      leftTurn rightTurn productTurn
  · exact coordinated_strict_imagChange_realChange productShape A B C D E H
      leftTurn rightTurn productTurn
  · exact coordinated_strict_imagChange_imagChange productShape A B C D E H
      leftTurn rightTurn productTurn

private theorem coordinatedCenter_admissible
    (leftShape rightShape productShape : FiniteTurn.SmallTurnShape)
    (A B C D E H leftTurn rightTurn productTurn : FiniteSign) :
    CoordinatedCenterRow leftShape rightShape productShape
      A B C D E H leftTurn rightTurn productTurn := by
  unfold CoordinatedCenterRow
  intro left right product turn lower upper
  have strict := coordinatedCenter_admissible_strict
    leftShape rightShape productShape
    (boolOfFiniteSign A) (boolOfFiniteSign B)
    (boolOfFiniteSign C) (boolOfFiniteSign D)
    (boolOfFiniteSign E) (boolOfFiniteSign H)
    leftTurn rightTurn productTurn
  rw [finiteSignOfBool_boolOfFiniteSign A left.1,
    finiteSignOfBool_boolOfFiniteSign B left.2.1,
    finiteSignOfBool_boolOfFiniteSign C right.1,
    finiteSignOfBool_boolOfFiniteSign D right.2.1,
    finiteSignOfBool_boolOfFiniteSign E product.1,
    finiteSignOfBool_boolOfFiniteSign H product.2.1] at strict
  exact strict left right product turn lower upper

/-- Three compatible finite small turns admit an explicitly selected common
center for the two factors and their complex product. -/
theorem exists_admissibleSigns_of_smallTurns
    (Aₗ Bₗ Cₗ Dₗ Eₗ Hₗ Aᵣ Bᵣ Cᵣ Dᵣ Eᵣ Hᵣ
      leftTurn rightTurn productTurn : FiniteSign)
    (left : FiniteTurn.SmallTurnCompatible
      Aₗ Bₗ Aᵣ Bᵣ leftTurn)
    (right : FiniteTurn.SmallTurnCompatible
      Cₗ Dₗ Cᵣ Dᵣ rightTurn)
    (product : FiniteTurn.SmallTurnCompatible
      Eₗ Hₗ Eᵣ Hᵣ productTurn)
    (turn : FiniteSign.SumCompatible
      leftTurn rightTurn productTurn)
    (lower : FiniteSign.ComplexProductCompatible
      Aₗ Bₗ Cₗ Dₗ Eₗ Hₗ)
    (upper : FiniteSign.ComplexProductCompatible
      Aᵣ Bᵣ Cᵣ Dᵣ Eᵣ Hᵣ) :
    ∃ centers : ProductCenterSigns,
      centers.AdmissibleSigns
        Aₗ Bₗ Cₗ Dₗ Eₗ Hₗ Aᵣ Bᵣ Cᵣ Dᵣ Eᵣ Hᵣ := by
  let leftShape := FiniteTurn.smallTurnShape Aₗ Bₗ Aᵣ Bᵣ
  let rightShape := FiniteTurn.smallTurnShape Cₗ Dₗ Cᵣ Dᵣ
  let productShape := FiniteTurn.smallTurnShape Eₗ Hₗ Eᵣ Hᵣ
  have leftEndpoints :=
    FiniteTurn.apply_smallTurnShape_eq_of_compatible _ _ _ _ _ left
  have rightEndpoints :=
    FiniteTurn.apply_smallTurnShape_eq_of_compatible _ _ _ _ _ right
  have productEndpoints :=
    FiniteTurn.apply_smallTurnShape_eq_of_compatible _ _ _ _ _ product
  have leftAtShape : FiniteTurn.SmallTurnCompatible Aₗ Bₗ
      (FiniteTurn.applySmallTurnShape leftShape Aₗ Bₗ).1
      (FiniteTurn.applySmallTurnShape leftShape Aₗ Bₗ).2 leftTurn := by
    rw [leftEndpoints]
    exact left
  have rightAtShape : FiniteTurn.SmallTurnCompatible Cₗ Dₗ
      (FiniteTurn.applySmallTurnShape rightShape Cₗ Dₗ).1
      (FiniteTurn.applySmallTurnShape rightShape Cₗ Dₗ).2 rightTurn := by
    rw [rightEndpoints]
    exact right
  have productAtShape : FiniteTurn.SmallTurnCompatible Eₗ Hₗ
      (FiniteTurn.applySmallTurnShape productShape Eₗ Hₗ).1
      (FiniteTurn.applySmallTurnShape productShape Eₗ Hₗ).2 productTurn := by
    rw [productEndpoints]
    exact product
  refine ⟨coordinatedCenter leftShape rightShape productShape
    Aₗ Bₗ Cₗ Dₗ, ?_⟩
  have admissible := coordinatedCenter_admissible
    leftShape rightShape productShape
    Aₗ Bₗ Cₗ Dₗ Eₗ Hₗ leftTurn rightTurn productTurn
    leftAtShape rightAtShape productAtShape turn lower (by
      rw [leftEndpoints, rightEndpoints, productEndpoints]
      exact upper)
  rw [leftEndpoints, rightEndpoints, productEndpoints] at admissible
  exact admissible

def finiteSignCandidates : List FiniteSign :=
  [.negative, .zero, .positive]

theorem mem_finiteSignCandidates (sign : FiniteSign) :
    sign ∈ finiteSignCandidates := by
  cases sign <;> simp [finiteSignCandidates]

/-- The displayed `3^4` search space. -/
def candidates : List ProductCenterSigns :=
  finiteSignCandidates.flatMap fun factorLeftReal =>
  finiteSignCandidates.flatMap fun factorLeftImag =>
  finiteSignCandidates.flatMap fun factorRightReal =>
  finiteSignCandidates.map fun factorRightImag =>
    { factorLeftReal, factorLeftImag, factorRightReal, factorRightImag }

theorem mem_candidates (centers : ProductCenterSigns) :
    centers ∈ candidates := by
  rcases centers with
    ⟨factorLeftReal, factorLeftImag, factorRightReal, factorRightImag⟩
  unfold candidates
  apply QuotientFreeList.mem_flatMap.mpr
  refine ⟨factorLeftReal, mem_finiteSignCandidates factorLeftReal, ?_⟩
  apply QuotientFreeList.mem_flatMap.mpr
  refine ⟨factorLeftImag, mem_finiteSignCandidates factorLeftImag, ?_⟩
  apply QuotientFreeList.mem_flatMap.mpr
  refine ⟨factorRightReal, mem_finiteSignCandidates factorRightReal, ?_⟩
  apply QuotientFreeList.mem_map.mpr
  exact ⟨factorRightImag, mem_finiteSignCandidates factorRightImag, rfl⟩

def signCheck
    (Aₗ Bₗ Cₗ Dₗ Eₗ Hₗ Aᵣ Bᵣ Cᵣ Dᵣ Eᵣ Hᵣ : FiniteSign)
    (centers : ProductCenterSigns) : Bool :=
  decide (centers.AdmissibleSigns
    Aₗ Bₗ Cₗ Dₗ Eₗ Hₗ Aᵣ Bᵣ Cᵣ Dᵣ Eᵣ Hᵣ)

def signSearch?
    (Aₗ Bₗ Cₗ Dₗ Eₗ Hₗ Aᵣ Bᵣ Cᵣ Dᵣ Eᵣ Hᵣ : FiniteSign) :
    Option ProductCenterSigns :=
  candidates.find? fun centers =>
    signCheck Aₗ Bₗ Cₗ Dₗ Eₗ Hₗ Aᵣ Bᵣ Cᵣ Dᵣ Eᵣ Hᵣ centers

theorem signSearch?_some_admissible
    {Aₗ Bₗ Cₗ Dₗ Eₗ Hₗ Aᵣ Bᵣ Cᵣ Dᵣ Eᵣ Hᵣ : FiniteSign}
    {centers : ProductCenterSigns}
    (found : signSearch?
      Aₗ Bₗ Cₗ Dₗ Eₗ Hₗ Aᵣ Bᵣ Cᵣ Dᵣ Eᵣ Hᵣ = some centers) :
    centers.AdmissibleSigns
      Aₗ Bₗ Cₗ Dₗ Eₗ Hₗ Aᵣ Bᵣ Cᵣ Dᵣ Eᵣ Hᵣ := by
  have checked := List.find?_some found
  change decide (centers.AdmissibleSigns
    Aₗ Bₗ Cₗ Dₗ Eₗ Hₗ Aᵣ Bᵣ Cᵣ Dᵣ Eᵣ Hᵣ) = true at checked
  exact of_decide_eq_true checked

theorem signSearch?_isSome_of_admissible
    {Aₗ Bₗ Cₗ Dₗ Eₗ Hₗ Aᵣ Bᵣ Cᵣ Dᵣ Eᵣ Hᵣ : FiniteSign}
    (centers : ProductCenterSigns)
    (admissible : centers.AdmissibleSigns
      Aₗ Bₗ Cₗ Dₗ Eₗ Hₗ Aᵣ Bᵣ Cᵣ Dᵣ Eᵣ Hᵣ) :
    (signSearch?
      Aₗ Bₗ Cₗ Dₗ Eₗ Hₗ Aᵣ Bᵣ Cᵣ Dᵣ Eᵣ Hᵣ).isSome := by
  rw [signSearch?, QuotientFreeList.find?_isSome]
  refine ⟨centers, mem_candidates centers, ?_⟩
  simp [signCheck, admissible]

theorem signSearch?_isSome_of_smallTurns
    (Aₗ Bₗ Cₗ Dₗ Eₗ Hₗ Aᵣ Bᵣ Cᵣ Dᵣ Eᵣ Hᵣ
      leftTurn rightTurn productTurn : FiniteSign)
    (left : FiniteTurn.SmallTurnCompatible
      Aₗ Bₗ Aᵣ Bᵣ leftTurn)
    (right : FiniteTurn.SmallTurnCompatible
      Cₗ Dₗ Cᵣ Dᵣ rightTurn)
    (product : FiniteTurn.SmallTurnCompatible
      Eₗ Hₗ Eᵣ Hᵣ productTurn)
    (turn : FiniteSign.SumCompatible
      leftTurn rightTurn productTurn)
    (lower : FiniteSign.ComplexProductCompatible
      Aₗ Bₗ Cₗ Dₗ Eₗ Hₗ)
    (upper : FiniteSign.ComplexProductCompatible
      Aᵣ Bᵣ Cᵣ Dᵣ Eᵣ Hᵣ) :
    (signSearch?
      Aₗ Bₗ Cₗ Dₗ Eₗ Hₗ Aᵣ Bᵣ Cᵣ Dᵣ Eᵣ Hᵣ).isSome := by
  obtain ⟨centers, admissible⟩ := exists_admissibleSigns_of_smallTurns
    Aₗ Bₗ Cₗ Dₗ Eₗ Hₗ Aᵣ Bᵣ Cᵣ Dᵣ Eᵣ Hᵣ
    leftTurn rightTurn productTurn left right product turn lower upper
  exact signSearch?_isSome_of_admissible centers admissible

/-- Rational specialization of the finite center table. -/
theorem signSearch?_isSome_of_narrowTurns
    {Aₗ Bₗ Cₗ Dₗ Aᵣ Bᵣ Cᵣ Dᵣ : Coordinate}
    (AₗNonzero : Aₗ ≠ 0) (BₗNonzero : Bₗ ≠ 0)
    (CₗNonzero : Cₗ ≠ 0) (DₗNonzero : Dₗ ≠ 0)
    (EₗNonzero : Aₗ * Cₗ - Bₗ * Dₗ ≠ 0)
    (HₗNonzero : Aₗ * Dₗ + Bₗ * Cₗ ≠ 0)
    (AᵣNonzero : Aᵣ ≠ 0) (BᵣNonzero : Bᵣ ≠ 0)
    (CᵣNonzero : Cᵣ ≠ 0) (DᵣNonzero : Dᵣ ≠ 0)
    (EᵣNonzero : Aᵣ * Cᵣ - Bᵣ * Dᵣ ≠ 0)
    (HᵣNonzero : Aᵣ * Dᵣ + Bᵣ * Cᵣ ≠ 0)
    (leftNarrow : NarrowComplexTurn Aₗ Bₗ Aᵣ Bᵣ)
    (rightNarrow : NarrowComplexTurn Cₗ Dₗ Cᵣ Dᵣ) :
    (signSearch?
      (FiniteSign.ofCoordinate Aₗ) (FiniteSign.ofCoordinate Bₗ)
      (FiniteSign.ofCoordinate Cₗ) (FiniteSign.ofCoordinate Dₗ)
      (FiniteSign.ofCoordinate (Aₗ * Cₗ - Bₗ * Dₗ))
      (FiniteSign.ofCoordinate (Aₗ * Dₗ + Bₗ * Cₗ))
      (FiniteSign.ofCoordinate Aᵣ) (FiniteSign.ofCoordinate Bᵣ)
      (FiniteSign.ofCoordinate Cᵣ) (FiniteSign.ofCoordinate Dᵣ)
      (FiniteSign.ofCoordinate (Aᵣ * Cᵣ - Bᵣ * Dᵣ))
      (FiniteSign.ofCoordinate (Aᵣ * Dᵣ + Bᵣ * Cᵣ))).isSome := by
  let Eₗ := Aₗ * Cₗ - Bₗ * Dₗ
  let Hₗ := Aₗ * Dₗ + Bₗ * Cₗ
  let Eᵣ := Aᵣ * Cᵣ - Bᵣ * Dᵣ
  let Hᵣ := Aᵣ * Dᵣ + Bᵣ * Cᵣ
  let leftTurn := FiniteSign.ofCoordinate (Aₗ * Bᵣ - Bₗ * Aᵣ)
  let rightTurn := FiniteSign.ofCoordinate (Cₗ * Dᵣ - Dₗ * Cᵣ)
  let productTurn := FiniteSign.ofCoordinate (Eₗ * Hᵣ - Hₗ * Eᵣ)
  have leftSmall : FiniteTurn.SmallTurnCompatible
      (FiniteSign.ofCoordinate Aₗ) (FiniteSign.ofCoordinate Bₗ)
      (FiniteSign.ofCoordinate Aᵣ) (FiniteSign.ofCoordinate Bᵣ)
      leftTurn := by
    simpa only [leftTurn] using FiniteTurn.smallTurnCompatible_of_dot_pos
      AₗNonzero BₗNonzero AᵣNonzero BᵣNonzero
      (complexDot_pos_of_narrowComplexTurn leftNarrow)
  have rightSmall : FiniteTurn.SmallTurnCompatible
      (FiniteSign.ofCoordinate Cₗ) (FiniteSign.ofCoordinate Dₗ)
      (FiniteSign.ofCoordinate Cᵣ) (FiniteSign.ofCoordinate Dᵣ)
      rightTurn := by
    simpa only [rightTurn] using FiniteTurn.smallTurnCompatible_of_dot_pos
      CₗNonzero DₗNonzero CᵣNonzero DᵣNonzero
      (complexDot_pos_of_narrowComplexTurn rightNarrow)
  have productDotPositive : 0 < Eₗ * Eᵣ + Hₗ * Hᵣ := by
    simpa only [Eₗ, Hₗ, Eᵣ, Hᵣ] using
      productComplexDot_pos_of_narrowTurns leftNarrow rightNarrow
  have productSmall : FiniteTurn.SmallTurnCompatible
      (FiniteSign.ofCoordinate Eₗ) (FiniteSign.ofCoordinate Hₗ)
      (FiniteSign.ofCoordinate Eᵣ) (FiniteSign.ofCoordinate Hᵣ)
      productTurn := by
    apply FiniteTurn.smallTurnCompatible_of_dot_pos
      (by simpa only [Eₗ] using EₗNonzero)
      (by simpa only [Hₗ] using HₗNonzero)
      (by simpa only [Eᵣ] using EᵣNonzero)
      (by simpa only [Hᵣ] using HᵣNonzero)
    exact productDotPositive
  have turnCompatible : FiniteSign.SumCompatible
      leftTurn rightTurn productTurn := by
    simpa only [leftTurn, rightTurn, productTurn, Eₗ, Hₗ, Eᵣ, Hᵣ] using
      productTurn_sumCompatible_of_narrowTurns leftNarrow rightNarrow
  have lowerCompatible := finiteSign_complexProductCompatible Aₗ Bₗ Cₗ Dₗ
  have upperCompatible := finiteSign_complexProductCompatible Aᵣ Bᵣ Cᵣ Dᵣ
  simpa only [Eₗ, Hₗ, Eᵣ, Hᵣ] using signSearch?_isSome_of_smallTurns
    (FiniteSign.ofCoordinate Aₗ) (FiniteSign.ofCoordinate Bₗ)
    (FiniteSign.ofCoordinate Cₗ) (FiniteSign.ofCoordinate Dₗ)
    (FiniteSign.ofCoordinate Eₗ) (FiniteSign.ofCoordinate Hₗ)
    (FiniteSign.ofCoordinate Aᵣ) (FiniteSign.ofCoordinate Bᵣ)
    (FiniteSign.ofCoordinate Cᵣ) (FiniteSign.ofCoordinate Dᵣ)
    (FiniteSign.ofCoordinate Eᵣ) (FiniteSign.ofCoordinate Hᵣ)
    leftTurn rightTurn productTurn leftSmall rightSmall productSmall
    turnCompatible lowerCompatible upperCompatible

def Admissible
    (centers : ProductCenterSigns)
    (A B C D E H : Polynomial) (interval : Interval) : Prop :=
  centers.AdmissibleSigns
    (FiniteSign.ofCoordinate (A.eval interval.lower))
    (FiniteSign.ofCoordinate (B.eval interval.lower))
    (FiniteSign.ofCoordinate (C.eval interval.lower))
    (FiniteSign.ofCoordinate (D.eval interval.lower))
    (FiniteSign.ofCoordinate (E.eval interval.lower))
    (FiniteSign.ofCoordinate (H.eval interval.lower))
    (FiniteSign.ofCoordinate (A.eval interval.upper))
    (FiniteSign.ofCoordinate (B.eval interval.upper))
    (FiniteSign.ofCoordinate (C.eval interval.upper))
    (FiniteSign.ofCoordinate (D.eval interval.upper))
    (FiniteSign.ofCoordinate (E.eval interval.upper))
    (FiniteSign.ofCoordinate (H.eval interval.upper))

instance (centers : ProductCenterSigns)
    (A B C D E H : Polynomial) (interval : Interval) :
    Decidable (centers.Admissible A B C D E H interval) := by
  unfold Admissible
  infer_instance

def search?
    (A B C D E H : Polynomial) (interval : Interval) :
    Option ProductCenterSigns :=
  signSearch?
    (FiniteSign.ofCoordinate (A.eval interval.lower))
    (FiniteSign.ofCoordinate (B.eval interval.lower))
    (FiniteSign.ofCoordinate (C.eval interval.lower))
    (FiniteSign.ofCoordinate (D.eval interval.lower))
    (FiniteSign.ofCoordinate (E.eval interval.lower))
    (FiniteSign.ofCoordinate (H.eval interval.lower))
    (FiniteSign.ofCoordinate (A.eval interval.upper))
    (FiniteSign.ofCoordinate (B.eval interval.upper))
    (FiniteSign.ofCoordinate (C.eval interval.upper))
    (FiniteSign.ofCoordinate (D.eval interval.upper))
    (FiniteSign.ofCoordinate (E.eval interval.upper))
    (FiniteSign.ofCoordinate (H.eval interval.upper))

theorem search?_some_admissible
    {A B C D E H : Polynomial} {interval : Interval}
    {centers : ProductCenterSigns}
    (found : search? A B C D E H interval = some centers) :
    centers.Admissible A B C D E H interval := by
  exact signSearch?_some_admissible found

theorem search?_isSome_of_narrowTurns
    {A B C D E H : Polynomial} {interval : Interval}
    (AₗNonzero : A.eval interval.lower ≠ 0)
    (BₗNonzero : B.eval interval.lower ≠ 0)
    (CₗNonzero : C.eval interval.lower ≠ 0)
    (DₗNonzero : D.eval interval.lower ≠ 0)
    (EₗNonzero : E.eval interval.lower ≠ 0)
    (HₗNonzero : H.eval interval.lower ≠ 0)
    (AᵣNonzero : A.eval interval.upper ≠ 0)
    (BᵣNonzero : B.eval interval.upper ≠ 0)
    (CᵣNonzero : C.eval interval.upper ≠ 0)
    (DᵣNonzero : D.eval interval.upper ≠ 0)
    (EᵣNonzero : E.eval interval.upper ≠ 0)
    (HᵣNonzero : H.eval interval.upper ≠ 0)
    (productRealLowerEq : E.eval interval.lower =
      A.eval interval.lower * C.eval interval.lower -
        B.eval interval.lower * D.eval interval.lower)
    (productImagLowerEq : H.eval interval.lower =
      A.eval interval.lower * D.eval interval.lower +
        B.eval interval.lower * C.eval interval.lower)
    (productRealUpperEq : E.eval interval.upper =
      A.eval interval.upper * C.eval interval.upper -
        B.eval interval.upper * D.eval interval.upper)
    (productImagUpperEq : H.eval interval.upper =
      A.eval interval.upper * D.eval interval.upper +
        B.eval interval.upper * C.eval interval.upper)
    (leftNarrow : NarrowComplexTurn
      (A.eval interval.lower) (B.eval interval.lower)
      (A.eval interval.upper) (B.eval interval.upper))
    (rightNarrow : NarrowComplexTurn
      (C.eval interval.lower) (D.eval interval.lower)
      (C.eval interval.upper) (D.eval interval.upper)) :
    (search? A B C D E H interval).isSome := by
  unfold search?
  rw [productRealLowerEq, productImagLowerEq,
    productRealUpperEq, productImagUpperEq]
  exact signSearch?_isSome_of_narrowTurns
    AₗNonzero BₗNonzero CₗNonzero DₗNonzero
    (by simpa only [← productRealLowerEq] using EₗNonzero)
    (by simpa only [← productImagLowerEq] using HₗNonzero)
    AᵣNonzero BᵣNonzero CᵣNonzero DᵣNonzero
    (by simpa only [← productRealUpperEq] using EᵣNonzero)
    (by simpa only [← productImagUpperEq] using HᵣNonzero)
    leftNarrow rightNarrow

end ProductCenterSigns

/-- Complete executable local event-data classifier. -/
def localEventData?
    (A B C D E H : Polynomial) (interval : Interval) :
    Option (LocalEventData A B C D E H interval) := by
  match leftFound : cauchyEventSigns? A B interval with
  | none => exact none
  | some left =>
    match rightFound : cauchyEventSigns? C D interval with
    | none => exact none
    | some right =>
      match productFound : cauchyEventSigns? E H interval with
      | none => exact none
      | some product =>
        match centerFound : ProductCenterSigns.search?
            A B C D E H interval with
        | none => exact none
        | some centers =>
          if admissible : centers.Admissible A B C D E H interval then
            if leftImagLower : B.eval interval.lower ≠ 0 then
              if rightImagLower : D.eval interval.lower ≠ 0 then
                if productImagLower : H.eval interval.lower ≠ 0 then
                  if leftImagUpper : B.eval interval.upper ≠ 0 then
                    if rightImagUpper : D.eval interval.upper ≠ 0 then
                      if productImagUpper : H.eval interval.upper ≠ 0 then
                        if productRealLowerEq : E.eval interval.lower =
                            A.eval interval.lower * C.eval interval.lower -
                              B.eval interval.lower * D.eval interval.lower then
                          if productImagLowerEq : H.eval interval.lower =
                              A.eval interval.lower * D.eval interval.lower +
                                B.eval interval.lower * C.eval interval.lower then
                            if productRealUpperEq : E.eval interval.upper =
                                A.eval interval.upper * C.eval interval.upper -
                                  B.eval interval.upper * D.eval interval.upper then
                              if productImagUpperEq : H.eval interval.upper =
                                  A.eval interval.upper * D.eval interval.upper +
                                    B.eval interval.upper * C.eval interval.upper then
                                exact some (LocalEventData.ofRecenteredFactors
                                  left right product
                                  centers.factorLeftReal centers.factorLeftImag
                                  centers.factorRightReal centers.factorRightImag
                                  admissible.1 admissible.2.1 admissible.2.2
                                  leftImagLower rightImagLower productImagLower
                                  leftImagUpper rightImagUpper productImagUpper
                                  productRealLowerEq productImagLowerEq
                                  productRealUpperEq productImagUpperEq)
                              else exact none
                            else exact none
                          else exact none
                        else exact none
                      else exact none
                    else exact none
                  else exact none
                else exact none
              else exact none
            else exact none
          else exact none

theorem localEventData?_isSome
    {A B C D E H : Polynomial} {interval : Interval}
    (leftFound : (cauchyEventSigns? A B interval).isSome = true)
    (rightFound : (cauchyEventSigns? C D interval).isSome = true)
    (productFound : (cauchyEventSigns? E H interval).isSome = true)
    (centerFound :
      (ProductCenterSigns.search? A B C D E H interval).isSome = true)
    (leftImagLower : B.eval interval.lower ≠ 0)
    (rightImagLower : D.eval interval.lower ≠ 0)
    (productImagLower : H.eval interval.lower ≠ 0)
    (leftImagUpper : B.eval interval.upper ≠ 0)
    (rightImagUpper : D.eval interval.upper ≠ 0)
    (productImagUpper : H.eval interval.upper ≠ 0)
    (productRealLowerEq : E.eval interval.lower =
      A.eval interval.lower * C.eval interval.lower -
        B.eval interval.lower * D.eval interval.lower)
    (productImagLowerEq : H.eval interval.lower =
      A.eval interval.lower * D.eval interval.lower +
        B.eval interval.lower * C.eval interval.lower)
    (productRealUpperEq : E.eval interval.upper =
      A.eval interval.upper * C.eval interval.upper -
        B.eval interval.upper * D.eval interval.upper)
    (productImagUpperEq : H.eval interval.upper =
      A.eval interval.upper * D.eval interval.upper +
        B.eval interval.upper * C.eval interval.upper) :
    (localEventData? A B C D E H interval).isSome = true := by
  cases leftEquation : cauchyEventSigns? A B interval with
  | none => simp [leftEquation] at leftFound
  | some left =>
    cases rightEquation : cauchyEventSigns? C D interval with
    | none => simp [rightEquation] at rightFound
    | some right =>
      cases productEquation : cauchyEventSigns? E H interval with
      | none => simp [productEquation] at productFound
      | some product =>
        cases centerEquation : ProductCenterSigns.search?
            A B C D E H interval with
        | none => simp [centerEquation] at centerFound
        | some centers =>
          have admissible : centers.Admissible A B C D E H interval :=
            ProductCenterSigns.search?_some_admissible centerEquation
          have productImagLowerExpression :
              A.eval interval.lower * D.eval interval.lower +
                  B.eval interval.lower * C.eval interval.lower ≠ 0 := by
            intro zero
            apply productImagLower
            rw [productImagLowerEq, zero]
          have productImagUpperExpression :
              A.eval interval.upper * D.eval interval.upper +
                  B.eval interval.upper * C.eval interval.upper ≠ 0 := by
            intro zero
            apply productImagUpper
            rw [productImagUpperEq, zero]
          unfold localEventData?
          rw [leftEquation, rightEquation, productEquation, centerEquation]
          simp [admissible, leftImagLower, rightImagLower, leftImagUpper,
            rightImagUpper, productRealLowerEq, productImagLowerEq,
            productRealUpperEq, productImagUpperEq,
            productImagLowerExpression, productImagUpperExpression]

def localProductCell?
    (A B C D E H : Polynomial) (interval : Interval) : Bool :=
  (localEventData? A B C D E H interval).isSome

theorem auxiliaryProductFormula_of_localProductCell
    (A B C D E H : Polynomial) (interval : Interval)
    (checked : localProductCell? A B C D E H interval = true) :
    AuxiliaryProductFormula A B C D E H
      interval.lower interval.upper := by
  unfold localProductCell? at checked
  cases found : localEventData? A B C D E H interval with
  | none => simp [found] at checked
  | some data => exact data.auxiliaryProductFormula

end RFAP.CauchyProductCells
