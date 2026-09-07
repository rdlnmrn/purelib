import mathlib.Tactic.QuotientFreeRing
import FiniteMeasure.ContentOperations

/-!
# Exact integration against finite contents

A finite-content integral is an exact rational weighted sum.  The usual
linearity, monotonicity, indicator, restriction, and pushforward identities
are all finite list calculations.
-/

namespace FiniteMeasure

theorem expectationWeight_mapAtoms {α β : Type}
    (function : α → β) (value : β → Coordinate) :
    ∀ atoms : List (Weighted α),
      Distribution.expectationWeight (mapAtoms function atoms) value =
        Distribution.expectationWeight atoms
          (fun item => value (function item))
  | [] => rfl
  | atom :: remaining => by
      simp only [mapAtoms, Distribution.expectationWeight,
        expectationWeight_mapAtoms function value remaining]

theorem expectationWeight_restrictAtoms {α : Type}
    (condition : α → Bool) (value : α → Coordinate) :
    ∀ atoms : List (Weighted α),
      Distribution.expectationWeight (restrictAtoms atoms condition) value =
        Distribution.expectationWeight atoms
          (fun item => Distribution.indicator condition item * value item)
  | [] => rfl
  | atom :: remaining => by
      cases selected : condition atom.item <;>
        simp only [restrictAtoms, selected, Bool.false_eq_true, ↓reduceIte,
          Distribution.expectationWeight, Distribution.indicator,
          zero_mul, mul_zero, zero_add, one_mul,
          expectationWeight_restrictAtoms condition value remaining]

/-- Finite Fubini identity for a separable rational observable on a
displayed product atom list. -/
theorem expectationWeight_productAtoms_mul {α β : Type}
    (leftValue : α → Coordinate) (rightValue : β → Coordinate) :
    ∀ (left : List (Weighted α)) (right : List (Weighted β)),
      Distribution.expectationWeight (productAtoms left right)
          (fun pair => leftValue pair.1 * rightValue pair.2) =
        Distribution.expectationWeight left leftValue *
          Distribution.expectationWeight right rightValue
  | [], right => by
      simp only [productAtoms, Distribution.expectationWeight, zero_mul]
  | atom :: remaining, right => by
      rw [productAtoms, expectationWeight_append,
        expectationWeight_scaleAtoms, expectationWeight_mapAtoms,
        expectationWeight_productAtoms_mul leftValue rightValue remaining right]
      change atom.weight *
            Distribution.expectationWeight right
              (fun item => leftValue atom.item * rightValue item) +
          Distribution.expectationWeight remaining leftValue *
            Distribution.expectationWeight right rightValue =
        (atom.weight * leftValue atom.item +
            Distribution.expectationWeight remaining leftValue) *
          Distribution.expectationWeight right rightValue
      rw [Distribution.expectationWeight_scale]
      ring1

/-- Full finite Fubini identity for an arbitrary rational observable on a
displayed product atom list. -/
theorem expectationWeight_productAtoms {α β : Type}
    (value : α × β → Coordinate) :
    ∀ (left : List (Weighted α)) (right : List (Weighted β)),
      Distribution.expectationWeight (productAtoms left right) value =
        Distribution.expectationWeight left (fun leftItem =>
          Distribution.expectationWeight right (fun rightItem =>
            value (leftItem, rightItem)))
  | [], right => rfl
  | atom :: remaining, right => by
      rw [productAtoms, expectationWeight_append,
        expectationWeight_scaleAtoms, expectationWeight_mapAtoms,
        expectationWeight_productAtoms value remaining right]
      rfl

namespace FiniteContent

/-- Exact rational integral of a displayed rational observable. -/
def integral {α : Type} (content : FiniteContent α)
    (value : α → Coordinate) : Coordinate :=
  Distribution.expectationWeight content.atoms value

/-- Pointwise equality is sufficient for equality of exact finite
integrals; no equality of function-valued observables is required. -/
theorem integral_congr {α : Type} (content : FiniteContent α)
    (left right : α → Coordinate)
    (pointwise : ∀ item, left item = right item) :
    content.integral left = content.integral right :=
  Distribution.expectationWeight_congr content.atoms left right pointwise

theorem scale_integral {α : Type} (content : FiniteContent α)
    (factor : Coordinate) (nonnegative : 0 ≤ factor)
    (value : α → Coordinate) :
    (content.scale factor nonnegative).integral value =
      factor * content.integral value :=
  expectationWeight_scaleAtoms factor nonnegative content.atoms value

theorem append_integral {α : Type} (left right : FiniteContent α)
    (value : α → Coordinate) :
    (left.append right).integral value =
      left.integral value + right.integral value :=
  expectationWeight_append left.atoms right.atoms value

theorem integral_add {α : Type} (content : FiniteContent α)
    (left right : α → Coordinate) :
    content.integral (fun item => left item + right item) =
      content.integral left + content.integral right :=
  Distribution.expectationWeight_add content.atoms left right

theorem integral_scale {α : Type} (content : FiniteContent α)
    (factor : Coordinate) (value : α → Coordinate) :
    content.integral (fun item => factor * value item) =
      factor * content.integral value :=
  Distribution.expectationWeight_scale content.atoms factor value

theorem integral_nonneg {α : Type} (content : FiniteContent α)
    (value : α → Coordinate)
    (nonnegative : ∀ atom, atom ∈ content.atoms → 0 ≤ value atom.item) :
    0 ≤ content.integral value :=
  Distribution.expectationWeight_nonneg content.atoms value nonnegative

theorem integral_mono {α : Type} (content : FiniteContent α)
    (lower upper : α → Coordinate)
    (pointwise : ∀ atom, atom ∈ content.atoms →
      lower atom.item ≤ upper atom.item) :
    content.integral lower ≤ content.integral upper :=
  Distribution.expectationWeight_mono content.atoms lower upper pointwise

theorem integral_indicator {α : Type} (content : FiniteContent α)
    (event : α → Bool) :
    content.integral (Distribution.indicator event) = content.measure event := by
  unfold integral measure
  induction content.atoms with
  | nil => rfl
  | cons atom remaining inductionHypothesis =>
      cases selected : event atom.item <;>
        simp only [Distribution.expectationWeight, eventWeight,
          Distribution.indicator, selected, mul_zero, zero_add, mul_one,
          inductionHypothesis]

theorem integral_constant {α : Type} (content : FiniteContent α)
    (constant : Coordinate) :
    content.integral (fun _ => constant) = content.total * constant := by
  unfold integral total
  induction content.atoms with
  | nil =>
      simp only [Distribution.expectationWeight, totalWeight, zero_mul]
  | cons atom remaining inductionHypothesis =>
      simp only [Distribution.expectationWeight, totalWeight,
        inductionHypothesis]
      ring1

/-- Restriction is multiplication by the exact finite indicator inside the
original integral. -/
theorem restrict_integral {α : Type} (content : FiniteContent α)
    (condition : α → Bool) (value : α → Coordinate) :
    (content.restrict condition).integral value =
      content.integral (fun item =>
        Distribution.indicator condition item * value item) :=
  expectationWeight_restrictAtoms condition value content.atoms

/-- Exact finite change of variables for pushforward content. -/
theorem map_integral {α β : Type} (content : FiniteContent α)
    (function : α → β) (value : β → Coordinate) :
    (content.map function).integral value =
      content.integral (fun item => value (function item)) :=
  expectationWeight_mapAtoms function value content.atoms

/-- Finite Fubini factorization for a separable rational observable. -/
theorem product_integral_mul {α β : Type}
    (left : FiniteContent α) (right : FiniteContent β)
    (leftValue : α → Coordinate) (rightValue : β → Coordinate) :
    (left.product right).integral
        (fun pair => leftValue pair.1 * rightValue pair.2) =
      left.integral leftValue * right.integral rightValue :=
  expectationWeight_productAtoms_mul leftValue rightValue
    left.atoms right.atoms

/-- Full finite Fubini theorem for exact rational contents. -/
theorem product_integral {α β : Type}
    (left : FiniteContent α) (right : FiniteContent β)
    (value : α × β → Coordinate) :
    (left.product right).integral value =
      left.integral (fun leftItem =>
        right.integral (fun rightItem => value (leftItem, rightItem))) :=
  expectationWeight_productAtoms value left.atoms right.atoms

/-- Exact integration cells representing a finite-content integral. -/
def integralCells {α : Type} (content : FiniteContent α)
    (value : α → Coordinate) : List (IntegrationCell α) :=
  content.atoms.map fun atom =>
    IntegrationCell.exact atom.item atom.weight (value atom.item)
      atom.nonnegative

theorem lowerIntegral_integralCells {α : Type}
    (content : FiniteContent α) (value : α → Coordinate) :
    lowerIntegral (content.integralCells value) = content.integral value := by
  unfold integralCells integral
  induction content.atoms with
  | nil => rfl
  | cons atom remaining inductionHypothesis =>
      simp only [List.map_cons, lowerIntegral,
        Distribution.expectationWeight]
      rw [inductionHypothesis]
      rfl

theorem upperIntegral_integralCells {α : Type}
    (content : FiniteContent α) (value : α → Coordinate) :
    upperIntegral (content.integralCells value) = content.integral value := by
  unfold integralCells integral
  induction content.atoms with
  | nil => rfl
  | cons atom remaining inductionHypothesis =>
      simp only [List.map_cons, upperIntegral,
        Distribution.expectationWeight]
      rw [inductionHypothesis]
      rfl

/-- Exact finite integration is the zero-width special case of the generic
lower/upper integration enclosure. -/
theorem integralBound_integralCells {α : Type}
    (content : FiniteContent α) (value : α → Coordinate) :
    integralBound (content.integralCells value) =
      Bound.exact (content.integral value) := by
  apply Bound.ext
  · exact content.lowerIntegral_integralCells value
  · exact content.upperIntegral_integralCells value

end FiniteContent

end FiniteMeasure
