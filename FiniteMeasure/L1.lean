import mathlib.Tactic.QuotientFreeRing
import FiniteMeasure.EnclosureObservation
import FiniteMeasure.Stability

/-!
# Finite rational L1 error

The exact integral of pointwise rational separation gives a finite analogue
of L1 distance.  It supports the metric-style inequalities and controls
expectation error by direct finite summation.  Indicator distance is exactly
the probability or content of an executable symmetric difference.

No function-space completion, equivalence class, convergence mode, or limit
is constructed.
-/

namespace FiniteMeasure

/-- Rational separation satisfies the triangle inequality directly. -/
theorem rationalSeparation_triangle
    (left middle right : Coordinate) :
    rationalSeparation left right ≤
      rationalSeparation left middle + rationalSeparation middle right := by
  apply max_le
  · calc
      left - right = (left - middle) + (middle - right) := by ring1
      _ ≤ rationalSeparation left middle +
          rationalSeparation middle right :=
        add_le_add (le_max_left _ _) (le_max_left _ _)
  · calc
      right - left = (middle - left) + (right - middle) := by ring1
      _ ≤ rationalSeparation left middle +
          rationalSeparation middle right :=
        add_le_add (le_max_right _ _) (le_max_right _ _)

/-- Adding two pairs of rational values is subadditive for rational
separation. -/
theorem rationalSeparation_add_le
    (leftFirst leftSecond rightFirst rightSecond : Coordinate) :
    rationalSeparation (leftFirst + leftSecond) (rightFirst + rightSecond) ≤
      rationalSeparation leftFirst rightFirst +
        rationalSeparation leftSecond rightSecond := by
  apply max_le
  · calc
      leftFirst + leftSecond - (rightFirst + rightSecond) =
          (leftFirst - rightFirst) + (leftSecond - rightSecond) := by ring1
      _ ≤ rationalSeparation leftFirst rightFirst +
          rationalSeparation leftSecond rightSecond :=
        add_le_add (le_max_left _ _) (le_max_left _ _)
  · calc
      rightFirst + rightSecond - (leftFirst + leftSecond) =
          (rightFirst - leftFirst) + (rightSecond - leftSecond) := by ring1
      _ ≤ rationalSeparation leftFirst rightFirst +
          rationalSeparation leftSecond rightSecond :=
        add_le_add (le_max_right _ _) (le_max_right _ _)

/-- Negating both rational values preserves their separation. -/
theorem rationalSeparation_neg (left right : Coordinate) :
    rationalSeparation (-left) (-right) =
      rationalSeparation left right := by
  unfold rationalSeparation
  calc
    max (-left - -right) (-right - -left) =
        max (right - left) (left - right) := by
      congr 1 <;> ring1
    _ = max (left - right) (right - left) := max_comm _ _

/-- Subtracting two pairs of rational values is subadditive for rational
separation. -/
theorem rationalSeparation_sub_le
    (leftFirst leftSecond rightFirst rightSecond : Coordinate) :
    rationalSeparation (leftFirst - leftSecond)
        (rightFirst - rightSecond) ≤
      rationalSeparation leftFirst rightFirst +
        rationalSeparation leftSecond rightSecond := by
  change rationalSeparation (leftFirst + -leftSecond)
      (rightFirst + -rightSecond) ≤
    rationalSeparation leftFirst rightFirst +
      rationalSeparation leftSecond rightSecond
  calc
    rationalSeparation (leftFirst + -leftSecond)
        (rightFirst + -rightSecond) ≤
      rationalSeparation leftFirst rightFirst +
        rationalSeparation (-leftSecond) (-rightSecond) :=
      rationalSeparation_add_le _ _ _ _
    _ = rationalSeparation leftFirst rightFirst +
        rationalSeparation leftSecond rightSecond := by
      rw [rationalSeparation_neg]

/-- Rational separation between two values is separation of their explicit
difference from zero. -/
theorem rationalSeparation_eq_sub_zero
    (left right : Coordinate) :
    rationalSeparation left right =
      rationalSeparation (left - right) 0 := by
  unfold rationalSeparation
  congr 1 <;> ring1

theorem rationalSeparation_zero_of_nonneg
    {value : Coordinate} (nonnegative : 0 ≤ value) :
    rationalSeparation value 0 = value := by
  unfold rationalSeparation
  rw [sub_zero, zero_sub]
  apply max_eq_left
  exact (neg_nonpos.mpr nonnegative).trans nonnegative

theorem rationalSeparation_zero_of_nonpos
    {value : Coordinate} (nonpositive : value ≤ 0) :
    rationalSeparation value 0 = -value := by
  unfold rationalSeparation
  rw [sub_zero, zero_sub]
  apply max_eq_right
  exact nonpositive.trans (neg_nonneg.mpr nonpositive)

/-- Rational separation from zero is subadditive. -/
theorem rationalSeparation_add_zero_le (left right : Coordinate) :
    rationalSeparation (left + right) 0 ≤
      rationalSeparation left 0 + rationalSeparation right 0 := by
  apply max_le
  · calc
      left + right - 0 = (left - 0) + (right - 0) := by ring1
      _ ≤ rationalSeparation left 0 + rationalSeparation right 0 :=
        add_le_add (le_max_left _ _) (le_max_left _ _)
  · calc
      0 - (left + right) = (0 - left) + (0 - right) := by ring1
      _ ≤ rationalSeparation left 0 + rationalSeparation right 0 :=
        add_le_add (le_max_right _ _) (le_max_right _ _)

/-- Rational separation from zero is exactly multiplicative. -/
theorem rationalSeparation_mul_zero (left right : Coordinate) :
    rationalSeparation (left * right) 0 =
      rationalSeparation left 0 * rationalSeparation right 0 := by
  by_cases leftNonnegative : 0 ≤ left
  · by_cases rightNonnegative : 0 ≤ right
    · have productNonnegative :=
        RFAP.ConstructiveFraction.mul_nonneg_direct
          leftNonnegative rightNonnegative
      rw [rationalSeparation_zero_of_nonneg productNonnegative,
        rationalSeparation_zero_of_nonneg leftNonnegative,
        rationalSeparation_zero_of_nonneg rightNonnegative]
    · have rightNonpositive : right ≤ 0 :=
        (RFAP.ConstructiveFraction.lt_of_not_ge_direct
          rightNonnegative).le
      have productNonpositive : left * right ≤ 0 := by
        apply neg_nonneg.mp
        calc
          0 ≤ left * (-right) :=
            RFAP.ConstructiveFraction.mul_nonneg_direct leftNonnegative
              (neg_nonneg.mpr rightNonpositive)
          _ = -(left * right) := by ring1
      rw [rationalSeparation_zero_of_nonpos productNonpositive,
        rationalSeparation_zero_of_nonneg leftNonnegative,
        rationalSeparation_zero_of_nonpos rightNonpositive]
      ring1
  · have leftNonpositive : left ≤ 0 :=
      (RFAP.ConstructiveFraction.lt_of_not_ge_direct leftNonnegative).le
    by_cases rightNonnegative : 0 ≤ right
    · have productNonpositive : left * right ≤ 0 := by
        apply neg_nonneg.mp
        calc
          0 ≤ (-left) * right :=
            RFAP.ConstructiveFraction.mul_nonneg_direct
              (neg_nonneg.mpr leftNonpositive) rightNonnegative
          _ = -(left * right) := by ring1
      rw [rationalSeparation_zero_of_nonpos productNonpositive,
        rationalSeparation_zero_of_nonpos leftNonpositive,
        rationalSeparation_zero_of_nonneg rightNonnegative]
      ring1
    · have rightNonpositive : right ≤ 0 :=
        (RFAP.ConstructiveFraction.lt_of_not_ge_direct
          rightNonnegative).le
      have productNonnegative : 0 ≤ left * right := by
        have product := RFAP.ConstructiveFraction.mul_nonneg_direct
          (neg_nonneg.mpr leftNonpositive)
          (neg_nonneg.mpr rightNonpositive)
        have equal : (-left) * (-right) = left * right := by ring1
        rw [equal] at product
        exact product
      rw [rationalSeparation_zero_of_nonneg productNonnegative,
        rationalSeparation_zero_of_nonpos leftNonpositive,
        rationalSeparation_zero_of_nonpos rightNonpositive]
      ring1

/-- Scaling both arguments scales rational separation by the exact rational
magnitude of the factor. -/
theorem rationalSeparation_scale (factor left right : Coordinate) :
    rationalSeparation (factor * left) (factor * right) =
      rationalSeparation factor 0 * rationalSeparation left right := by
  calc
    rationalSeparation (factor * left) (factor * right) =
        rationalSeparation (factor * left - factor * right) 0 :=
      rationalSeparation_eq_sub_zero _ _
    _ = rationalSeparation (factor * (left - right)) 0 := by
      congr 1
      ring1
    _ = rationalSeparation factor 0 * rationalSeparation (left - right) 0 :=
      rationalSeparation_mul_zero factor (left - right)
    _ = rationalSeparation factor 0 * rationalSeparation left right := by
      exact congrArg (fun magnitude => rationalSeparation factor 0 * magnitude)
        (rationalSeparation_eq_sub_zero left right).symm

namespace FiniteContent

/-- Exact finite rational L1 error between two displayed observables. -/
def l1Distance {α : Type} (content : FiniteContent α)
    (left right : α → Coordinate) : Coordinate :=
  content.integral fun item => rationalSeparation (left item) (right item)

theorem l1Distance_nonneg {α : Type} (content : FiniteContent α)
    (left right : α → Coordinate) :
    0 ≤ content.l1Distance left right := by
  apply content.integral_nonneg
  intro atom member
  exact rationalSeparation_nonneg _ _

theorem l1Distance_refl {α : Type} (content : FiniteContent α)
    (value : α → Coordinate) :
    content.l1Distance value value = 0 := by
  calc
    content.l1Distance value value =
        content.integral (fun _ => 0) := by
      exact content.integral_congr _ _ (fun item => by
        simp only [rationalSeparation, sub_self, max_self])
    _ = content.total * 0 := content.integral_constant 0
    _ = 0 := mul_zero _

theorem l1Distance_symm {α : Type} (content : FiniteContent α)
    (left right : α → Coordinate) :
    content.l1Distance left right = content.l1Distance right left := by
  exact content.integral_congr _ _ (fun item =>
    rationalSeparation_symm _ _)

theorem l1Distance_triangle {α : Type} (content : FiniteContent α)
    (left middle right : α → Coordinate) :
    content.l1Distance left right ≤
      content.l1Distance left middle + content.l1Distance middle right := by
  calc
    content.l1Distance left right ≤
        content.integral (fun item =>
          rationalSeparation (left item) (middle item) +
            rationalSeparation (middle item) (right item)) := by
      apply content.integral_mono
      intro atom member
      exact rationalSeparation_triangle _ _ _
    _ = content.l1Distance left middle +
        content.l1Distance middle right := by
      exact content.integral_add _ _

/-- Reverse triangle inequality for exact finite L1 distances.  Distances
from a common anchor can differ by at most the distance between their
endpoints. -/
theorem l1Distance_reverse_triangle {α : Type}
    (content : FiniteContent α)
    (first second anchor : α → Coordinate) :
    rationalSeparation (content.l1Distance first anchor)
        (content.l1Distance second anchor) ≤
      content.l1Distance first second := by
  unfold rationalSeparation
  apply max_le
  · apply (sub_le_iff_le_add).2
    exact content.l1Distance_triangle first second anchor
  · apply (sub_le_iff_le_add).2
    calc
      content.l1Distance second anchor ≤
          content.l1Distance second first +
            content.l1Distance first anchor :=
        content.l1Distance_triangle second first anchor
      _ = content.l1Distance first second +
            content.l1Distance first anchor := by
        rw [content.l1Distance_symm second first]

/-- Exact finite L1 error bounds both directed differences of integrals. -/
theorem integral_close_l1 {α : Type} (content : FiniteContent α)
    (left right : α → Coordinate) :
    content.integral right - content.integral left ≤
        content.l1Distance left right ∧
      content.integral left - content.integral right ≤
        content.l1Distance left right := by
  apply content.integral_symmetricError
  intro atom member
  exact ⟨le_max_right _ _, le_max_left _ _⟩

/-- Rational separation of two exact finite integrals is bounded by the
finite L1 distance of their integrands. -/
theorem integral_separation_le_l1Distance {α : Type}
    (content : FiniteContent α) (left right : α → Coordinate) :
    rationalSeparation (content.integral left) (content.integral right) ≤
      content.l1Distance left right := by
  have close := content.integral_close_l1 left right
  unfold rationalSeparation
  exact max_le close.2 close.1

end FiniteContent

namespace Distribution

/-- Probability-weighted finite rational L1 error. -/
def l1Distance {α : Type} (distribution : Distribution α)
    (left right : α → Coordinate) : Coordinate :=
  distribution.expectation fun item =>
    rationalSeparation (left item) (right item)

theorem l1Distance_nonneg {α : Type} (distribution : Distribution α)
    (left right : α → Coordinate) :
    0 ≤ distribution.l1Distance left right := by
  apply distribution.expectation_nonneg
  intro atom member
  exact rationalSeparation_nonneg _ _

theorem l1Distance_refl {α : Type} (distribution : Distribution α)
    (value : α → Coordinate) :
    distribution.l1Distance value value = 0 := by
  change distribution.toFiniteContent.l1Distance value value = 0
  exact distribution.toFiniteContent.l1Distance_refl value

theorem l1Distance_symm {α : Type} (distribution : Distribution α)
    (left right : α → Coordinate) :
    distribution.l1Distance left right =
      distribution.l1Distance right left := by
  exact distribution.expectation_congr _ _ (fun item =>
    rationalSeparation_symm _ _)

theorem l1Distance_triangle {α : Type} (distribution : Distribution α)
    (left middle right : α → Coordinate) :
    distribution.l1Distance left right ≤
      distribution.l1Distance left middle +
        distribution.l1Distance middle right := by
  change distribution.toFiniteContent.l1Distance left right ≤
    distribution.toFiniteContent.l1Distance left middle +
      distribution.toFiniteContent.l1Distance middle right
  exact distribution.toFiniteContent.l1Distance_triangle left middle right

/-- Reverse triangle inequality for normalized finite L1 distance. -/
theorem l1Distance_reverse_triangle {α : Type}
    (distribution : Distribution α)
    (first second anchor : α → Coordinate) :
    rationalSeparation (distribution.l1Distance first anchor)
        (distribution.l1Distance second anchor) ≤
      distribution.l1Distance first second :=
  distribution.toFiniteContent.l1Distance_reverse_triangle
    first second anchor

/-- Probability-weighted L1 error bounds both directed expectation
differences. -/
theorem expectation_close_l1 {α : Type} (distribution : Distribution α)
    (left right : α → Coordinate) :
    distribution.expectation right - distribution.expectation left ≤
        distribution.l1Distance left right ∧
      distribution.expectation left - distribution.expectation right ≤
        distribution.l1Distance left right := by
  change distribution.toFiniteContent.integral right -
        distribution.toFiniteContent.integral left ≤
      distribution.toFiniteContent.l1Distance left right ∧
    distribution.toFiniteContent.integral left -
        distribution.toFiniteContent.integral right ≤
      distribution.toFiniteContent.l1Distance left right
  exact distribution.toFiniteContent.integral_close_l1 left right

/-- Rational separation of finite expectations is at most the exact L1
distance. -/
theorem expectation_separation_le_l1Distance {α : Type}
    (distribution : Distribution α) (left right : α → Coordinate) :
    rationalSeparation (distribution.expectation left)
        (distribution.expectation right) ≤
      distribution.l1Distance left right := by
  have close := distribution.expectation_close_l1 left right
  unfold rationalSeparation
  exact max_le close.2 close.1

/-- A uniform pointwise error certificate bounds exact finite L1 error by
the same rational allowance. -/
theorem l1Distance_le_of_uniform {α : Type}
    (distribution : Distribution α) (epsilon : Coordinate)
    (left right : α → Coordinate)
    (bounded : SymmetricErrorOn distribution.atoms
      (fun _ => epsilon) left right) :
    distribution.l1Distance left right ≤ epsilon := by
  calc
    distribution.l1Distance left right ≤
        distribution.expectation (fun _ => epsilon) := by
      apply distribution.expectation_mono
      intro atom member
      exact max_le (bounded atom member).2 (bounded atom member).1
    _ = epsilon := distribution.expectation_constant epsilon

end Distribution

/-- Executable event that two rational observables are separated by at
least a displayed rational threshold. -/
def separationAtLeast {α : Type} (threshold : Coordinate)
    (left right : α → Coordinate) : α → Bool :=
  fun item => decide
    (threshold ≤ rationalSeparation (left item) (right item))

/-- Executable symmetric difference of two finite events. -/
def symmetricDifferenceEvent {α : Type}
    (first second : α → Bool) : α → Bool :=
  fun item => first item != second item

theorem indicator_rationalSeparation
    {α : Type} (first second : α → Bool) (item : α) :
    rationalSeparation
        (Distribution.indicator first item)
        (Distribution.indicator second item) =
      Distribution.indicator (symmetricDifferenceEvent first second) item := by
  cases firstSelected : first item <;>
    cases secondSelected : second item <;>
    simp only [rationalSeparation, Distribution.indicator,
      symmetricDifferenceEvent, firstSelected, secondSelected] <;>
    decide

namespace FiniteContent

/-- L1 distance between two indicators is exactly the finite content of
their symmetric difference. -/
theorem l1Distance_indicator {α : Type} (content : FiniteContent α)
    (first second : α → Bool) :
    content.l1Distance (Distribution.indicator first)
        (Distribution.indicator second) =
      content.measure (symmetricDifferenceEvent first second) := by
  unfold l1Distance
  calc
    content.integral (fun item =>
          rationalSeparation
            (Distribution.indicator first item)
            (Distribution.indicator second item)) =
        content.integral
          (Distribution.indicator (symmetricDifferenceEvent first second)) := by
      exact content.integral_congr _ _ (fun item =>
        indicator_rationalSeparation first second item)
    _ = content.measure (symmetricDifferenceEvent first second) :=
      content.integral_indicator _

end FiniteContent

namespace Distribution

/-- Finite one-shot L1-to-large-error bound.  This is the quantitative core
usually used in the implication from L1 convergence to convergence in
probability, stated here without any sequence or limiting object. -/
theorem probability_separationAtLeast_le_l1 {α : Type}
    (distribution : Distribution α) (threshold : Coordinate)
    (positive : 0 < threshold) (left right : α → Coordinate) :
    distribution.probability (separationAtLeast threshold left right) ≤
      distribution.l1Distance left right / threshold := by
  apply distribution.markov_bound
    (separationAtLeast threshold left right)
    (fun item => rationalSeparation (left item) (right item))
    threshold positive
  · intro atom member
    exact rationalSeparation_nonneg _ _
  · intro atom member selected
    exact of_decide_eq_true selected

/-- Indicator L1 distance is exactly finite symmetric-difference
probability. -/
theorem l1Distance_indicator {α : Type} (distribution : Distribution α)
    (first second : α → Bool) :
    distribution.l1Distance (indicator first) (indicator second) =
      distribution.probability (symmetricDifferenceEvent first second) := by
  change distribution.toFiniteContent.l1Distance
      (indicator first) (indicator second) =
    distribution.toFiniteContent.measure
      (symmetricDifferenceEvent first second)
  exact distribution.toFiniteContent.l1Distance_indicator first second

/-- Difference of any two finite event probabilities is controlled by their
exact symmetric-difference probability. -/
theorem probability_close_symmetricDifference {α : Type}
    (distribution : Distribution α) (first second : α → Bool) :
    distribution.probability second - distribution.probability first ≤
        distribution.probability (symmetricDifferenceEvent first second) ∧
      distribution.probability first - distribution.probability second ≤
        distribution.probability (symmetricDifferenceEvent first second) := by
  have bound := distribution.expectation_close_l1
    (indicator first) (indicator second)
  rw [distribution.expectation_indicator,
    distribution.expectation_indicator,
    distribution.l1Distance_indicator] at bound
  exact bound

end Distribution

end FiniteMeasure
