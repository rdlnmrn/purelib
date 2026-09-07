import mathlib.Tactic.QuotientFreeRing
import FiniteMeasure.PushforwardLp
import FiniteMeasure.ContentOperations
import FiniteMeasure.Stochastic

/-!
# Essential maxima on explicit finite products

The computed essential maximum of a separable product factors exactly over
the Cartesian product of two displayed finite contents.  The proof follows
the executable atom-list construction, treating zero weights directly; no
supremum, maximizing choice, or product sigma algebra is used.
-/

namespace FiniteMeasure

private theorem essentialMaximumMagnitudeOn_append {α : Type}
    (value : α → Coordinate) : ∀ left right : List (Weighted α),
    essentialMaximumMagnitudeOn value (left ++ right) =
      max (essentialMaximumMagnitudeOn value left)
        (essentialMaximumMagnitudeOn value right)
  | [], right => by
      simp only [List.nil_append, essentialMaximumMagnitudeOn]
      exact (max_eq_right
        (essentialMaximumMagnitudeOn_nonnegative value right)).symm
  | atom :: remaining, right => by
      by_cases zero : atom.weight = 0
      · simp only [List.cons_append, essentialMaximumMagnitudeOn, zero,
          ↓reduceIte,
          essentialMaximumMagnitudeOn_append value remaining right]
      · simp only [List.cons_append, essentialMaximumMagnitudeOn, zero,
          ↓reduceIte,
          essentialMaximumMagnitudeOn_append value remaining right]
        exact (max_assoc _ _ _).symm

private theorem essentialMaximumMagnitudeOn_mapAtoms {α β : Type}
    (function : α → β) (value : β → Coordinate) :
    ∀ atoms : List (Weighted α),
      essentialMaximumMagnitudeOn value (mapAtoms function atoms) =
        essentialMaximumMagnitudeOn (fun item => value (function item)) atoms
  | [] => rfl
  | atom :: remaining => by
      simp only [mapAtoms, essentialMaximumMagnitudeOn,
        essentialMaximumMagnitudeOn_mapAtoms function value remaining]

private theorem essentialMaximumMagnitudeOn_scaleAtoms_zero {α : Type}
    (value : α → Coordinate) (nonnegative : 0 ≤ (0 : Coordinate)) :
    ∀ atoms : List (Weighted α),
      essentialMaximumMagnitudeOn value
          (scaleAtoms 0 nonnegative atoms) = 0
  | [] => rfl
  | atom :: remaining => by
      simp only [scaleAtoms, zero_mul, essentialMaximumMagnitudeOn,
        ↓reduceIte,
        essentialMaximumMagnitudeOn_scaleAtoms_zero value nonnegative
          remaining]

private theorem essentialMaximumMagnitudeOn_scaleAtoms_of_eq_zero {α : Type}
    (value : α → Coordinate) (factor : Coordinate)
    (nonnegative : 0 ≤ factor) (factorZero : factor = 0)
    (atoms : List (Weighted α)) :
    essentialMaximumMagnitudeOn value
        (scaleAtoms factor nonnegative atoms) = 0 := by
  subst factor
  exact essentialMaximumMagnitudeOn_scaleAtoms_zero value nonnegative atoms

private theorem essentialMaximumMagnitudeOn_scaleAtoms_of_ne {α : Type}
    (value : α → Coordinate) (factor : Coordinate)
    (nonnegative : 0 ≤ factor) (factorNonzero : factor ≠ 0) :
    ∀ atoms : List (Weighted α),
      essentialMaximumMagnitudeOn value
          (scaleAtoms factor nonnegative atoms) =
        essentialMaximumMagnitudeOn value atoms
  | [] => rfl
  | atom :: remaining => by
      by_cases atomZero : atom.weight = 0
      · simp only [scaleAtoms, essentialMaximumMagnitudeOn, atomZero,
          mul_zero, ↓reduceIte,
          essentialMaximumMagnitudeOn_scaleAtoms_of_ne value factor
            nonnegative factorNonzero remaining]
      · have productNonzero : factor * atom.weight ≠ 0 :=
          RFAP.ConstructiveFraction.mul_ne_zero_direct
            factorNonzero atomZero
        simp only [scaleAtoms, essentialMaximumMagnitudeOn, productNonzero,
          atomZero, ↓reduceIte,
          essentialMaximumMagnitudeOn_scaleAtoms_of_ne value factor
            nonnegative factorNonzero remaining]

private theorem essentialMaximumMagnitudeOn_productRow {α β : Type}
    (leftItem : α) (leftValue : α → Coordinate)
    (rightValue : β → Coordinate) (right : List (Weighted β)) :
    essentialMaximumMagnitudeOn
        (fun pair => leftValue pair.1 * rightValue pair.2)
        (mapAtoms (fun rightItem => (leftItem, rightItem)) right) =
      rationalSeparation (leftValue leftItem) 0 *
        essentialMaximumMagnitudeOn rightValue right := by
  rw [essentialMaximumMagnitudeOn_mapAtoms]
  simpa only [FiniteContent.essentialMaximumMagnitude] using
    (show
      (⟨right⟩ : FiniteContent β).essentialMaximumMagnitude
          (fun item => leftValue leftItem * rightValue item) =
        rationalSeparation (leftValue leftItem) 0 *
          (⟨right⟩ : FiniteContent β).essentialMaximumMagnitude rightValue
      from
        (⟨right⟩ : FiniteContent β).essentialMaximumMagnitude_scale
          (leftValue leftItem) rightValue)

private theorem essentialMaximumMagnitudeOn_magnitude {α : Type}
    (value : α → Coordinate) : ∀ atoms : List (Weighted α),
    essentialMaximumMagnitudeOn
        (fun item => rationalSeparation (value item) 0) atoms =
      essentialMaximumMagnitudeOn value atoms
  | [] => rfl
  | atom :: remaining => by
      by_cases zero : atom.weight = 0
      · simp only [essentialMaximumMagnitudeOn, zero, ↓reduceIte,
          essentialMaximumMagnitudeOn_magnitude value remaining]
      · simp only [essentialMaximumMagnitudeOn, zero, ↓reduceIte,
          essentialMaximumMagnitudeOn_magnitude value remaining]
        rw [rationalSeparation_zero_of_nonneg
          (rationalSeparation_nonneg (value atom.item) 0)]

/-- Direct rational distributivity of multiplication over `max`, avoiding
the generic ordered-ring instance route through proposition choice. -/
private theorem max_mul_of_nonnegative_direct
    (left right factor : Coordinate) (factorNonnegative : 0 ≤ factor) :
    max (left * factor) (right * factor) =
      max left right * factor := by
  by_cases order : left ≤ right
  · have scaled : left * factor ≤ right * factor :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
        order factorNonnegative
    rw [max_eq_right order, max_eq_right scaled]
  · have reverse : right ≤ left :=
      (RFAP.ConstructiveFraction.lt_of_not_ge_direct order).le
    have scaled : right * factor ≤ left * factor :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
        reverse factorNonnegative
    rw [max_eq_left reverse, max_eq_left scaled]

private theorem essentialMaximumMagnitudeOn_productAtoms {α β : Type}
    (leftValue : α → Coordinate) (rightValue : β → Coordinate) :
    ∀ left : List (Weighted α), ∀ right : List (Weighted β),
    essentialMaximumMagnitudeOn
        (fun pair => leftValue pair.1 * rightValue pair.2)
        (productAtoms left right) =
      essentialMaximumMagnitudeOn leftValue left *
        essentialMaximumMagnitudeOn rightValue right
  | [], right => by
      simp only [productAtoms, essentialMaximumMagnitudeOn, zero_mul]
  | atom :: remaining, right => by
      let rightMaximum := essentialMaximumMagnitudeOn rightValue right
      have rightMaximumNonnegative : 0 ≤ rightMaximum :=
        essentialMaximumMagnitudeOn_nonnegative rightValue right
      rw [productAtoms, essentialMaximumMagnitudeOn_append]
      by_cases atomZero : atom.weight = 0
      · rw [essentialMaximumMagnitudeOn_scaleAtoms_of_eq_zero _ atom.weight
          atom.nonnegative atomZero,
          essentialMaximumMagnitudeOn_productAtoms leftValue rightValue
            remaining right]
        simp only [essentialMaximumMagnitudeOn, atomZero, ↓reduceIte]
        exact max_eq_right
          (RFAP.ConstructiveFraction.mul_nonneg_direct
            (essentialMaximumMagnitudeOn_nonnegative leftValue remaining)
            rightMaximumNonnegative)
      · rw [essentialMaximumMagnitudeOn_scaleAtoms_of_ne _ atom.weight
          atom.nonnegative atomZero,
          essentialMaximumMagnitudeOn_productRow,
          essentialMaximumMagnitudeOn_productAtoms leftValue rightValue
            remaining right]
        simp only [essentialMaximumMagnitudeOn, atomZero, ↓reduceIte]
        exact max_mul_of_nonnegative_direct _ _ _
          rightMaximumNonnegative

namespace FiniteContent

/-- Exact `L∞` tensor-product law for arbitrary displayed finite contents. -/
theorem product_essentialMaximumMagnitude_mul {α β : Type}
    (left : FiniteContent α) (right : FiniteContent β)
    (leftValue : α → Coordinate) (rightValue : β → Coordinate) :
    (left.product right).essentialMaximumMagnitude
        (fun pair => leftValue pair.1 * rightValue pair.2) =
      left.essentialMaximumMagnitude leftValue *
        right.essentialMaximumMagnitude rightValue :=
  essentialMaximumMagnitudeOn_productAtoms leftValue rightValue
    left.atoms right.atoms

end FiniteContent

namespace Distribution

/-- The executable essential maximum of a finite bind is the source
essential maximum of the transition-wise essential maxima. -/
theorem bind_essentialMaximumMagnitude {α β : Type}
    (source : Distribution α) (transition : α → Distribution β)
    (value : β → Coordinate) :
    (source.bind transition).essentialMaximumMagnitude value =
      source.essentialMaximumMagnitude
        (fun item => (transition item).essentialMaximumMagnitude value) := by
  change essentialMaximumMagnitudeOn value
      (bindAtoms source.atoms transition) =
    essentialMaximumMagnitudeOn
      (fun item => essentialMaximumMagnitudeOn value (transition item).atoms)
      source.atoms
  induction source.atoms with
  | nil => rfl
  | cons atom remaining inductionHypothesis =>
      rw [bindAtoms, essentialMaximumMagnitudeOn_append]
      by_cases atomZero : atom.weight = 0
      · rw [essentialMaximumMagnitudeOn_scaleAtoms_of_eq_zero _ atom.weight
          atom.nonnegative atomZero, inductionHypothesis]
        simp only [essentialMaximumMagnitudeOn, atomZero, ↓reduceIte]
        exact max_eq_right
          (essentialMaximumMagnitudeOn_nonnegative
            (fun item => essentialMaximumMagnitudeOn value
              (transition item).atoms) remaining)
      · rw [essentialMaximumMagnitudeOn_scaleAtoms_of_ne _ atom.weight
          atom.nonnegative atomZero, inductionHypothesis]
        simp only [essentialMaximumMagnitudeOn, atomZero, ↓reduceIte]
        rw [rationalSeparation_zero_of_nonneg
          (essentialMaximumMagnitudeOn_nonnegative value
            (transition atom.item).atoms)]

/-- Essential-maximum distance through a finite bind is the source
essential maximum of the transition-wise distances. -/
theorem bind_essentialMaximumDistance {α β : Type}
    (source : Distribution α) (transition : α → Distribution β)
    (left right : β → Coordinate) :
    (source.bind transition).essentialMaximumDistance left right =
      source.essentialMaximumMagnitude (fun item =>
        (transition item).essentialMaximumDistance left right) := by
  unfold essentialMaximumDistance
  exact source.bind_essentialMaximumMagnitude transition
    (fun item => left item - right item)

private theorem essentialMaximumMagnitude_magnitude {α : Type}
    (distribution : Distribution α) (value : α → Coordinate) :
    distribution.essentialMaximumMagnitude
        (fun item => rationalSeparation (value item) 0) =
      distribution.essentialMaximumMagnitude value :=
  essentialMaximumMagnitudeOn_magnitude value distribution.atoms

/-- Exact executable essential-maximum tensor-product law for normalized
finite distributions. -/
theorem product_essentialMaximumMagnitude_mul {α β : Type}
    (left : Distribution α) (right : Distribution β)
    (leftValue : α → Coordinate) (rightValue : β → Coordinate) :
    (left.product right).essentialMaximumMagnitude
        (fun pair => leftValue pair.1 * rightValue pair.2) =
      left.essentialMaximumMagnitude leftValue *
        right.essentialMaximumMagnitude rightValue := by
  unfold Distribution.product
  rw [left.bind_essentialMaximumMagnitude]
  let rightMaximum := right.essentialMaximumMagnitude rightValue
  have rightMaximumNonnegative : 0 ≤ rightMaximum :=
    right.essentialMaximumMagnitude_nonnegative rightValue
  calc
    left.essentialMaximumMagnitude (fun leftItem =>
          (right.map fun rightItem => (leftItem, rightItem))
            |>.essentialMaximumMagnitude
              (fun pair => leftValue pair.1 * rightValue pair.2)) =
        left.essentialMaximumMagnitude (fun leftItem =>
          rationalSeparation (leftValue leftItem) 0 * rightMaximum) :=
      left.essentialMaximumMagnitude_congr _ _ (fun leftItem => by
        rw [right.map_essentialMaximumMagnitude]
        exact right.essentialMaximumMagnitude_scale
          (leftValue leftItem) rightValue)
    left.essentialMaximumMagnitude (fun leftItem =>
          rationalSeparation (leftValue leftItem) 0 * rightMaximum) =
        left.essentialMaximumMagnitude (fun leftItem =>
          rightMaximum * rationalSeparation (leftValue leftItem) 0) := by
      exact left.essentialMaximumMagnitude_congr _ _
        (fun leftItem => by ring1)
    _ = rationalSeparation rightMaximum 0 *
          left.essentialMaximumMagnitude (fun leftItem =>
            rationalSeparation (leftValue leftItem) 0) :=
      left.essentialMaximumMagnitude_scale rightMaximum _
    _ = rightMaximum * left.essentialMaximumMagnitude leftValue := by
      rw [rationalSeparation_zero_of_nonneg rightMaximumNonnegative,
        left.essentialMaximumMagnitude_magnitude leftValue]
    _ = left.essentialMaximumMagnitude leftValue * rightMaximum := by ring1

/-- Pullback from the left coordinate preserves the executable essential
maximum on a normalized finite product. -/
theorem product_essentialMaximumMagnitude_left {α β : Type}
    (left : Distribution α) (right : Distribution β)
    (value : α → Coordinate) :
    (left.product right).essentialMaximumMagnitude
        (fun pair => value pair.1) =
      left.essentialMaximumMagnitude value := by
  calc
    (left.product right).essentialMaximumMagnitude
          (fun pair => value pair.1) =
        (left.product right).essentialMaximumMagnitude
          (fun pair => value pair.1 * 1) := by
      exact (left.product right).essentialMaximumMagnitude_congr _ _
        (fun pair => by ring1)
    _ = left.essentialMaximumMagnitude value *
          right.essentialMaximumMagnitude (fun _ => 1) :=
      left.product_essentialMaximumMagnitude_mul right value (fun _ => 1)
    _ = left.essentialMaximumMagnitude value := by
      rw [right.essentialMaximumMagnitude_constant,
        show rationalSeparation 1 0 = 1 by decide, mul_one]

/-- Symmetric right-coordinate preservation law. -/
theorem product_essentialMaximumMagnitude_right {α β : Type}
    (left : Distribution α) (right : Distribution β)
    (value : β → Coordinate) :
    (left.product right).essentialMaximumMagnitude
        (fun pair => value pair.2) =
      right.essentialMaximumMagnitude value := by
  calc
    (left.product right).essentialMaximumMagnitude
          (fun pair => value pair.2) =
        (left.product right).essentialMaximumMagnitude
          (fun pair => 1 * value pair.2) := by
      exact (left.product right).essentialMaximumMagnitude_congr _ _
        (fun pair => by ring1)
    _ = left.essentialMaximumMagnitude (fun _ => 1) *
          right.essentialMaximumMagnitude value :=
      left.product_essentialMaximumMagnitude_mul right (fun _ => 1) value
    _ = right.essentialMaximumMagnitude value := by
      rw [left.essentialMaximumMagnitude_constant,
        show rationalSeparation 1 0 = 1 by decide, one_mul]

theorem product_essentialMaximumDistance_left {α β : Type}
    (left : Distribution α) (right : Distribution β)
    (first second : α → Coordinate) :
    (left.product right).essentialMaximumDistance
        (fun pair => first pair.1) (fun pair => second pair.1) =
      left.essentialMaximumDistance first second := by
  unfold essentialMaximumDistance
  exact left.product_essentialMaximumMagnitude_left right
    (fun item => first item - second item)

theorem product_essentialMaximumDistance_right {α β : Type}
    (left : Distribution α) (right : Distribution β)
    (first second : β → Coordinate) :
    (left.product right).essentialMaximumDistance
        (fun pair => first pair.2) (fun pair => second pair.2) =
      right.essentialMaximumDistance first second := by
  unfold essentialMaximumDistance
  exact left.product_essentialMaximumMagnitude_right right
    (fun item => first item - second item)

end Distribution

end FiniteMeasure
