import mathlib.Tactic.QuotientFreeRing
import FiniteMeasure.EssentialBound

/-!
# Executable finite essential maxima

On a displayed finite atom table, every rational observable has a computed
least essential magnitude bound: recursively ignore zero-weight rows and
take the rational maximum on the rest.  Thus no supremum, infimum, or
completed line is needed.  The construction also gives an explicit uniform
absolute-continuity bound for restricted integrals.
-/

namespace FiniteMeasure

/-- Exact maximum rational magnitude over the displayed nonzero-weight
rows. -/
def essentialMaximumMagnitudeOn {α : Type}
    (value : α → Coordinate) : List (Weighted α) → Coordinate
  | [] => 0
  | atom :: remaining =>
      if atom.weight = 0 then essentialMaximumMagnitudeOn value remaining
      else max (rationalSeparation (value atom.item) 0)
        (essentialMaximumMagnitudeOn value remaining)

/-- Pointwise-equal observables have the same computed maximum on every
displayed finite atom list. -/
theorem essentialMaximumMagnitudeOn_congr {α : Type}
    (atoms : List (Weighted α)) (left right : α → Coordinate)
    (pointwise : ∀ item, left item = right item) :
    essentialMaximumMagnitudeOn left atoms =
      essentialMaximumMagnitudeOn right atoms := by
  induction atoms with
  | nil => rfl
  | cons atom remaining inductionHypothesis =>
      simp only [essentialMaximumMagnitudeOn, pointwise atom.item,
        inductionHypothesis]

theorem essentialMaximumMagnitudeOn_nonnegative {α : Type}
    (value : α → Coordinate) :
    ∀ atoms : List (Weighted α),
      0 ≤ essentialMaximumMagnitudeOn value atoms
  | [] => le_rfl
  | atom :: remaining => by
      by_cases zero : atom.weight = 0
      · simp only [essentialMaximumMagnitudeOn, zero, ↓reduceIte]
        exact essentialMaximumMagnitudeOn_nonnegative value remaining
      · simp only [essentialMaximumMagnitudeOn, zero, ↓reduceIte]
        exact le_max_of_le_right
          (essentialMaximumMagnitudeOn_nonnegative value remaining)

/-- Every displayed row is either null or bounded by the computed essential
maximum. -/
theorem essentiallyBoundedByOn_essentialMaximumMagnitudeOn {α : Type}
    (value : α → Coordinate) :
    ∀ atoms : List (Weighted α),
      EssentiallyBoundedByOn atoms value
        (essentialMaximumMagnitudeOn value atoms)
  | [] => by
      intro atom member
      cases member
  | atom :: remaining => by
      intro candidate member
      rcases List.mem_cons.mp member with same | tail
      · subst candidate
        by_cases zero : atom.weight = 0
        · exact Or.inl zero
        · apply Or.inr
          simp only [essentialMaximumMagnitudeOn, zero, ↓reduceIte]
          exact le_max_left _ _
      · rcases essentiallyBoundedByOn_essentialMaximumMagnitudeOn value
          remaining candidate tail with zero | bound
        · exact Or.inl zero
        · apply Or.inr
          by_cases headZero : atom.weight = 0
          · simpa only [essentialMaximumMagnitudeOn, headZero, ↓reduceIte]
              using bound
          · simp only [essentialMaximumMagnitudeOn, headZero, ↓reduceIte]
            exact bound.trans (le_max_right _ _)

/-- The computed maximum is below every other nonnegative essential bound. -/
theorem essentialMaximumMagnitudeOn_le {α : Type}
    (value : α → Coordinate) (ceiling : Coordinate)
    (ceilingNonnegative : 0 ≤ ceiling) :
    ∀ atoms : List (Weighted α),
      EssentiallyBoundedByOn atoms value ceiling →
        essentialMaximumMagnitudeOn value atoms ≤ ceiling
  | [], bounded => ceilingNonnegative
  | atom :: remaining, bounded => by
      have tailBounded : EssentiallyBoundedByOn remaining value ceiling :=
        fun candidate member =>
          bounded candidate (List.mem_cons_of_mem atom member)
      have tailLe := essentialMaximumMagnitudeOn_le value ceiling
        ceilingNonnegative remaining tailBounded
      by_cases zero : atom.weight = 0
      · simpa only [essentialMaximumMagnitudeOn, zero, ↓reduceIte]
          using tailLe
      · have headLe : rationalSeparation (value atom.item) 0 ≤ ceiling := by
          rcases bounded atom List.mem_cons_self with impossible | bound
          · exact (zero impossible).elim
          · exact bound
        simp only [essentialMaximumMagnitudeOn, zero, ↓reduceIte]
        exact max_le headLe tailLe

namespace FiniteContent

/-- Computed least essential magnitude bound of a finite-content
observable. -/
def essentialMaximumMagnitude {α : Type} (content : FiniteContent α)
    (value : α → Coordinate) : Coordinate :=
  essentialMaximumMagnitudeOn value content.atoms

/-- Pointwise equality suffices for equality of computed finite essential
maxima. -/
theorem essentialMaximumMagnitude_congr {α : Type}
    (content : FiniteContent α) (left right : α → Coordinate)
    (pointwise : ∀ item, left item = right item) :
    content.essentialMaximumMagnitude left =
      content.essentialMaximumMagnitude right :=
  essentialMaximumMagnitudeOn_congr content.atoms left right pointwise

theorem essentialMaximumMagnitude_nonnegative {α : Type}
    (content : FiniteContent α) (value : α → Coordinate) :
    0 ≤ content.essentialMaximumMagnitude value :=
  essentialMaximumMagnitudeOn_nonnegative value content.atoms

theorem essentiallyBoundedBy_essentialMaximumMagnitude {α : Type}
    (content : FiniteContent α) (value : α → Coordinate) :
    content.EssentiallyBoundedBy value
      (content.essentialMaximumMagnitude value) :=
  essentiallyBoundedByOn_essentialMaximumMagnitudeOn value content.atoms

theorem essentialMaximumMagnitude_le {α : Type}
    (content : FiniteContent α) (value : α → Coordinate)
    (ceiling : Coordinate) (ceilingNonnegative : 0 ≤ ceiling)
    (bounded : content.EssentiallyBoundedBy value ceiling) :
    content.essentialMaximumMagnitude value ≤ ceiling :=
  essentialMaximumMagnitudeOn_le value ceiling ceilingNonnegative
    content.atoms bounded

/-- Almost-everywhere equal observables have the same computed finite
essential maximum. -/
theorem essentialMaximumMagnitude_congr_almostEverywhere {α : Type}
    (content : FiniteContent α) (left right : α → Coordinate)
    (equal : content.EqualAlmostEverywhere left right) :
    content.essentialMaximumMagnitude left =
      content.essentialMaximumMagnitude right := by
  apply RFAP.ConstructiveFraction.le_antisymm
  · apply content.essentialMaximumMagnitude_le left
      (content.essentialMaximumMagnitude right)
      (content.essentialMaximumMagnitude_nonnegative right)
    exact content.essentiallyBoundedBy_congr_almostEverywhere equal.symm
      (content.essentiallyBoundedBy_essentialMaximumMagnitude right)
  · apply content.essentialMaximumMagnitude_le right
      (content.essentialMaximumMagnitude left)
      (content.essentialMaximumMagnitude_nonnegative left)
    exact content.essentiallyBoundedBy_congr_almostEverywhere equal
      (content.essentiallyBoundedBy_essentialMaximumMagnitude left)

theorem essentialMaximumMagnitude_zero {α : Type}
    (content : FiniteContent α) :
    content.essentialMaximumMagnitude (fun _ => 0) = 0 := by
  apply RFAP.ConstructiveFraction.le_antisymm
  · exact content.essentialMaximumMagnitude_le (fun _ => 0) 0 le_rfl
      content.essentiallyBoundedBy_zero
  · exact content.essentialMaximumMagnitude_nonnegative (fun _ => 0)

/-- A finite content's computed maximum of a constant is at most its exact
rational magnitude.  Equality need not hold when every displayed row has
zero weight. -/
theorem essentialMaximumMagnitude_constant_le {α : Type}
    (content : FiniteContent α) (constant : Coordinate) :
    content.essentialMaximumMagnitude (fun _ => constant) ≤
      rationalSeparation constant 0 := by
  exact content.essentialMaximumMagnitude_le (fun _ => constant)
    (rationalSeparation constant 0) (rationalSeparation_nonneg _ _)
    (content.essentiallyBoundedBy_constant constant)

/-- Definiteness modulo the displayed zero-weight rows: the computed finite
essential maximum vanishes exactly when the observable is zero almost
everywhere in the finite sense. -/
theorem essentialMaximumMagnitude_eq_zero_iff {α : Type}
    (content : FiniteContent α) (value : α → Coordinate) :
    content.essentialMaximumMagnitude value = 0 ↔
      content.EqualAlmostEverywhere value (fun _ => 0) := by
  constructor
  · intro maximumZero atom member
    rcases content.essentiallyBoundedBy_essentialMaximumMagnitude value
        atom member with zero | bound
    · exact Or.inl zero
    · apply Or.inr
      apply (rationalSeparation_eq_zero_iff (value atom.item) 0).mp
      exact RFAP.ConstructiveFraction.le_antisymm _ _
        (bound.trans_eq maximumZero) (rationalSeparation_nonneg _ _)
  · intro equal
    calc
      content.essentialMaximumMagnitude value =
          content.essentialMaximumMagnitude (fun _ => 0) :=
        content.essentialMaximumMagnitude_congr_almostEverywhere
          value (fun _ => 0) equal
      _ = 0 := content.essentialMaximumMagnitude_zero

/-- The computed finite essential maximum is subadditive. -/
theorem essentialMaximumMagnitude_add_le {α : Type}
    (content : FiniteContent α) (left right : α → Coordinate) :
    content.essentialMaximumMagnitude (fun item => left item + right item) ≤
      content.essentialMaximumMagnitude left +
        content.essentialMaximumMagnitude right := by
  apply content.essentialMaximumMagnitude_le
  · exact add_nonneg
      (content.essentialMaximumMagnitude_nonnegative left)
      (content.essentialMaximumMagnitude_nonnegative right)
  · exact content.essentiallyBoundedBy_add left right
      (content.essentialMaximumMagnitude left)
      (content.essentialMaximumMagnitude right)
      (content.essentiallyBoundedBy_essentialMaximumMagnitude left)
      (content.essentiallyBoundedBy_essentialMaximumMagnitude right)

/-- Scaling by a displayed rational scales the computed essential maximum
by at most the rational magnitude of that factor. -/
theorem essentialMaximumMagnitude_scale_le {α : Type}
    (content : FiniteContent α) (factor : Coordinate)
    (value : α → Coordinate) :
    content.essentialMaximumMagnitude (fun item => factor * value item) ≤
      rationalSeparation factor 0 *
        content.essentialMaximumMagnitude value := by
  apply content.essentialMaximumMagnitude_le
  · exact RFAP.ConstructiveFraction.mul_nonneg_direct
      (rationalSeparation_nonneg _ _)
      (content.essentialMaximumMagnitude_nonnegative value)
  · exact content.essentiallyBoundedBy_scale factor value
      (content.essentialMaximumMagnitude value)
      (content.essentiallyBoundedBy_essentialMaximumMagnitude value)

/-- Exact homogeneity of the computed finite essential maximum.  The proof
separates the zero factor and otherwise uses its explicit rational inverse;
no supremum or choice principle is involved. -/
theorem essentialMaximumMagnitude_scale {α : Type}
    (content : FiniteContent α) (factor : Coordinate)
    (value : α → Coordinate) :
    content.essentialMaximumMagnitude (fun item => factor * value item) =
      rationalSeparation factor 0 *
        content.essentialMaximumMagnitude value := by
  by_cases factorZero : factor = 0
  · subst factor
    calc
      content.essentialMaximumMagnitude (fun item => 0 * value item) =
          content.essentialMaximumMagnitude (fun _ => 0) :=
        content.essentialMaximumMagnitude_congr _ _ (fun item =>
          zero_mul (value item))
      _ = 0 := content.essentialMaximumMagnitude_zero
      _ = rationalSeparation 0 0 *
            content.essentialMaximumMagnitude value := by
        simp only [rationalSeparation, sub_self, max_self, zero_mul]
  · apply RFAP.ConstructiveFraction.le_antisymm
    · exact content.essentialMaximumMagnitude_scale_le factor value
    · let scaledValue := fun item => factor * value item
      have inverseBound := content.essentialMaximumMagnitude_scale_le
        factor⁻¹ scaledValue
      have restored : content.essentialMaximumMagnitude
          (fun item => factor⁻¹ * scaledValue item) =
          content.essentialMaximumMagnitude value :=
        content.essentialMaximumMagnitude_congr _ _ (fun item => by
          dsimp only [scaledValue]
          calc
            factor⁻¹ * (factor * value item) =
                (factor⁻¹ * factor) * value item := by
              rw [mul_assoc]
            _ = value item := by
              rw [RFAP.ConstructiveFraction.inv_mul_cancel factor factorZero,
                one_mul])
      rw [restored] at inverseBound
      have multiplied :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          inverseBound (rationalSeparation_nonneg factor 0)
      have magnitudesCancel :
          rationalSeparation factor 0 *
              rationalSeparation factor⁻¹ 0 = 1 := by
        rw [← rationalSeparation_mul_zero,
          RFAP.ConstructiveFraction.mul_inv_cancel factor factorZero]
        decide
      calc
        rationalSeparation factor 0 *
              content.essentialMaximumMagnitude value ≤
            rationalSeparation factor 0 *
              (rationalSeparation factor⁻¹ 0 *
                content.essentialMaximumMagnitude scaledValue) := multiplied
        _ = (rationalSeparation factor 0 *
              rationalSeparation factor⁻¹ 0) *
                content.essentialMaximumMagnitude scaledValue := by
          rw [mul_assoc]
        _ = content.essentialMaximumMagnitude scaledValue := by
          rw [magnitudesCancel, one_mul]

/-- Negation preserves the computed finite essential maximum exactly. -/
theorem essentialMaximumMagnitude_neg {α : Type}
    (content : FiniteContent α) (value : α → Coordinate) :
    content.essentialMaximumMagnitude (fun item => -value item) =
      content.essentialMaximumMagnitude value := by
  apply RFAP.ConstructiveFraction.le_antisymm
  · apply content.essentialMaximumMagnitude_le
    · exact content.essentialMaximumMagnitude_nonnegative value
    · exact content.essentiallyBoundedBy_neg value
        (content.essentialMaximumMagnitude value)
        (content.essentiallyBoundedBy_essentialMaximumMagnitude value)
  · apply content.essentialMaximumMagnitude_le
    · exact content.essentialMaximumMagnitude_nonnegative
        (fun item => -value item)
    · have doubleNegated := content.essentiallyBoundedBy_neg
          (fun item => -value item)
          (content.essentialMaximumMagnitude (fun item => -value item))
          (content.essentiallyBoundedBy_essentialMaximumMagnitude
            (fun item => -value item))
      intro atom member
      rcases doubleNegated atom member with zero | bound
      · exact Or.inl zero
      · apply Or.inr
        change rationalSeparation (value atom.item) 0 ≤
          content.essentialMaximumMagnitude (fun item => -value item)
        change rationalSeparation (- -value atom.item) 0 ≤
          content.essentialMaximumMagnitude (fun item => -value item) at bound
        rw [neg_neg] at bound
        exact bound

/-- The usual subtraction triangle inequality for the computed finite
essential maximum. -/
theorem essentialMaximumMagnitude_sub_le {α : Type}
    (content : FiniteContent α) (left right : α → Coordinate) :
    content.essentialMaximumMagnitude (fun item => left item - right item) ≤
      content.essentialMaximumMagnitude left +
        content.essentialMaximumMagnitude right := by
  apply content.essentialMaximumMagnitude_le
  · exact add_nonneg
      (content.essentialMaximumMagnitude_nonnegative left)
      (content.essentialMaximumMagnitude_nonnegative right)
  · exact content.essentiallyBoundedBy_sub left right
      (content.essentialMaximumMagnitude left)
      (content.essentialMaximumMagnitude right)
      (content.essentiallyBoundedBy_essentialMaximumMagnitude left)
      (content.essentiallyBoundedBy_essentialMaximumMagnitude right)

/-- Products satisfy the finite essential-maximum algebra bound. -/
theorem essentialMaximumMagnitude_mul_le {α : Type}
    (content : FiniteContent α) (left right : α → Coordinate) :
    content.essentialMaximumMagnitude (fun item => left item * right item) ≤
      content.essentialMaximumMagnitude left *
        content.essentialMaximumMagnitude right := by
  apply content.essentialMaximumMagnitude_le
  · exact RFAP.ConstructiveFraction.mul_nonneg_direct
      (content.essentialMaximumMagnitude_nonnegative left)
      (content.essentialMaximumMagnitude_nonnegative right)
  · exact content.essentiallyBoundedBy_mul left right
      (content.essentialMaximumMagnitude left)
      (content.essentialMaximumMagnitude right)
      (content.essentiallyBoundedBy_essentialMaximumMagnitude left)
      (content.essentiallyBoundedBy_essentialMaximumMagnitude right)

/-! ## Executable finite essential-maximum distance -/

/-- Root-free finite `L∞` distance: the computed essential maximum of the
explicit pointwise difference. -/
def essentialMaximumDistance {α : Type} (content : FiniteContent α)
    (left right : α → Coordinate) : Coordinate :=
  content.essentialMaximumMagnitude fun item => left item - right item

theorem essentialMaximumDistance_nonnegative {α : Type}
    (content : FiniteContent α) (left right : α → Coordinate) :
    0 ≤ content.essentialMaximumDistance left right :=
  content.essentialMaximumMagnitude_nonnegative _

theorem essentialMaximumDistance_refl {α : Type}
    (content : FiniteContent α) (value : α → Coordinate) :
    content.essentialMaximumDistance value value = 0 := by
  unfold essentialMaximumDistance
  calc
    content.essentialMaximumMagnitude (fun item => value item - value item) =
        content.essentialMaximumMagnitude (fun _ => (0 : Coordinate)) :=
      content.essentialMaximumMagnitude_congr _ _ (fun item => by ring1)
    _ = 0 := content.essentialMaximumMagnitude_zero

theorem essentialMaximumDistance_symm {α : Type}
    (content : FiniteContent α) (left right : α → Coordinate) :
    content.essentialMaximumDistance left right =
      content.essentialMaximumDistance right left := by
  unfold essentialMaximumDistance
  have negated := content.essentialMaximumMagnitude_neg
    (fun item => left item - right item)
  have same : content.essentialMaximumMagnitude
      (fun item => -(left item - right item)) =
      content.essentialMaximumMagnitude
        (fun item => right item - left item) :=
    content.essentialMaximumMagnitude_congr _ _ (fun item => by ring1)
  rw [same] at negated
  exact negated.symm

theorem essentialMaximumDistance_triangle {α : Type}
    (content : FiniteContent α)
    (left middle right : α → Coordinate) :
    content.essentialMaximumDistance left right ≤
      content.essentialMaximumDistance left middle +
        content.essentialMaximumDistance middle right := by
  have bound := content.essentialMaximumMagnitude_add_le
    (fun item => left item - middle item)
    (fun item => middle item - right item)
  have same : content.essentialMaximumMagnitude (fun item =>
      (left item - middle item) + (middle item - right item)) =
      content.essentialMaximumMagnitude
        (fun item => left item - right item) :=
    content.essentialMaximumMagnitude_congr _ _ (fun item => by ring1)
  rw [same] at bound
  exact bound

/-- Reverse triangle inequality for the executable finite essential-maximum
distance. -/
theorem essentialMaximumDistance_reverse_triangle {α : Type}
    (content : FiniteContent α)
    (first second anchor : α → Coordinate) :
    rationalSeparation (content.essentialMaximumDistance first anchor)
        (content.essentialMaximumDistance second anchor) ≤
      content.essentialMaximumDistance first second := by
  unfold rationalSeparation
  apply max_le
  · apply (sub_le_iff_le_add).2
    exact content.essentialMaximumDistance_triangle first second anchor
  · apply (sub_le_iff_le_add).2
    calc
      content.essentialMaximumDistance second anchor ≤
          content.essentialMaximumDistance second first +
            content.essentialMaximumDistance first anchor :=
        content.essentialMaximumDistance_triangle second first anchor
      _ = content.essentialMaximumDistance first second +
            content.essentialMaximumDistance first anchor := by
        rw [content.essentialMaximumDistance_symm second first]

/-- The computed essential magnitude is distance from the zero observable. -/
theorem essentialMaximumMagnitude_eq_distance_zero {α : Type}
    (content : FiniteContent α) (value : α → Coordinate) :
    content.essentialMaximumMagnitude value =
      content.essentialMaximumDistance value (fun _ => 0) := by
  unfold essentialMaximumDistance
  exact content.essentialMaximumMagnitude_congr _ _ (fun item => by ring1)

/-- Reverse triangle stability of computed finite essential magnitudes. -/
theorem essentialMaximumMagnitude_separation_le_distance {α : Type}
    (content : FiniteContent α) (left right : α → Coordinate) :
    rationalSeparation (content.essentialMaximumMagnitude left)
        (content.essentialMaximumMagnitude right) ≤
      content.essentialMaximumDistance left right := by
  rw [content.essentialMaximumMagnitude_eq_distance_zero,
    content.essentialMaximumMagnitude_eq_distance_zero]
  exact content.essentialMaximumDistance_reverse_triangle
    left right (fun _ => 0)

/-- The finite essential-maximum distance separates observables precisely
up to equality on all displayed nonzero-weight rows. -/
theorem essentialMaximumDistance_eq_zero_iff {α : Type}
    (content : FiniteContent α) (left right : α → Coordinate) :
    content.essentialMaximumDistance left right = 0 ↔
      content.EqualAlmostEverywhere left right := by
  unfold essentialMaximumDistance
  constructor
  · intro zero
    have differenceZero :=
      (content.essentialMaximumMagnitude_eq_zero_iff
        (fun item => left item - right item)).mp zero
    intro atom member
    rcases differenceZero atom member with weightZero | same
    · exact Or.inl weightZero
    · apply Or.inr
      apply sub_eq_zero.mp
      exact same
  · intro equal
    apply (content.essentialMaximumMagnitude_eq_zero_iff
      (fun item => left item - right item)).mpr
    intro atom member
    rcases equal atom member with weightZero | same
    · exact Or.inl weightZero
    · apply Or.inr
      change left atom.item - right atom.item = 0
      rw [same, sub_self]

/-- Exact homogeneity of finite essential-maximum distance. -/
theorem essentialMaximumDistance_scale {α : Type}
    (content : FiniteContent α) (factor : Coordinate)
    (left right : α → Coordinate) :
    content.essentialMaximumDistance
        (fun item => factor * left item)
        (fun item => factor * right item) =
      rationalSeparation factor 0 *
        content.essentialMaximumDistance left right := by
  unfold essentialMaximumDistance
  have same : content.essentialMaximumMagnitude
      (fun item => factor * left item - factor * right item) =
      content.essentialMaximumMagnitude
        (fun item => factor * (left item - right item)) :=
    content.essentialMaximumMagnitude_congr _ _ (fun item => by ring1)
  rw [same, content.essentialMaximumMagnitude_scale]

private theorem poweredL1_indicator {α : Type}
    (content : FiniteContent α) (event : α → Bool) :
    content.poweredL1 (Distribution.indicator event) =
      content.measure event := by
  unfold poweredL1
  calc
    content.integral (fun item =>
        rationalSeparation (Distribution.indicator event item) 0) =
        content.integral (Distribution.indicator event) :=
      content.integral_congr _ _ (fun item => by
        cases selected : event item
        · simp only [Distribution.indicator, selected, rationalSeparation,
            sub_self, max_self]
        · simp only [Distribution.indicator, selected, rationalSeparation,
            sub_zero, zero_sub]
          decide)
    _ = content.measure event := content.integral_indicator event

/-- Explicit finite uniform absolute continuity of integration: the L1 mass
of an observable restricted to an event is bounded by its computed essential
maximum times the event content. -/
theorem poweredL1_indicator_mul_le_essentialMaximum_mul_measure {α : Type}
    (content : FiniteContent α) (event : α → Bool)
    (value : α → Coordinate) :
    content.poweredL1 (fun item =>
        Distribution.indicator event item * value item) ≤
      content.essentialMaximumMagnitude value * content.measure event := by
  have bound := content.poweredL1_mul_le_of_right_essentialBound
    (Distribution.indicator event) value
    (content.essentialMaximumMagnitude value)
    (content.essentiallyBoundedBy_essentialMaximumMagnitude value)
  rw [content.poweredL1_indicator event] at bound
  exact bound

/-- Finite L1--L∞ Hölder inequality using the computed essential maximum
of the right factor. -/
theorem poweredL1_mul_le_essentialMaximum_right {α : Type}
    (content : FiniteContent α) (left right : α → Coordinate) :
    content.poweredL1 (fun item => left item * right item) ≤
      content.essentialMaximumMagnitude right * content.poweredL1 left :=
  content.poweredL1_mul_le_of_right_essentialBound left right
    (content.essentialMaximumMagnitude right)
    (content.essentiallyBoundedBy_essentialMaximumMagnitude right)

/-- Symmetric finite L∞--L1 Hölder inequality. -/
theorem poweredL1_mul_le_essentialMaximum_left {α : Type}
    (content : FiniteContent α) (left right : α → Coordinate) :
    content.poweredL1 (fun item => left item * right item) ≤
      content.essentialMaximumMagnitude left * content.poweredL1 right := by
  have bound := content.poweredL1_mul_le_essentialMaximum_right right left
  have commuted : content.poweredL1 (fun item => right item * left item) =
      content.poweredL1 (fun item => left item * right item) :=
    content.poweredL1_congr _ _ (fun item => by ring1)
  rw [commuted] at bound
  exact bound

/-- Product perturbation estimate in finite L1. -/
theorem l1Distance_mul_le {α : Type} (content : FiniteContent α)
    (leftFirst leftSecond rightFirst rightSecond : α → Coordinate) :
    content.l1Distance
        (fun item => leftFirst item * rightFirst item)
        (fun item => leftSecond item * rightSecond item) ≤
      content.essentialMaximumMagnitude rightFirst *
          content.l1Distance leftFirst leftSecond +
        content.essentialMaximumMagnitude leftSecond *
          content.l1Distance rightFirst rightSecond := by
  calc
    content.l1Distance
          (fun item => leftFirst item * rightFirst item)
          (fun item => leftSecond item * rightSecond item) =
        content.poweredL1 (fun item =>
          leftFirst item * rightFirst item -
            leftSecond item * rightSecond item) :=
      (content.poweredL1_sub_eq_l1Distance
        (fun item => leftFirst item * rightFirst item)
        (fun item => leftSecond item * rightSecond item)).symm
    _ = content.poweredL1 (fun item =>
          (leftFirst item - leftSecond item) * rightFirst item +
            leftSecond item *
              (rightFirst item - rightSecond item)) :=
      content.poweredL1_congr _ _ (fun item => by ring1)
    _ ≤ content.poweredL1 (fun item =>
          (leftFirst item - leftSecond item) * rightFirst item) +
        content.poweredL1 (fun item =>
          leftSecond item * (rightFirst item - rightSecond item)) :=
      content.poweredL1_add_le _ _
    _ ≤ content.essentialMaximumMagnitude rightFirst *
          content.poweredL1 (fun item =>
            leftFirst item - leftSecond item) +
        content.essentialMaximumMagnitude leftSecond *
          content.poweredL1 (fun item =>
            rightFirst item - rightSecond item) :=
      add_le_add
        (content.poweredL1_mul_le_essentialMaximum_right _ rightFirst)
        (content.poweredL1_mul_le_essentialMaximum_left leftSecond _)
    _ = content.essentialMaximumMagnitude rightFirst *
          content.l1Distance leftFirst leftSecond +
        content.essentialMaximumMagnitude leftSecond *
          content.l1Distance rightFirst rightSecond := by
      rw [content.poweredL1_sub_eq_l1Distance,
        content.poweredL1_sub_eq_l1Distance]

/-- Multiplication by one fixed essentially bounded right factor is
L1-Lipschitz with its computed essential maximum. -/
theorem l1Distance_mul_right_le {α : Type} (content : FiniteContent α)
    (leftFirst leftSecond right : α → Coordinate) :
    content.l1Distance
        (fun item => leftFirst item * right item)
        (fun item => leftSecond item * right item) ≤
      content.essentialMaximumMagnitude right *
        content.l1Distance leftFirst leftSecond := by
  have bound := content.l1Distance_mul_le
    leftFirst leftSecond right right
  rw [content.l1Distance_refl, mul_zero, add_zero] at bound
  exact bound

/-- Symmetric fixed-left-factor L1 Lipschitz estimate. -/
theorem l1Distance_mul_left_le {α : Type} (content : FiniteContent α)
    (left rightFirst rightSecond : α → Coordinate) :
    content.l1Distance
        (fun item => left item * rightFirst item)
        (fun item => left item * rightSecond item) ≤
      content.essentialMaximumMagnitude left *
        content.l1Distance rightFirst rightSecond := by
  have bound := content.l1Distance_mul_le
    left left rightFirst rightSecond
  rw [content.l1Distance_refl, mul_zero, zero_add] at bound
  exact bound

/-- Every natural-powered finite quantity is controlled by the computed
least essential maximum. -/
theorem poweredLp_le_essentialMaximum {α : Type}
    (content : FiniteContent α) (exponent : Nat)
    (value : α → Coordinate) :
    content.poweredLp exponent value ≤
      content.total * content.essentialMaximumMagnitude value ^ exponent :=
  content.poweredLp_le_of_essentialBound exponent value
    (content.essentialMaximumMagnitude value)
    (content.essentiallyBoundedBy_essentialMaximumMagnitude value)

/-- Every natural-powered finite distance is controlled by the displayed
mass times the matching power of essential-maximum distance. -/
theorem poweredLpDistance_le_essentialMaximumDistance {α : Type}
    (content : FiniteContent α) (exponent : Nat)
    (left right : α → Coordinate) :
    content.poweredLpDistance exponent left right ≤
      content.total *
        content.essentialMaximumDistance left right ^ exponent := by
  have bound := content.poweredLp_le_essentialMaximum exponent
    (fun item => left item - right item)
  rw [content.poweredLp_sub_eq_poweredLpDistance exponent left right]
    at bound
  exact bound

theorem l1Distance_le_total_mul_essentialMaximumDistance {α : Type}
    (content : FiniteContent α) (left right : α → Coordinate) :
    content.l1Distance left right ≤
      content.total * content.essentialMaximumDistance left right := by
  have bound := content.poweredLpDistance_le_essentialMaximumDistance
    1 left right
  rw [content.poweredLpDistance_one, pow_one] at bound
  exact bound

/-- Exact finite integration is Lipschitz from essential-maximum distance,
with the displayed total mass as its operator factor. -/
theorem integral_separation_le_total_mul_essentialMaximumDistance {α : Type}
    (content : FiniteContent α) (left right : α → Coordinate) :
    rationalSeparation (content.integral left) (content.integral right) ≤
      content.total * content.essentialMaximumDistance left right :=
  (content.integral_separation_le_l1Distance left right).trans
    (content.l1Distance_le_total_mul_essentialMaximumDistance left right)

theorem poweredL2Distance_le_total_mul_essentialMaximumDistance_sq
    {α : Type} (content : FiniteContent α)
    (left right : α → Coordinate) :
    content.poweredL2Distance left right ≤
      content.total * content.essentialMaximumDistance left right ^ 2 := by
  have bound := content.poweredLpDistance_le_essentialMaximumDistance
    2 left right
  rw [content.poweredLpDistance_two] at bound
  exact bound

end FiniteContent

namespace Distribution

def essentialMaximumMagnitude {α : Type} (distribution : Distribution α)
    (value : α → Coordinate) : Coordinate :=
  distribution.toFiniteContent.essentialMaximumMagnitude value

/-- Pointwise equality suffices for equality of computed finite essential
maxima under a normalized distribution. -/
theorem essentialMaximumMagnitude_congr {α : Type}
    (distribution : Distribution α) (left right : α → Coordinate)
    (pointwise : ∀ item, left item = right item) :
    distribution.essentialMaximumMagnitude left =
      distribution.essentialMaximumMagnitude right :=
  distribution.toFiniteContent.essentialMaximumMagnitude_congr
    left right pointwise

theorem essentialMaximumMagnitude_nonnegative {α : Type}
    (distribution : Distribution α) (value : α → Coordinate) :
    0 ≤ distribution.essentialMaximumMagnitude value :=
  distribution.toFiniteContent.essentialMaximumMagnitude_nonnegative value

theorem essentialMaximumMagnitude_zero {α : Type}
    (distribution : Distribution α) :
    distribution.essentialMaximumMagnitude (fun _ => 0) = 0 :=
  distribution.toFiniteContent.essentialMaximumMagnitude_zero

/-- A normalized finite distribution has the exact expected constant law
for its computed essential maximum. -/
theorem essentialMaximumMagnitude_constant {α : Type}
    (distribution : Distribution α) (constant : Coordinate) :
    distribution.essentialMaximumMagnitude (fun _ => constant) =
      rationalSeparation constant 0 := by
  apply RFAP.ConstructiveFraction.le_antisymm
  · exact distribution.toFiniteContent.essentialMaximumMagnitude_constant_le
      constant
  · have lower :=
        distribution.toFiniteContent.poweredL1_le_of_essentialBound
          (fun _ => constant)
          (distribution.essentialMaximumMagnitude (fun _ => constant))
          (FiniteContent.essentiallyBoundedBy_essentialMaximumMagnitude
            distribution.toFiniteContent (fun _ => constant))
    unfold FiniteContent.poweredL1 at lower
    rw [distribution.toFiniteContent.integral_constant,
      distribution.toFiniteContent_total] at lower
    simpa only [one_mul] using lower

theorem essentialMaximumMagnitude_eq_zero_iff {α : Type}
    (distribution : Distribution α) (value : α → Coordinate) :
    distribution.essentialMaximumMagnitude value = 0 ↔
      distribution.EqualAlmostEverywhere value (fun _ => 0) :=
  distribution.toFiniteContent.essentialMaximumMagnitude_eq_zero_iff value

theorem essentialMaximumMagnitude_add_le {α : Type}
    (distribution : Distribution α) (left right : α → Coordinate) :
    distribution.essentialMaximumMagnitude
        (fun item => left item + right item) ≤
      distribution.essentialMaximumMagnitude left +
        distribution.essentialMaximumMagnitude right :=
  distribution.toFiniteContent.essentialMaximumMagnitude_add_le left right

theorem essentialMaximumMagnitude_scale_le {α : Type}
    (distribution : Distribution α) (factor : Coordinate)
    (value : α → Coordinate) :
    distribution.essentialMaximumMagnitude
        (fun item => factor * value item) ≤
      rationalSeparation factor 0 *
        distribution.essentialMaximumMagnitude value :=
  distribution.toFiniteContent.essentialMaximumMagnitude_scale_le
    factor value

theorem essentialMaximumMagnitude_scale {α : Type}
    (distribution : Distribution α) (factor : Coordinate)
    (value : α → Coordinate) :
    distribution.essentialMaximumMagnitude
        (fun item => factor * value item) =
      rationalSeparation factor 0 *
        distribution.essentialMaximumMagnitude value :=
  distribution.toFiniteContent.essentialMaximumMagnitude_scale factor value

theorem essentialMaximumMagnitude_neg {α : Type}
    (distribution : Distribution α) (value : α → Coordinate) :
    distribution.essentialMaximumMagnitude (fun item => -value item) =
      distribution.essentialMaximumMagnitude value :=
  distribution.toFiniteContent.essentialMaximumMagnitude_neg value

theorem essentialMaximumMagnitude_sub_le {α : Type}
    (distribution : Distribution α) (left right : α → Coordinate) :
    distribution.essentialMaximumMagnitude
        (fun item => left item - right item) ≤
      distribution.essentialMaximumMagnitude left +
        distribution.essentialMaximumMagnitude right :=
  distribution.toFiniteContent.essentialMaximumMagnitude_sub_le left right

theorem essentialMaximumMagnitude_mul_le {α : Type}
    (distribution : Distribution α) (left right : α → Coordinate) :
    distribution.essentialMaximumMagnitude
        (fun item => left item * right item) ≤
      distribution.essentialMaximumMagnitude left *
        distribution.essentialMaximumMagnitude right :=
  distribution.toFiniteContent.essentialMaximumMagnitude_mul_le left right

theorem poweredL1_mul_le_essentialMaximum_right {α : Type}
    (distribution : Distribution α) (left right : α → Coordinate) :
    distribution.poweredL1 (fun item => left item * right item) ≤
      distribution.essentialMaximumMagnitude right *
        distribution.poweredL1 left :=
  distribution.toFiniteContent
    |>.poweredL1_mul_le_essentialMaximum_right left right

theorem poweredL1_mul_le_essentialMaximum_left {α : Type}
    (distribution : Distribution α) (left right : α → Coordinate) :
    distribution.poweredL1 (fun item => left item * right item) ≤
      distribution.essentialMaximumMagnitude left *
        distribution.poweredL1 right :=
  distribution.toFiniteContent
    |>.poweredL1_mul_le_essentialMaximum_left left right

theorem l1Distance_mul_le {α : Type} (distribution : Distribution α)
    (leftFirst leftSecond rightFirst rightSecond : α → Coordinate) :
    distribution.l1Distance
        (fun item => leftFirst item * rightFirst item)
        (fun item => leftSecond item * rightSecond item) ≤
      distribution.essentialMaximumMagnitude rightFirst *
          distribution.l1Distance leftFirst leftSecond +
        distribution.essentialMaximumMagnitude leftSecond *
          distribution.l1Distance rightFirst rightSecond :=
  distribution.toFiniteContent
    |>.l1Distance_mul_le leftFirst leftSecond rightFirst rightSecond

theorem l1Distance_mul_right_le {α : Type}
    (distribution : Distribution α)
    (leftFirst leftSecond right : α → Coordinate) :
    distribution.l1Distance
        (fun item => leftFirst item * right item)
        (fun item => leftSecond item * right item) ≤
      distribution.essentialMaximumMagnitude right *
        distribution.l1Distance leftFirst leftSecond :=
  distribution.toFiniteContent
    |>.l1Distance_mul_right_le leftFirst leftSecond right

theorem l1Distance_mul_left_le {α : Type}
    (distribution : Distribution α)
    (left rightFirst rightSecond : α → Coordinate) :
    distribution.l1Distance
        (fun item => left item * rightFirst item)
        (fun item => left item * rightSecond item) ≤
      distribution.essentialMaximumMagnitude left *
        distribution.l1Distance rightFirst rightSecond :=
  distribution.toFiniteContent
    |>.l1Distance_mul_left_le left rightFirst rightSecond

def essentialMaximumDistance {α : Type} (distribution : Distribution α)
    (left right : α → Coordinate) : Coordinate :=
  distribution.toFiniteContent.essentialMaximumDistance left right

theorem essentialMaximumDistance_nonnegative {α : Type}
    (distribution : Distribution α) (left right : α → Coordinate) :
    0 ≤ distribution.essentialMaximumDistance left right :=
  distribution.toFiniteContent.essentialMaximumDistance_nonnegative left right

theorem essentialMaximumDistance_refl {α : Type}
    (distribution : Distribution α) (value : α → Coordinate) :
    distribution.essentialMaximumDistance value value = 0 :=
  distribution.toFiniteContent.essentialMaximumDistance_refl value

theorem essentialMaximumDistance_symm {α : Type}
    (distribution : Distribution α) (left right : α → Coordinate) :
    distribution.essentialMaximumDistance left right =
      distribution.essentialMaximumDistance right left :=
  distribution.toFiniteContent.essentialMaximumDistance_symm left right

theorem essentialMaximumDistance_triangle {α : Type}
    (distribution : Distribution α)
    (left middle right : α → Coordinate) :
    distribution.essentialMaximumDistance left right ≤
      distribution.essentialMaximumDistance left middle +
        distribution.essentialMaximumDistance middle right :=
  distribution.toFiniteContent.essentialMaximumDistance_triangle
    left middle right

theorem essentialMaximumDistance_reverse_triangle {α : Type}
    (distribution : Distribution α)
    (first second anchor : α → Coordinate) :
    rationalSeparation
        (distribution.essentialMaximumDistance first anchor)
        (distribution.essentialMaximumDistance second anchor) ≤
      distribution.essentialMaximumDistance first second :=
  distribution.toFiniteContent.essentialMaximumDistance_reverse_triangle
    first second anchor

theorem essentialMaximumMagnitude_eq_distance_zero {α : Type}
    (distribution : Distribution α) (value : α → Coordinate) :
    distribution.essentialMaximumMagnitude value =
      distribution.essentialMaximumDistance value (fun _ => 0) :=
  distribution.toFiniteContent.essentialMaximumMagnitude_eq_distance_zero
    value

theorem essentialMaximumMagnitude_separation_le_distance {α : Type}
    (distribution : Distribution α) (left right : α → Coordinate) :
    rationalSeparation (distribution.essentialMaximumMagnitude left)
        (distribution.essentialMaximumMagnitude right) ≤
      distribution.essentialMaximumDistance left right :=
  distribution.toFiniteContent
    |>.essentialMaximumMagnitude_separation_le_distance left right

theorem essentialMaximumDistance_eq_zero_iff {α : Type}
    (distribution : Distribution α) (left right : α → Coordinate) :
    distribution.essentialMaximumDistance left right = 0 ↔
      distribution.EqualAlmostEverywhere left right :=
  distribution.toFiniteContent.essentialMaximumDistance_eq_zero_iff left right

theorem essentialMaximumDistance_scale {α : Type}
    (distribution : Distribution α) (factor : Coordinate)
    (left right : α → Coordinate) :
    distribution.essentialMaximumDistance
        (fun item => factor * left item)
        (fun item => factor * right item) =
      rationalSeparation factor 0 *
        distribution.essentialMaximumDistance left right :=
  distribution.toFiniteContent.essentialMaximumDistance_scale
    factor left right

theorem poweredLp_le_essentialMaximum {α : Type}
    (distribution : Distribution α) (exponent : Nat)
    (value : α → Coordinate) :
    distribution.poweredLp exponent value ≤
      distribution.essentialMaximumMagnitude value ^ exponent := by
  have bound := distribution.toFiniteContent.poweredLp_le_essentialMaximum
    exponent value
  rw [distribution.toFiniteContent_total, one_mul] at bound
  exact bound

theorem poweredLpDistance_le_essentialMaximumDistance {α : Type}
    (distribution : Distribution α) (exponent : Nat)
    (left right : α → Coordinate) :
    distribution.poweredLpDistance exponent left right ≤
      distribution.essentialMaximumDistance left right ^ exponent := by
  have bound :=
    distribution.toFiniteContent.poweredLpDistance_le_essentialMaximumDistance
      exponent left right
  rw [distribution.toFiniteContent_total, one_mul] at bound
  exact bound

theorem l1Distance_le_essentialMaximumDistance {α : Type}
    (distribution : Distribution α) (left right : α → Coordinate) :
    distribution.l1Distance left right ≤
      distribution.essentialMaximumDistance left right := by
  have bound := distribution.poweredLpDistance_le_essentialMaximumDistance
    1 left right
  rw [distribution.poweredLpDistance_one, pow_one] at bound
  exact bound

/-- A normalized finite expectation is one-Lipschitz for the executable
essential-maximum distance. -/
theorem expectation_separation_le_essentialMaximumDistance {α : Type}
    (distribution : Distribution α) (left right : α → Coordinate) :
    rationalSeparation (distribution.expectation left)
        (distribution.expectation right) ≤
      distribution.essentialMaximumDistance left right :=
  (distribution.expectation_separation_le_l1Distance left right).trans
    (distribution.l1Distance_le_essentialMaximumDistance left right)

theorem poweredL2Distance_le_essentialMaximumDistance_sq {α : Type}
    (distribution : Distribution α) (left right : α → Coordinate) :
    distribution.poweredL2Distance left right ≤
      distribution.essentialMaximumDistance left right ^ 2 := by
  have bound := distribution.poweredLpDistance_le_essentialMaximumDistance
    2 left right
  rw [distribution.poweredLpDistance_two] at bound
  exact bound

end Distribution

end FiniteMeasure
