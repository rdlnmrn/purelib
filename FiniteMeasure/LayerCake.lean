import FiniteMeasure.ContentIntegral
import FiniteMeasure.ZeroWeight

/-!
# Finite layer-cake identities

For a natural-valued observable, truncation at a displayed finite height is
the sum of its Boolean upper-level indicators.  Integrating this pointwise
identity gives an exact finite tail-sum, or layer-cake, formula.  There is no
infinite series and no improper integral.
-/

namespace FiniteMeasure

/-- Executable strict upper-level event for a natural-valued observable. -/
def natAboveEvent {α : Type} (height : Nat) (value : α → Nat) : α → Bool :=
  fun item => decide (height < value item)

namespace FiniteContent

/-- Sum of upper-level contents from level zero to the displayed height. -/
def natTailMeasureSum {α : Type} (content : FiniteContent α)
    (value : α → Nat) : Nat → Coordinate
  | 0 => 0
  | height + 1 =>
      natTailMeasureSum content value height +
        content.measure (natAboveEvent height value)

private theorem cast_min_succ_eq_cast_min_add_indicator {α : Type}
    (value : α → Nat) (height : Nat) (item : α) :
    ((min (value item) (height + 1) : Nat) : Coordinate) =
      ((min (value item) height : Nat) : Coordinate) +
        Distribution.indicator (natAboveEvent height value) item := by
  by_cases above : height < value item
  · have naturalIdentity :
        min (value item) (height + 1) = min (value item) height + 1 := by
      rw [Nat.min_eq_right (Nat.succ_le_of_lt above),
        Nat.min_eq_right (Nat.le_of_lt above)]
    rw [naturalIdentity, Nat.cast_add, Nat.cast_one]
    simp only [Distribution.indicator, natAboveEvent, above, decide_true]
  · have naturalIdentity :
        min (value item) (height + 1) = min (value item) height := by
      have valueLeHeight : value item ≤ height := Nat.le_of_not_gt above
      rw [Nat.min_eq_left (valueLeHeight.trans (Nat.le_succ height)),
        Nat.min_eq_left valueLeHeight]
    rw [naturalIdentity]
    simp only [Distribution.indicator, natAboveEvent, above, decide_false,
      add_zero]

/-- Exact finite layer-cake formula for a natural observable truncated at a
displayed height. -/
theorem integral_truncatedNat_eq_natTailMeasureSum {α : Type}
    (content : FiniteContent α) (value : α → Nat) :
    ∀ height : Nat,
      content.integral (fun item =>
          ((min (value item) height : Nat) : Coordinate)) =
        content.natTailMeasureSum value height
  | 0 => by
      rw [natTailMeasureSum]
      calc
        content.integral (fun item =>
              ((min (value item) 0 : Nat) : Coordinate)) =
            content.integral (fun _ => (0 : Coordinate)) :=
          content.integral_congr _ _ (fun item => by
            simp only [min_eq_right, Nat.zero_le, Nat.cast_zero])
        _ = content.total * 0 := content.integral_constant 0
        _ = 0 := mul_zero content.total
  | height + 1 => by
      rw [natTailMeasureSum]
      calc
        content.integral (fun item =>
              ((min (value item) (height + 1) : Nat) : Coordinate)) =
            content.integral (fun item =>
              ((min (value item) height : Nat) : Coordinate) +
                Distribution.indicator
                  (natAboveEvent height value) item) :=
          content.integral_congr _ _ (fun item =>
            cast_min_succ_eq_cast_min_add_indicator value height item)
        _ = content.integral (fun item =>
              ((min (value item) height : Nat) : Coordinate)) +
              content.integral
                (Distribution.indicator (natAboveEvent height value)) :=
          content.integral_add _ _
        _ = content.natTailMeasureSum value height +
              content.measure (natAboveEvent height value) :=
          congrArg₂ (fun left right => left + right)
            (integral_truncatedNat_eq_natTailMeasureSum
              content value height)
            (content.integral_indicator (natAboveEvent height value))

/-- If the displayed atoms are bounded by the chosen height, the truncated
formula is the ordinary expectation of the natural observable. -/
theorem integral_nat_eq_natTailMeasureSum_of_bounded {α : Type}
    (content : FiniteContent α) (value : α → Nat) (height : Nat)
    (bounded : ∀ atom, atom ∈ content.atoms → value atom.item ≤ height) :
    content.integral (fun item => (value item : Coordinate)) =
      content.natTailMeasureSum value height := by
  calc
    content.integral (fun item => (value item : Coordinate)) =
        content.integral (fun item =>
          ((min (value item) height : Nat) : Coordinate)) := by
      apply expectationWeight_congr_off_zero content.atoms
      intro atom member
      apply Or.inr
      change (value atom.item : Coordinate) =
        ((min (value atom.item) height : Nat) : Coordinate)
      rw [Nat.min_eq_left (bounded atom member)]
    _ = content.natTailMeasureSum value height :=
      content.integral_truncatedNat_eq_natTailMeasureSum value height

end FiniteContent

namespace Distribution

/-- Finite sum of natural upper-tail probabilities. -/
def natTailProbabilitySum {α : Type} (distribution : Distribution α)
    (value : α → Nat) (height : Nat) : Coordinate :=
  distribution.toFiniteContent.natTailMeasureSum value height

theorem expectation_truncatedNat_eq_natTailProbabilitySum {α : Type}
    (distribution : Distribution α) (value : α → Nat)
    (height : Nat) :
    distribution.expectation (fun item =>
        ((min (value item) height : Nat) : Coordinate)) =
      distribution.natTailProbabilitySum value height :=
  distribution.toFiniteContent.integral_truncatedNat_eq_natTailMeasureSum
    value height

/-- Exact finite probability tail-sum formula for an atomwise bounded
natural observable. -/
theorem expectation_nat_eq_natTailProbabilitySum_of_bounded {α : Type}
    (distribution : Distribution α) (value : α → Nat) (height : Nat)
    (bounded : ∀ atom, atom ∈ distribution.atoms →
      value atom.item ≤ height) :
    distribution.expectation (fun item => (value item : Coordinate)) =
      distribution.natTailProbabilitySum value height :=
  distribution.toFiniteContent.integral_nat_eq_natTailMeasureSum_of_bounded
    value height bounded

end Distribution

end FiniteMeasure
