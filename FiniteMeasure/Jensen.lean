import mathlib.Tactic.QuotientFreeRing
import FiniteMeasure.L1

/-!
# Finite rational Jensen certificates

A supporting line supplied at the exact rational mean proves Jensen's
inequality by finite linearity.  Convex functions on a completed carrier are
not introduced: the caller gives the finitely checkable support inequalities
needed on the displayed atoms.
-/

namespace FiniteMeasure

namespace Distribution

/-- A displayed supporting line at the rational mean is sufficient for the
finite Jensen inequality. -/
theorem jensen_of_supportingLine {α : Type}
    (distribution : Distribution α) (value : α → Coordinate)
    (transform : Coordinate → Coordinate) (slope : Coordinate)
    (supports : ∀ atom, atom ∈ distribution.atoms →
      transform (distribution.expectation value) +
          slope * (value atom.item - distribution.expectation value) ≤
        transform (value atom.item)) :
    transform (distribution.expectation value) ≤
      distribution.expectation (fun item => transform (value item)) := by
  calc
    transform (distribution.expectation value) =
        distribution.expectation (fun item =>
          transform (distribution.expectation value) +
            slope * (value item - distribution.expectation value)) := by
      rw [distribution.expectation_add, distribution.expectation_scale,
        distribution.expectation_sub, distribution.expectation_constant,
        distribution.expectation_constant]
      ring1
    _ ≤ distribution.expectation (fun item => transform (value item)) := by
      apply distribution.expectation_mono
      intro atom member
      exact supports atom member

/-- Squaring has the explicit supporting slope twice the rational mean, so
finite Jensen recovers the second-moment bound without any square root. -/
theorem jensen_square {α : Type} (distribution : Distribution α)
    (value : α → Coordinate) :
    distribution.expectation value ^ 2 ≤
      distribution.expectation (fun item => value item ^ 2) := by
  apply distribution.jensen_of_supportingLine value (fun item => item ^ 2)
    (2 * distribution.expectation value)
  intro atom member
  apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
  calc
    0 ≤ (value atom.item - distribution.expectation value) ^ 2 :=
      RFAP.ConstructiveFraction.sq_nonneg_direct _
    _ = value atom.item ^ 2 -
        (distribution.expectation value ^ 2 +
          2 * distribution.expectation value *
            (value atom.item - distribution.expectation value)) := by
      ring1

/-- The rational absolute-value analogue: separation of the mean from zero
is bounded by the mean separation from zero.  The supporting slope is chosen
by the decidable sign of the rational mean. -/
theorem jensen_rationalSeparation_zero {α : Type}
    (distribution : Distribution α) (value : α → Coordinate) :
    rationalSeparation (distribution.expectation value) 0 ≤
      distribution.expectation (fun item =>
        rationalSeparation (value item) 0) := by
  by_cases meanNonnegative : 0 ≤ distribution.expectation value
  · apply distribution.jensen_of_supportingLine value
      (fun item => rationalSeparation item 0) 1
    intro atom member
    rw [rationalSeparation_zero_of_nonneg meanNonnegative]
    calc
      distribution.expectation value +
            1 * (value atom.item - distribution.expectation value) =
          value atom.item := by
        ring1
      _ ≤ rationalSeparation (value atom.item) 0 :=
        by
          unfold rationalSeparation
          rw [sub_zero, zero_sub]
          exact le_max_left _ _
  · have meanNonpositive : distribution.expectation value ≤ 0 :=
      (RFAP.ConstructiveFraction.lt_of_not_ge_direct meanNonnegative).le
    apply distribution.jensen_of_supportingLine value
      (fun item => rationalSeparation item 0) (-1)
    intro atom member
    rw [rationalSeparation_zero_of_nonpos meanNonpositive]
    calc
      -distribution.expectation value +
            -1 * (value atom.item - distribution.expectation value) =
          -value atom.item := by
        ring1
      _ ≤ rationalSeparation (value atom.item) 0 :=
        by
          unfold rationalSeparation
          rw [sub_zero, zero_sub]
          exact le_max_right _ _

end Distribution

end FiniteMeasure
