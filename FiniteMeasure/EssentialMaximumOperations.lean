import FiniteMeasure.EssentialMaximum
import FiniteMeasure.Conditioning

/-!
# Essential maxima under finite measure operations

Restriction and nonnegative reweighting can only remove nonzero rows from
the support relevant to the executable essential maximum.  Consequently
restriction, change of density, and positive-event conditioning are exact
finite `L∞` contractions.
-/

namespace FiniteMeasure

private theorem mem_restrictAtoms {α : Type} :
    ∀ (atoms : List (Weighted α)) (event : α → Bool)
      (candidate : Weighted α),
      candidate ∈ restrictAtoms atoms event → candidate ∈ atoms
  | [], event, candidate, member => by
      cases member
  | atom :: remaining, event, candidate, member => by
      cases selected : event atom.item
      · simp only [restrictAtoms, selected] at member
        exact List.mem_cons_of_mem atom
          (mem_restrictAtoms remaining event candidate member)
      · simp only [restrictAtoms, selected] at member
        rcases List.mem_cons.mp member with same | tail
        · subst candidate
          exact List.mem_cons_self
        · exact List.mem_cons_of_mem atom
            (mem_restrictAtoms remaining event candidate tail)

private theorem essentiallyBoundedByOn_densityAtoms {α : Type}
    (density : α → Coordinate) (densityNonnegative : ∀ item, 0 ≤ density item)
    (value : α → Coordinate) (ceiling : Coordinate) :
    ∀ atoms : List (Weighted α),
      EssentiallyBoundedByOn atoms value ceiling →
        EssentiallyBoundedByOn
          (densityAtoms density densityNonnegative atoms) value ceiling
  | [], bounded => by
      intro atom member
      cases member
  | source :: remaining, bounded => by
      have tailBounded : EssentiallyBoundedByOn remaining value ceiling :=
        fun atom member =>
          bounded atom (List.mem_cons_of_mem source member)
      have tailResult := essentiallyBoundedByOn_densityAtoms
        density densityNonnegative value ceiling remaining tailBounded
      intro candidate member
      simp only [densityAtoms, List.mem_cons] at member
      rcases member with same | tail
      · subst candidate
        rcases bounded source List.mem_cons_self with sourceZero | valueBound
        · apply Or.inl
          change source.weight * density source.item = 0
          rw [sourceZero, zero_mul]
        · exact Or.inr valueBound
      · exact tailResult candidate tail

private theorem essentialMaximumMagnitudeOn_append_direct {α : Type}
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
          essentialMaximumMagnitudeOn_append_direct value remaining right]
      · simp only [List.cons_append, essentialMaximumMagnitudeOn, zero,
          ↓reduceIte,
          essentialMaximumMagnitudeOn_append_direct value remaining right]
        exact (max_assoc _ _ _).symm

private theorem essentialMaximumMagnitudeOn_scaleAtoms_of_eq_zero_direct
    {α : Type} (value : α → Coordinate) (factor : Coordinate)
    (factorNonnegative : 0 ≤ factor) (factorZero : factor = 0) :
    ∀ atoms : List (Weighted α),
      essentialMaximumMagnitudeOn value
        (scaleAtoms factor factorNonnegative atoms) = 0
  | [] => rfl
  | atom :: remaining => by
      have scaledZero : factor * atom.weight = 0 := by
        rw [factorZero, zero_mul]
      simp only [scaleAtoms, essentialMaximumMagnitudeOn, scaledZero,
        ↓reduceIte,
        essentialMaximumMagnitudeOn_scaleAtoms_of_eq_zero_direct value
          factor factorNonnegative factorZero remaining]

private theorem essentialMaximumMagnitudeOn_scaleAtoms_of_ne_direct
    {α : Type} (value : α → Coordinate) (factor : Coordinate)
    (factorNonnegative : 0 ≤ factor) (factorNonzero : factor ≠ 0) :
    ∀ atoms : List (Weighted α),
      essentialMaximumMagnitudeOn value
          (scaleAtoms factor factorNonnegative atoms) =
        essentialMaximumMagnitudeOn value atoms
  | [] => rfl
  | atom :: remaining => by
      by_cases atomZero : atom.weight = 0
      · simp only [scaleAtoms, essentialMaximumMagnitudeOn, atomZero,
          mul_zero, ↓reduceIte,
          essentialMaximumMagnitudeOn_scaleAtoms_of_ne_direct value factor
            factorNonnegative factorNonzero remaining]
      · have productNonzero : factor * atom.weight ≠ 0 :=
          RFAP.ConstructiveFraction.mul_ne_zero_direct
            factorNonzero atomZero
        simp only [scaleAtoms, essentialMaximumMagnitudeOn, productNonzero,
          atomZero, ↓reduceIte,
          essentialMaximumMagnitudeOn_scaleAtoms_of_ne_direct value factor
            factorNonnegative factorNonzero remaining]

namespace FiniteContent

/-- The essential maximum on a concatenated finite content is exactly the
maximum of the two component essential maxima. -/
theorem append_essentialMaximumMagnitude {α : Type}
    (left right : FiniteContent α) (value : α → Coordinate) :
    (left.append right).essentialMaximumMagnitude value =
      max (left.essentialMaximumMagnitude value)
        (right.essentialMaximumMagnitude value) :=
  essentialMaximumMagnitudeOn_append_direct value left.atoms right.atoms

theorem append_essentialMaximumDistance {α : Type}
    (left right : FiniteContent α) (first second : α → Coordinate) :
    (left.append right).essentialMaximumDistance first second =
      max (left.essentialMaximumDistance first second)
        (right.essentialMaximumDistance first second) := by
  unfold essentialMaximumDistance
  exact left.append_essentialMaximumMagnitude right
    (fun item => first item - second item)

/-- Scaling every displayed weight by zero removes the whole support seen by
the executable essential maximum. -/
theorem scale_essentialMaximumMagnitude_of_eq_zero {α : Type}
    (content : FiniteContent α) (factor : Coordinate)
    (factorNonnegative : 0 ≤ factor) (factorZero : factor = 0)
    (value : α → Coordinate) :
    (content.scale factor factorNonnegative).essentialMaximumMagnitude value =
      0 :=
  essentialMaximumMagnitudeOn_scaleAtoms_of_eq_zero_direct value factor
    factorNonnegative factorZero content.atoms

/-- Scaling all displayed weights by a nonzero nonnegative rational preserves
the support and hence preserves the executable essential maximum exactly. -/
theorem scale_essentialMaximumMagnitude_of_ne {α : Type}
    (content : FiniteContent α) (factor : Coordinate)
    (factorNonnegative : 0 ≤ factor) (factorNonzero : factor ≠ 0)
    (value : α → Coordinate) :
    (content.scale factor factorNonnegative).essentialMaximumMagnitude value =
      content.essentialMaximumMagnitude value :=
  essentialMaximumMagnitudeOn_scaleAtoms_of_ne_direct value factor
    factorNonnegative factorNonzero content.atoms

/-- Nonnegative scaling can only preserve or discard nonzero support rows. -/
theorem scale_essentialMaximumMagnitude_le {α : Type}
    (content : FiniteContent α) (factor : Coordinate)
    (factorNonnegative : 0 ≤ factor) (value : α → Coordinate) :
    (content.scale factor factorNonnegative).essentialMaximumMagnitude value ≤
      content.essentialMaximumMagnitude value := by
  by_cases factorZero : factor = 0
  · rw [content.scale_essentialMaximumMagnitude_of_eq_zero factor
      factorNonnegative factorZero value]
    exact content.essentialMaximumMagnitude_nonnegative value
  · rw [content.scale_essentialMaximumMagnitude_of_ne factor
      factorNonnegative factorZero value]

theorem scale_essentialMaximumDistance_le {α : Type}
    (content : FiniteContent α) (factor : Coordinate)
    (factorNonnegative : 0 ≤ factor) (first second : α → Coordinate) :
    (content.scale factor factorNonnegative).essentialMaximumDistance
        first second ≤
      content.essentialMaximumDistance first second := by
  unfold essentialMaximumDistance
  exact content.scale_essentialMaximumMagnitude_le factor
    factorNonnegative (fun item => first item - second item)

/-- Restricting a displayed content cannot increase its computed essential
maximum. -/
theorem restrict_essentialMaximumMagnitude_le {α : Type}
    (content : FiniteContent α) (event : α → Bool)
    (value : α → Coordinate) :
    (content.restrict event).essentialMaximumMagnitude value ≤
      content.essentialMaximumMagnitude value := by
  apply (content.restrict event).essentialMaximumMagnitude_le value
    (content.essentialMaximumMagnitude value)
    (content.essentialMaximumMagnitude_nonnegative value)
  intro atom member
  exact content.essentiallyBoundedBy_essentialMaximumMagnitude value atom
    (mem_restrictAtoms content.atoms event atom member)

theorem restrict_essentialMaximumDistance_le {α : Type}
    (content : FiniteContent α) (event : α → Bool)
    (left right : α → Coordinate) :
    (content.restrict event).essentialMaximumDistance left right ≤
      content.essentialMaximumDistance left right := by
  unfold essentialMaximumDistance
  exact content.restrict_essentialMaximumMagnitude_le event
    (fun item => left item - right item)

/-- Any displayed nonnegative density change can only discard support rows
from the essential-maximum calculation. -/
theorem reweight_essentialMaximumMagnitude_le {α : Type}
    (content : FiniteContent α) (density : α → Coordinate)
    (densityNonnegative : ∀ item, 0 ≤ density item)
    (value : α → Coordinate) :
    (content.reweight density densityNonnegative).essentialMaximumMagnitude
        value ≤
      content.essentialMaximumMagnitude value := by
  apply (content.reweight density densityNonnegative)
    |>.essentialMaximumMagnitude_le value
      (content.essentialMaximumMagnitude value)
      (content.essentialMaximumMagnitude_nonnegative value)
  exact essentiallyBoundedByOn_densityAtoms density densityNonnegative
    value (content.essentialMaximumMagnitude value) content.atoms
      (content.essentiallyBoundedBy_essentialMaximumMagnitude value)

theorem reweight_essentialMaximumDistance_le {α : Type}
    (content : FiniteContent α) (density : α → Coordinate)
    (densityNonnegative : ∀ item, 0 ≤ density item)
    (left right : α → Coordinate) :
    (content.reweight density densityNonnegative).essentialMaximumDistance
        left right ≤
      content.essentialMaximumDistance left right := by
  unfold essentialMaximumDistance
  exact content.reweight_essentialMaximumMagnitude_le
    density densityNonnegative (fun item => left item - right item)

end FiniteContent

namespace Distribution

theorem reweight_essentialMaximumMagnitude_le {α : Type}
    (distribution : Distribution α) (density : α → Coordinate)
    (densityNonnegative : ∀ item, 0 ≤ density item)
    (normalizes : distribution.expectation density = 1)
    (value : α → Coordinate) :
    (distribution.reweight density densityNonnegative normalizes).essentialMaximumMagnitude
        value ≤
      distribution.essentialMaximumMagnitude value :=
  distribution.toFiniteContent.reweight_essentialMaximumMagnitude_le
    density densityNonnegative value

theorem reweight_essentialMaximumDistance_le {α : Type}
    (distribution : Distribution α) (density : α → Coordinate)
    (densityNonnegative : ∀ item, 0 ≤ density item)
    (normalizes : distribution.expectation density = 1)
    (left right : α → Coordinate) :
    (distribution.reweight density densityNonnegative normalizes).essentialMaximumDistance
        left right ≤
      distribution.essentialMaximumDistance left right :=
  distribution.toFiniteContent.reweight_essentialMaximumDistance_le
    density densityNonnegative left right

/-- Conditioning on an explicitly positive event is an `L∞` contraction. -/
theorem conditioned_essentialMaximumMagnitude_le {α : Type}
    (distribution : Distribution α) (event : α → Bool)
    (positive : 0 < distribution.probability event)
    (value : α → Coordinate) :
    (distribution.conditioned event positive).essentialMaximumMagnitude
        value ≤
      distribution.essentialMaximumMagnitude value := by
  unfold conditioned
  exact distribution.reweight_essentialMaximumMagnitude_le
    (distribution.conditioningDensity event positive)
    (distribution.conditioningDensity_nonnegative event positive)
    (distribution.conditioningDensity_normalizes event positive) value

theorem conditioned_essentialMaximumDistance_le {α : Type}
    (distribution : Distribution α) (event : α → Bool)
    (positive : 0 < distribution.probability event)
    (left right : α → Coordinate) :
    (distribution.conditioned event positive).essentialMaximumDistance
        left right ≤
      distribution.essentialMaximumDistance left right := by
  unfold conditioned
  exact distribution.reweight_essentialMaximumDistance_le
    (distribution.conditioningDensity event positive)
    (distribution.conditioningDensity_nonnegative event positive)
    (distribution.conditioningDensity_normalizes event positive)
    left right

end Distribution

end FiniteMeasure
