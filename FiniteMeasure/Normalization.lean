import FiniteMeasure.ContentIntegral

/-!
# Normalizing positive finite contents

Any displayed finite rational content with explicitly positive total mass can
be normalized by direct rational scaling.  Event probabilities and
expectations are exactly the original finite measure and integral divided by
that displayed total.
-/

namespace FiniteMeasure

namespace FiniteContent

/-- Normalize a positive displayed finite content to total rational mass one. -/
def normalize {α : Type} (content : FiniteContent α)
    (positive : 0 < content.total) : Distribution α where
  atoms := scaleAtoms (1 / content.total)
    (RFAP.ConstructiveFraction.div_nonneg_direct (by decide) positive.le)
    content.atoms
  total_one := by
    rw [totalWeight_scaleAtoms]
    exact RFAP.ConstructiveFraction.div_mul_cancel_of_ne
      1 content.total positive.ne'

theorem normalize_atoms_length {α : Type} (content : FiniteContent α)
    (positive : 0 < content.total) :
    (content.normalize positive).atoms.length = content.atoms.length :=
  scaleAtoms_length _ _ content.atoms

/-- Normalized event probability is exact finite content divided by total
content. -/
theorem normalize_probability {α : Type} (content : FiniteContent α)
    (positive : 0 < content.total) (event : α → Bool) :
    (content.normalize positive).probability event =
      content.measure event / content.total := by
  unfold Distribution.probability normalize measure
  rw [eventWeight_scaleAtoms]
  change (1 * content.total⁻¹) * eventWeight content.atoms event =
    eventWeight content.atoms event * content.total⁻¹
  rw [RFAP.ConstructiveFraction.one_mul]
  exact RFAP.ConstructiveFraction.mul_comm _ _

/-- Normalized expectation is exact finite integration divided by total
content. -/
theorem normalize_expectation {α : Type} (content : FiniteContent α)
    (positive : 0 < content.total) (value : α → Coordinate) :
    (content.normalize positive).expectation value =
      content.integral value / content.total := by
  unfold Distribution.expectation normalize integral
  rw [expectationWeight_scaleAtoms]
  change (1 * content.total⁻¹) *
      Distribution.expectationWeight content.atoms value =
    Distribution.expectationWeight content.atoms value * content.total⁻¹
  rw [RFAP.ConstructiveFraction.one_mul]
  exact RFAP.ConstructiveFraction.mul_comm _ _

theorem normalize_probability_mul_total {α : Type}
    (content : FiniteContent α) (positive : 0 < content.total)
    (event : α → Bool) :
    (content.normalize positive).probability event * content.total =
      content.measure event := by
  rw [content.normalize_probability positive event]
  exact RFAP.ConstructiveFraction.div_mul_cancel_of_ne _ _ positive.ne'

theorem normalize_expectation_mul_total {α : Type}
    (content : FiniteContent α) (positive : 0 < content.total)
    (value : α → Coordinate) :
    (content.normalize positive).expectation value * content.total =
      content.integral value := by
  rw [content.normalize_expectation positive value]
  exact RFAP.ConstructiveFraction.div_mul_cancel_of_ne _ _ positive.ne'

end FiniteContent

end FiniteMeasure
