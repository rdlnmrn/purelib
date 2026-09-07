import mathlib.Tactic.QuotientFreeRing
import CCL.Measure.PrefixProfile
import FiniteMeasure.EssentialMaximum

/-!
# Essential-maximum enclosures from finite CCL prefixes

A finite probability table of completed CCL prefixes has an explicit witness
probe value in every row.  The largest probe discrepancy permitted by those
finite cylinders is an executable rational radius.  Centering at the
essential maximum of the witness values therefore encloses the essential
maximum obtained from every explicitly supplied realization family.

No completed stream, limiting point, or supremum is formed.
-/

namespace CCL.FiniteMeasure

/-- Largest sensitivity-times-spread budget among the displayed nonzero
prefix rows. -/
def prefixFamilyProbeEssentialMaximumRadius
    (distribution :
      _root_.FiniteMeasure.Distribution CompletedPrefixCertificate)
    (factor : Coordinate) : Coordinate :=
  distribution.essentialMaximumMagnitude fun certificate =>
    factor * cylinderSpread certificate.blocks

/-- Essential maximum of the explicit witness probe values. -/
def prefixFamilyProbeWitnessEssentialMaximum
    (distribution :
      _root_.FiniteMeasure.Distribution CompletedPrefixCertificate)
    (probe : Proj → Coordinate) : Coordinate :=
  distribution.essentialMaximumMagnitude fun certificate =>
    probe certificate.witness

theorem prefixFamilyProbeEssentialMaximumRadius_nonnegative
    (distribution :
      _root_.FiniteMeasure.Distribution CompletedPrefixCertificate)
    (factor : Coordinate) :
    0 ≤ prefixFamilyProbeEssentialMaximumRadius distribution factor :=
  distribution.essentialMaximumMagnitude_nonnegative _

/-- Witness-centered enclosure for the essential maximum of a probe over a
finite family of CCL prefixes. -/
def prefixFamilyProbeEssentialMaximumBound
    (distribution :
      _root_.FiniteMeasure.Distribution CompletedPrefixCertificate)
    (probe : Proj → Coordinate) (factor : Coordinate) :
    _root_.FiniteMeasure.Bound where
  lower := prefixFamilyProbeWitnessEssentialMaximum distribution probe -
    prefixFamilyProbeEssentialMaximumRadius distribution factor
  upper := prefixFamilyProbeWitnessEssentialMaximum distribution probe +
    prefixFamilyProbeEssentialMaximumRadius distribution factor
  valid :=
    (sub_le_self _
      (prefixFamilyProbeEssentialMaximumRadius_nonnegative
        distribution factor)).trans
      (le_add_of_nonneg_right
        (prefixFamilyProbeEssentialMaximumRadius_nonnegative
          distribution factor))

theorem prefixFamilyProbeEssentialMaximumBound_width
    (distribution :
      _root_.FiniteMeasure.Distribution CompletedPrefixCertificate)
    (probe : Proj → Coordinate) (factor : Coordinate) :
    (prefixFamilyProbeEssentialMaximumBound distribution probe factor).width =
      2 * prefixFamilyProbeEssentialMaximumRadius distribution factor := by
  unfold prefixFamilyProbeEssentialMaximumBound
    _root_.FiniteMeasure.Bound.width
  ring1

private theorem cellRadius_le_familyRadius
    (distribution :
      _root_.FiniteMeasure.Distribution CompletedPrefixCertificate)
    (factor : Coordinate) (factorNonnegative : 0 ≤ factor)
    (atom : _root_.FiniteMeasure.Weighted CompletedPrefixCertificate)
    (member : atom ∈ distribution.atoms) (nonzero : atom.weight ≠ 0) :
    factor * cylinderSpread atom.item.blocks ≤
      prefixFamilyProbeEssentialMaximumRadius distribution factor := by
  have bounded :=
    distribution.toFiniteContent
      |>.essentiallyBoundedBy_essentialMaximumMagnitude
        (fun certificate => factor * cylinderSpread certificate.blocks)
        atom member
  rcases bounded with zero | bound
  · exact (nonzero zero).elim
  · have cellNonnegative :
        0 ≤ factor * cylinderSpread atom.item.blocks :=
      RFAP.ConstructiveFraction.mul_nonneg_direct factorNonnegative
        (cylinderSpread_nonneg atom.item.blocks)
    change _root_.FiniteMeasure.rationalSeparation
        (factor * cylinderSpread atom.item.blocks) 0 ≤
      prefixFamilyProbeEssentialMaximumRadius distribution factor at bound
    rw [_root_.FiniteMeasure.rationalSeparation_zero_of_nonneg
      cellNonnegative] at bound
    exact bound

/-- The probe values of any realization family are within the displayed
family radius of the explicit witness probe values in finite `L∞`. -/
theorem prefixFamilyProbe_essentialMaximumDistance_le_radius
    (distribution :
      _root_.FiniteMeasure.Distribution CompletedPrefixCertificate)
    (probe : Proj → Coordinate) (factor : Coordinate)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation (probe left) (probe right) ≤
        factor * CCL.Chordal.chordalSq left right)
    (points : CompletedPrefixCertificate → Proj)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.Realizes atom.item.blocks (points atom.item)) :
    distribution.essentialMaximumDistance
        (fun certificate => probe (points certificate))
        (fun certificate => probe certificate.witness) ≤
      prefixFamilyProbeEssentialMaximumRadius distribution factor := by
  change distribution.toFiniteContent.essentialMaximumMagnitude
      (fun certificate =>
        probe (points certificate) - probe certificate.witness) ≤ _
  apply distribution.toFiniteContent.essentialMaximumMagnitude_le
    (fun certificate =>
      probe (points certificate) - probe certificate.witness)
    (prefixFamilyProbeEssentialMaximumRadius distribution factor)
    (prefixFamilyProbeEssentialMaximumRadius_nonnegative
      distribution factor)
  intro atom member
  by_cases zero : atom.weight = 0
  · exact Or.inl zero
  · apply Or.inr
    change _root_.FiniteMeasure.rationalSeparation
      (probe (points atom.item) - probe atom.item.witness) 0 ≤ _
    rw [← _root_.FiniteMeasure.rationalSeparation_eq_sub_zero]
    calc
      _root_.FiniteMeasure.rationalSeparation
          (probe (points atom.item)) (probe atom.item.witness) ≤
          factor * CCL.Chordal.chordalSq
            (points atom.item) atom.item.witness :=
        sensitive _ _
      _ ≤ factor * cylinderSpread atom.item.blocks :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          (CCL.Cylinder.Realizes.chordalSq_le_half_pow
            (pointsRealize atom member) atom.item.witnessRealizes)
          factorNonnegative
      _ ≤ prefixFamilyProbeEssentialMaximumRadius distribution factor :=
        cellRadius_le_familyRadius distribution factor factorNonnegative
          atom member zero

/-- Every explicitly supplied realization family has its exact finite
essential maximum inside the CCL-derived rational enclosure. -/
theorem prefixFamilyProbeEssentialMaximumBound_contains
    (distribution :
      _root_.FiniteMeasure.Distribution CompletedPrefixCertificate)
    (probe : Proj → Coordinate) (factor : Coordinate)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation (probe left) (probe right) ≤
        factor * CCL.Chordal.chordalSq left right)
    (points : CompletedPrefixCertificate → Proj)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.Realizes atom.item.blocks (points atom.item)) :
    _root_.FiniteMeasure.Bound.Contains
      (prefixFamilyProbeEssentialMaximumBound distribution probe factor)
      (distribution.essentialMaximumMagnitude fun certificate =>
        probe (points certificate)) := by
  let actual := distribution.essentialMaximumMagnitude fun certificate =>
    probe (points certificate)
  let center := prefixFamilyProbeWitnessEssentialMaximum distribution probe
  let radius := prefixFamilyProbeEssentialMaximumRadius distribution factor
  have separation :
      _root_.FiniteMeasure.rationalSeparation actual center ≤ radius := by
    calc
      _root_.FiniteMeasure.rationalSeparation actual center ≤
          distribution.essentialMaximumDistance
            (fun certificate => probe (points certificate))
            (fun certificate => probe certificate.witness) :=
        distribution.essentialMaximumMagnitude_separation_le_distance _ _
      _ ≤ radius :=
        prefixFamilyProbe_essentialMaximumDistance_le_radius distribution
          probe factor factorNonnegative sensitive points pointsRealize
  have directed : actual - center ≤ radius ∧ center - actual ≤ radius :=
    max_le_iff.mp separation
  change center - radius ≤ actual ∧ actual ≤ center + radius
  constructor
  · apply (sub_le_iff_le_add).2
    calc
      center ≤ radius + actual := (sub_le_iff_le_add).1 directed.2
      _ = actual + radius := by ring1
  · calc
      actual ≤ radius + center := (sub_le_iff_le_add).1 directed.1
      _ = center + radius := by ring1

private theorem quarter_add_quarter_eq_half (target : Coordinate) :
    target / 4 + target / 4 = target / 2 := by
  apply RFAP.ConstructiveFraction.mul_right_cancel_of_ne
    (show (4 : Coordinate) ≠ 0 by decide)
  calc
    (target / 4 + target / 4) * 4 =
        (target / 4) * 4 + (target / 4) * 4 := by rw [add_mul]
    _ = target + target := by
      rw [show target / 4 * 4 = target from
        RFAP.ConstructiveFraction.div_mul_cancel_of_ne target 4 (by decide)]
    _ = target * 2 := by ring1
    _ = ((target / 2) * 2) * 2 := by
      rw [show target / 2 * 2 = target from
        RFAP.ConstructiveFraction.div_mul_cancel_of_ne target 2 (by decide)]
    _ = (target / 2) * (2 * 2) :=
      RFAP.ConstructiveFraction.mul_assoc (target / 2) 2 2
    _ = (target / 2) * 4 := by
      rw [show (2 : Coordinate) * 2 = 4 by decide]

private theorem two_mul_quarter_eq_half (target : Coordinate) :
    2 * (target / 4) = target / 2 := by
  calc
    2 * (target / 4) = target / 4 + target / 4 := by ring1
    _ = target / 2 := quarter_add_quarter_eq_half target

private theorem half_lt_self {target : Coordinate} (positive : 0 < target) :
    target / 2 < target := by
  apply (RFAP.ConstructiveFraction.div_lt_iff_pos
    (by decide : (0 : Coordinate) < 2)).2
  calc
    target = target * 1 := by ring1
    _ < target * 2 :=
      RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
        positive (by decide)

/-- A uniformly sufficient displayed block count makes the finite
essential-maximum enclosure narrower than any supplied positive rational
target.  The quarter-target request leaves explicit slack, avoiding a
strict-maximum construction. -/
theorem prefixFamilyProbeEssentialMaximumBound_width_lt_requested
    (distribution :
      _root_.FiniteMeasure.Distribution CompletedPrefixCertificate)
    (probe : Proj → Coordinate) (factor : Coordinate)
    (factorPositive : 0 < factor)
    (sensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation (probe left) (probe right) ≤
        factor * CCL.Chordal.chordalSq left right)
    (target : Coordinate) (targetPositive : 0 < target)
    (enough : ∀ atom, atom ∈ distribution.atoms →
      requiredProbeBlockCount (target / 4) factor ≤
        atom.item.blocks.length) :
    (prefixFamilyProbeEssentialMaximumBound distribution probe factor).width <
      target := by
  have quarterPositive : 0 < target / 4 :=
    RFAP.ConstructiveFraction.div_pos_direct targetPositive (by decide)
  have radiusBound :
      prefixFamilyProbeEssentialMaximumRadius distribution factor ≤
        target / 4 := by
    apply distribution.toFiniteContent.essentialMaximumMagnitude_le
      (fun certificate => factor * cylinderSpread certificate.blocks)
      (target / 4) quarterPositive.le
    intro atom member
    by_cases zero : atom.weight = 0
    · exact Or.inl zero
    · apply Or.inr
      have cellNonnegative :
          0 ≤ factor * cylinderSpread atom.item.blocks :=
        RFAP.ConstructiveFraction.mul_nonneg_direct factorPositive.le
          (cylinderSpread_nonneg atom.item.blocks)
      change _root_.FiniteMeasure.rationalSeparation
          (factor * cylinderSpread atom.item.blocks) 0 ≤ target / 4
      rw [_root_.FiniteMeasure.rationalSeparation_zero_of_nonneg
        cellNonnegative]
      have widthSmall := completedPrefixProbeBound_width_lt_requested
        atom.item.witness atom.item.witnessRealizes probe factor
        factorPositive sensitive (target / 4) quarterPositive
        (enough atom member)
      rw [completedPrefixProbeBound_width] at widthSmall
      exact (calc
          factor * cylinderSpread atom.item.blocks ≤
              2 * (factor * cylinderSpread atom.item.blocks) := by
            calc
              factor * cylinderSpread atom.item.blocks =
                  factor * cylinderSpread atom.item.blocks + 0 := by ring1
              _ ≤ factor * cylinderSpread atom.item.blocks +
                    factor * cylinderSpread atom.item.blocks :=
                add_le_add le_rfl cellNonnegative
              _ = 2 * (factor * cylinderSpread atom.item.blocks) := by ring1
          _ < target / 4 := widthSmall).le
  rw [prefixFamilyProbeEssentialMaximumBound_width]
  calc
    2 * prefixFamilyProbeEssentialMaximumRadius distribution factor ≤
        2 * (target / 4) :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        radiusBound (by decide)
    _ = target / 2 := two_mul_quarter_eq_half target
    _ < target := half_lt_self targetPositive

end CCL.FiniteMeasure
