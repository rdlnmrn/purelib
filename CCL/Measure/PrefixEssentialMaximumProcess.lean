import mathlib.Tactic.QuotientFreeRing
import CCL.Measure.PrefixEssentialMaximum
import CCL.Measure.PrefixProcess

/-!
# Progressive essential maxima from finite CCL prefixes

This module packages the static CCL essential-maximum enclosure as a finite
request process.  A request computes one natural block count, extends every
displayed prefix to at least that length, and returns a nested rational bound
of the requested width.  It does not construct a stream of requests.
-/

namespace CCL.FiniteMeasure

namespace PrefixFamilyProcess

/-- Current largest sensitivity-times-spread budget over a fixed finite
index distribution. -/
def probeEssentialMaximumRadius {ι : Type}
    (process : PrefixFamilyProcess ι)
    (distribution : _root_.FiniteMeasure.Distribution ι)
    (state : process.State) (factor : Coordinate) : Coordinate :=
  distribution.essentialMaximumMagnitude fun item =>
    factor * cylinderSpread (process.blocks state item)

/-- Essential maximum of the process's fixed explicit witness probe values. -/
def probeWitnessEssentialMaximum {ι : Type}
    (process : PrefixFamilyProcess ι)
    (distribution : _root_.FiniteMeasure.Distribution ι)
    (probe : Proj → Coordinate) : Coordinate :=
  distribution.essentialMaximumMagnitude fun item =>
    probe (process.witness item)

theorem probeEssentialMaximumRadius_nonnegative {ι : Type}
    (process : PrefixFamilyProcess ι)
    (distribution : _root_.FiniteMeasure.Distribution ι)
    (state : process.State) (factor : Coordinate) :
    0 ≤ process.probeEssentialMaximumRadius distribution state factor :=
  distribution.essentialMaximumMagnitude_nonnegative _

/-- Current witness-centered essential-maximum enclosure. -/
def probeEssentialMaximumBound {ι : Type}
    (process : PrefixFamilyProcess ι)
    (distribution : _root_.FiniteMeasure.Distribution ι)
    (state : process.State) (probe : Proj → Coordinate)
    (factor : Coordinate) : _root_.FiniteMeasure.Bound where
  lower := process.probeWitnessEssentialMaximum distribution probe -
    process.probeEssentialMaximumRadius distribution state factor
  upper := process.probeWitnessEssentialMaximum distribution probe +
    process.probeEssentialMaximumRadius distribution state factor
  valid :=
    (sub_le_self _
      (process.probeEssentialMaximumRadius_nonnegative
        distribution state factor)).trans
      (le_add_of_nonneg_right
        (process.probeEssentialMaximumRadius_nonnegative
          distribution state factor))

theorem probeEssentialMaximumBound_width {ι : Type}
    (process : PrefixFamilyProcess ι)
    (distribution : _root_.FiniteMeasure.Distribution ι)
    (state : process.State) (probe : Proj → Coordinate)
    (factor : Coordinate) :
    (process.probeEssentialMaximumBound distribution state probe factor).width =
      2 * process.probeEssentialMaximumRadius distribution state factor := by
  unfold probeEssentialMaximumBound _root_.FiniteMeasure.Bound.width
  ring1

private theorem cellRadius_le_radius {ι : Type}
    (process : PrefixFamilyProcess ι)
    (distribution : _root_.FiniteMeasure.Distribution ι)
    (state : process.State) (factor : Coordinate)
    (factorNonnegative : 0 ≤ factor)
    (atom : _root_.FiniteMeasure.Weighted ι)
    (member : atom ∈ distribution.atoms) (nonzero : atom.weight ≠ 0) :
    factor * cylinderSpread (process.blocks state atom.item) ≤
      process.probeEssentialMaximumRadius distribution state factor := by
  have bounded :=
    distribution.toFiniteContent
      |>.essentiallyBoundedBy_essentialMaximumMagnitude
        (fun item => factor * cylinderSpread (process.blocks state item))
        atom member
  rcases bounded with zero | bound
  · exact (nonzero zero).elim
  · have cellNonnegative :
        0 ≤ factor * cylinderSpread (process.blocks state atom.item) :=
      RFAP.ConstructiveFraction.mul_nonneg_direct factorNonnegative
        (cylinderSpread_nonneg (process.blocks state atom.item))
    change _root_.FiniteMeasure.rationalSeparation
        (factor * cylinderSpread (process.blocks state atom.item)) 0 ≤
      process.probeEssentialMaximumRadius distribution state factor at bound
    rw [_root_.FiniteMeasure.rationalSeparation_zero_of_nonneg
      cellNonnegative] at bound
    exact bound

private theorem probeEssentialMaximumRadius_le_of_extensions {ι : Type}
    (process : PrefixFamilyProcess ι)
    (distribution : _root_.FiniteMeasure.Distribution ι)
    (inner outer : process.State) (factor : Coordinate)
    (factorNonnegative : 0 ≤ factor)
    (extension : ∀ item, ∃ suffix,
      process.blocks inner item = process.blocks outer item ++ suffix) :
    process.probeEssentialMaximumRadius distribution inner factor ≤
      process.probeEssentialMaximumRadius distribution outer factor := by
  apply distribution.toFiniteContent.essentialMaximumMagnitude_le
    (fun item => factor * cylinderSpread (process.blocks inner item))
    (process.probeEssentialMaximumRadius distribution outer factor)
    (process.probeEssentialMaximumRadius_nonnegative
      distribution outer factor)
  intro atom member
  by_cases zero : atom.weight = 0
  · exact Or.inl zero
  · apply Or.inr
    have innerNonnegative :
        0 ≤ factor * cylinderSpread (process.blocks inner atom.item) :=
      RFAP.ConstructiveFraction.mul_nonneg_direct factorNonnegative
        (cylinderSpread_nonneg (process.blocks inner atom.item))
    change _root_.FiniteMeasure.rationalSeparation
        (factor * cylinderSpread (process.blocks inner atom.item)) 0 ≤ _
    rw [_root_.FiniteMeasure.rationalSeparation_zero_of_nonneg
      innerNonnegative]
    rcases extension atom.item with ⟨suffix, equal⟩
    calc
      factor * cylinderSpread (process.blocks inner atom.item) =
          factor * cylinderSpread
            (process.blocks outer atom.item ++ suffix) := by rw [equal]
      _ ≤ factor * cylinderSpread (process.blocks outer atom.item) :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          (cylinderSpread_le_of_append
            (process.blocks outer atom.item) suffix)
          factorNonnegative
      _ ≤ process.probeEssentialMaximumRadius distribution outer factor :=
        process.cellRadius_le_radius distribution outer factor
          factorNonnegative atom member zero

private theorem probeEssentialMaximumBound_refines_of_extensions {ι : Type}
    (process : PrefixFamilyProcess ι)
    (distribution : _root_.FiniteMeasure.Distribution ι)
    (inner outer : process.State) (probe : Proj → Coordinate)
    (factor : Coordinate) (factorNonnegative : 0 ≤ factor)
    (extension : ∀ item, ∃ suffix,
      process.blocks inner item = process.blocks outer item ++ suffix) :
    _root_.FiniteMeasure.Bound.Refines
      (process.probeEssentialMaximumBound distribution inner probe factor)
      (process.probeEssentialMaximumBound distribution outer probe factor) := by
  have radiusLe := process.probeEssentialMaximumRadius_le_of_extensions
    distribution inner outer factor factorNonnegative extension
  constructor
  · exact RFAP.ConstructiveFraction.sub_le_sub_left_direct radiusLe
      (process.probeWitnessEssentialMaximum distribution probe)
  · exact RFAP.ConstructiveFraction.add_le_add_direct le_rfl radiusLe

/-- Every explicit realization family remains within the current finite
`L∞` radius of the fixed witness family. -/
theorem probe_essentialMaximumDistance_le_radius {ι : Type}
    (process : PrefixFamilyProcess ι)
    (distribution : _root_.FiniteMeasure.Distribution ι)
    (state : process.State) (probe : Proj → Coordinate)
    (factor : Coordinate) (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation (probe left) (probe right) ≤
        factor * CCL.Chordal.chordalSq left right)
    (points : ι → Proj)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.Realizes (process.blocks state atom.item)
        (points atom.item)) :
    distribution.essentialMaximumDistance
        (fun item => probe (points item))
        (fun item => probe (process.witness item)) ≤
      process.probeEssentialMaximumRadius distribution state factor := by
  change distribution.toFiniteContent.essentialMaximumMagnitude
      (fun item => probe (points item) - probe (process.witness item)) ≤ _
  apply distribution.toFiniteContent.essentialMaximumMagnitude_le
    (fun item => probe (points item) - probe (process.witness item))
    (process.probeEssentialMaximumRadius distribution state factor)
    (process.probeEssentialMaximumRadius_nonnegative
      distribution state factor)
  intro atom member
  by_cases zero : atom.weight = 0
  · exact Or.inl zero
  · apply Or.inr
    change _root_.FiniteMeasure.rationalSeparation
      (probe (points atom.item) - probe (process.witness atom.item)) 0 ≤ _
    rw [← _root_.FiniteMeasure.rationalSeparation_eq_sub_zero]
    calc
      _root_.FiniteMeasure.rationalSeparation
          (probe (points atom.item)) (probe (process.witness atom.item)) ≤
          factor * CCL.Chordal.chordalSq
            (points atom.item) (process.witness atom.item) := sensitive _ _
      _ ≤ factor * cylinderSpread (process.blocks state atom.item) :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          (CCL.Cylinder.Realizes.chordalSq_le_half_pow
            (pointsRealize atom member) (process.realizes state atom.item))
          factorNonnegative
      _ ≤ process.probeEssentialMaximumRadius distribution state factor :=
        process.cellRadius_le_radius distribution state factor
          factorNonnegative atom member zero

/-- The current process bound contains the essential maximum obtained from
every explicitly supplied realization family. -/
theorem probeEssentialMaximumBound_contains {ι : Type}
    (process : PrefixFamilyProcess ι)
    (distribution : _root_.FiniteMeasure.Distribution ι)
    (state : process.State) (probe : Proj → Coordinate)
    (factor : Coordinate) (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation (probe left) (probe right) ≤
        factor * CCL.Chordal.chordalSq left right)
    (points : ι → Proj)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.Realizes (process.blocks state atom.item)
        (points atom.item)) :
    _root_.FiniteMeasure.Bound.Contains
      (process.probeEssentialMaximumBound distribution state probe factor)
      (distribution.essentialMaximumMagnitude fun item =>
        probe (points item)) := by
  let actual := distribution.essentialMaximumMagnitude fun item =>
    probe (points item)
  let center := process.probeWitnessEssentialMaximum distribution probe
  let radius := process.probeEssentialMaximumRadius distribution state factor
  have separation :
      _root_.FiniteMeasure.rationalSeparation actual center ≤ radius := by
    calc
      _root_.FiniteMeasure.rationalSeparation actual center ≤
          distribution.essentialMaximumDistance
            (fun item => probe (points item))
            (fun item => probe (process.witness item)) :=
        distribution.essentialMaximumMagnitude_separation_le_distance _ _
      _ ≤ radius := process.probe_essentialMaximumDistance_le_radius
        distribution state probe factor factorNonnegative sensitive
          points pointsRealize
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

/-- Uniformly sufficient current prefixes give a requested-width current
essential-maximum enclosure. -/
theorem probeEssentialMaximumBound_width_lt_requested {ι : Type}
    (process : PrefixFamilyProcess ι)
    (distribution : _root_.FiniteMeasure.Distribution ι)
    (state : process.State) (probe : Proj → Coordinate)
    (factor : Coordinate) (factorPositive : 0 < factor)
    (sensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation (probe left) (probe right) ≤
        factor * CCL.Chordal.chordalSq left right)
    (target : Coordinate) (targetPositive : 0 < target)
    (enough : ∀ atom, atom ∈ distribution.atoms →
      requiredProbeBlockCount (target / 4) factor ≤
        (process.blocks state atom.item).length) :
    (process.probeEssentialMaximumBound distribution state probe factor).width <
      target := by
  have quarterPositive : 0 < target / 4 :=
    RFAP.ConstructiveFraction.div_pos_direct targetPositive (by decide)
  have radiusBound :
      process.probeEssentialMaximumRadius distribution state factor ≤
        target / 4 := by
    apply distribution.toFiniteContent.essentialMaximumMagnitude_le
      (fun item => factor * cylinderSpread (process.blocks state item))
      (target / 4) quarterPositive.le
    intro atom member
    by_cases zero : atom.weight = 0
    · exact Or.inl zero
    · apply Or.inr
      have cellNonnegative :
          0 ≤ factor * cylinderSpread (process.blocks state atom.item) :=
        RFAP.ConstructiveFraction.mul_nonneg_direct factorPositive.le
          (cylinderSpread_nonneg (process.blocks state atom.item))
      change _root_.FiniteMeasure.rationalSeparation
          (factor * cylinderSpread (process.blocks state atom.item)) 0 ≤
        target / 4
      rw [_root_.FiniteMeasure.rationalSeparation_zero_of_nonneg
        cellNonnegative]
      have widthSmall := completedPrefixProbeBound_width_lt_requested
        (process.witness atom.item) (process.realizes state atom.item)
        probe factor factorPositive sensitive
        (target / 4) quarterPositive (enough atom member)
      rw [completedPrefixProbeBound_width] at widthSmall
      exact (calc
          factor * cylinderSpread (process.blocks state atom.item) ≤
              2 * (factor * cylinderSpread
                (process.blocks state atom.item)) := by
            calc
              factor * cylinderSpread (process.blocks state atom.item) =
                  factor * cylinderSpread (process.blocks state atom.item) +
                    0 := by ring1
              _ ≤ factor * cylinderSpread (process.blocks state atom.item) +
                    factor * cylinderSpread
                      (process.blocks state atom.item) :=
                add_le_add le_rfl cellNonnegative
              _ = 2 * (factor * cylinderSpread
                    (process.blocks state atom.item)) := by ring1
          _ < target / 4 := widthSmall).le
  rw [process.probeEssentialMaximumBound_width]
  calc
    2 * process.probeEssentialMaximumRadius distribution state factor ≤
        2 * (target / 4) :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        radiusBound (by decide)
    _ = target / 2 := two_mul_quarter_eq_half target
    _ < target := half_lt_self targetPositive

/-- Progressive finite CCL controller for the essential maximum of one
rational probe over a fixed finite probability table. -/
def toProbeEssentialMaximumProcess {ι : Type}
    (process : PrefixFamilyProcess ι)
    (distribution : _root_.FiniteMeasure.Distribution ι)
    (probe : Proj → Coordinate) (factor : Coordinate)
    (factorPositive : 0 < factor)
    (sensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation (probe left) (probe right) ≤
        factor * CCL.Chordal.chordalSq left right) :
    _root_.FiniteMeasure.BoundProcess where
  State := process.State
  bound state :=
    process.probeEssentialMaximumBound distribution state probe factor
  initial := process.initial
  request state epsilon positive :=
    process.request state (requiredProbeBlockCount (epsilon / 4) factor)
  request_refines state epsilon positive := by
    apply process.probeEssentialMaximumBound_refines_of_extensions
      distribution _ state probe factor factorPositive.le
    intro item
    exact process.request_extends state
      (requiredProbeBlockCount (epsilon / 4) factor) item
  accurate state epsilon positive := by
    apply process.probeEssentialMaximumBound_width_lt_requested
      distribution _ probe factor factorPositive sensitive epsilon positive
    intro atom member
    exact process.request_length state
      (requiredProbeBlockCount (epsilon / 4) factor) atom.item
  refinesInitial state := by
    apply process.probeEssentialMaximumBound_refines_of_extensions
      distribution state process.initial probe factor factorPositive.le
    exact process.extendsInitial state

/-- Every explicit realization family remains in the current progressive
essential-maximum bound. -/
theorem essentialMaximum_mem_toProbeEssentialMaximumProcess_bound
    {ι : Type} (process : PrefixFamilyProcess ι)
    (distribution : _root_.FiniteMeasure.Distribution ι)
    (probe : Proj → Coordinate) (factor : Coordinate)
    (factorPositive : 0 < factor)
    (sensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation (probe left) (probe right) ≤
        factor * CCL.Chordal.chordalSq left right)
    (state : process.State) (points : ι → Proj)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.Realizes (process.blocks state atom.item)
        (points atom.item)) :
    ((process.toProbeEssentialMaximumProcess distribution probe factor
      factorPositive sensitive).bound state).Contains
        (distribution.essentialMaximumMagnitude fun item =>
          probe (points item)) :=
  process.probeEssentialMaximumBound_contains distribution state probe factor
    factorPositive.le sensitive points pointsRealize

/-- One finite request makes the progressive essential-maximum enclosure
narrower than the supplied rational tolerance. -/
theorem request_probeEssentialMaximum_width_lt {ι : Type}
    (process : PrefixFamilyProcess ι)
    (distribution : _root_.FiniteMeasure.Distribution ι)
    (probe : Proj → Coordinate) (factor : Coordinate)
    (factorPositive : 0 < factor)
    (sensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation (probe left) (probe right) ≤
        factor * CCL.Chordal.chordalSq left right)
    (state : process.State) (epsilon : Coordinate) (positive : 0 < epsilon) :
    ((process.toProbeEssentialMaximumProcess distribution probe factor
      factorPositive sensitive).bound
      ((process.toProbeEssentialMaximumProcess distribution probe factor
        factorPositive sensitive).request state epsilon positive)).width <
      epsilon :=
  (process.toProbeEssentialMaximumProcess distribution probe factor
    factorPositive sensitive).accurate state epsilon positive

end PrefixFamilyProcess

end CCL.FiniteMeasure
