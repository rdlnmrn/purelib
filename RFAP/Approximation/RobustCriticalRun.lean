import mathlib.Tactic.QuotientFreeRing
import RFAP.Approximation.CriticalRunBox
import RFAP.Approximation.RobustCriticalExterior

/-!
# Fully robust arbitrary finite critical runs

Each transported window has a positive rational squared-distance budget for
retaining its complete consecutive-best certificate.  This module takes the
finite minimum across the requested offsets and intersects the resulting box
with the existing common threshold-violation box.  The returned proper box
therefore preserves both properties for every member of the exact same-source
run.
-/

namespace RFAP.RobustCriticalRun

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev Box := RFAP.Boxes.Box
abbrev BadWindow := RFAP.DynamicalSharpness.BadWindow

open RFAP.BestApproximation

/-- The complete exterior-stability budget at one run offset. -/
def exteriorDistanceAtOffset
    (threshold : Coordinate) (requestedScale count : Nat)
    (offset : Fin count) : Coordinate :=
  let offsetBound : offset.val ≤ count := Nat.le_of_lt offset.isLt
  RFAP.RobustCriticalExterior.robustExteriorDistanceSq
    (RFAP.CriticalBadWindowRun.normalFormAtOffset threshold requestedScale
      count offset.val offsetBound)

theorem exteriorDistanceAtOffset_pos
    (threshold : Coordinate) (requestedScale count : Nat)
    (offset : Fin count) :
    0 < exteriorDistanceAtOffset threshold requestedScale count offset := by
  unfold exteriorDistanceAtOffset
  exact RFAP.RobustCriticalExterior.robustExteriorDistanceSq_pos _

def exteriorDistances
    (threshold : Coordinate) (requestedScale count : Nat) : List Coordinate :=
  List.ofFn (exteriorDistanceAtOffset threshold requestedScale count)

private def minimumPositiveDistance : List Coordinate → Coordinate
  | [] => 1
  | value :: remaining => min value (minimumPositiveDistance remaining)

private theorem minimumPositiveDistance_pos
    (values : List Coordinate) (positive : ∀ value, value ∈ values → 0 < value) :
    0 < minimumPositiveDistance values := by
  induction values with
  | nil => exact (show (0 : Coordinate) < 1 by decide)
  | cons head remaining inductionHypothesis =>
      unfold minimumPositiveDistance
      apply lt_min
      · exact positive head (List.mem_cons_self)
      · apply inductionHypothesis
        intro value member
        exact positive value (List.mem_cons_of_mem head member)

private theorem minimumPositiveDistance_le_of_mem
    {value : Coordinate} (values : List Coordinate) (member : value ∈ values) :
    minimumPositiveDistance values ≤ value := by
  induction values with
  | nil => cases member
  | cons head remaining inductionHypothesis =>
      rcases List.mem_cons.mp member with equal | tailMember
      · rw [equal]
        exact min_le_left _ _
      · exact (min_le_right _ _).trans
          (inductionHypothesis tailMember)

/-- Positive squared-distance budget shared by every requested run offset. -/
def runExteriorDistanceSq
    (threshold : Coordinate) (requestedScale count : Nat) : Coordinate :=
  minimumPositiveDistance (exteriorDistances threshold requestedScale count)

theorem runExteriorDistanceSq_pos
    (threshold : Coordinate) (requestedScale count : Nat) :
    0 < runExteriorDistanceSq threshold requestedScale count := by
  unfold runExteriorDistanceSq
  apply minimumPositiveDistance_pos
  intro value member
  rw [exteriorDistances, List.mem_ofFn] at member
  rcases member with ⟨offset, rfl⟩
  exact exteriorDistanceAtOffset_pos threshold requestedScale count offset

private theorem runExteriorDistanceSq_le_offset
    (threshold : Coordinate) (requestedScale count : Nat)
    (offset : Fin count) :
    runExteriorDistanceSq threshold requestedScale count ≤
      exteriorDistanceAtOffset threshold requestedScale count offset := by
  apply minimumPositiveDistance_le_of_mem
  rw [exteriorDistances, List.mem_ofFn]
  exact ⟨offset, rfl⟩

/-- Positive side radius whose square-box diagonal is strictly inside a
supplied positive squared-distance budget. -/
def radiusWithinDistanceSq (distanceSq : Coordinate) : Coordinate :=
  min 1 (distanceSq * (1 / 4 : Coordinate))

theorem radiusWithinDistanceSq_pos
    {distanceSq : Coordinate} (positive : 0 < distanceSq) :
    0 < radiusWithinDistanceSq distanceSq := by
  unfold radiusWithinDistanceSq
  exact lt_min (by decide)
    (RFAP.ConstructiveFraction.mul_pos_direct positive (by decide))

theorem two_mul_radiusWithinDistanceSq_sq_lt
    {distanceSq : Coordinate} (positive : 0 < distanceSq) :
    2 * radiusWithinDistanceSq distanceSq ^ 2 < distanceSq := by
  have radiusPositive := radiusWithinDistanceSq_pos positive
  have radiusLeOne : radiusWithinDistanceSq distanceSq ≤ 1 :=
    min_le_left _ _
  have squareLeRadius :
      radiusWithinDistanceSq distanceSq ^ 2 ≤
        radiusWithinDistanceSq distanceSq := by
    rw [pow_two]
    calc
      radiusWithinDistanceSq distanceSq *
          radiusWithinDistanceSq distanceSq ≤
        radiusWithinDistanceSq distanceSq * 1 :=
          RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
            radiusLeOne radiusPositive.le
      _ = radiusWithinDistanceSq distanceSq := by ring1
  have radiusLeQuarter :
      radiusWithinDistanceSq distanceSq ≤
        distanceSq * (1 / 4 : Coordinate) := min_le_right _ _
  have doubledRadiusBound :
      2 * radiusWithinDistanceSq distanceSq ≤
        distanceSq * (1 / 2 : Coordinate) := by
    calc
      2 * radiusWithinDistanceSq distanceSq ≤
          2 * (distanceSq * (1 / 4 : Coordinate)) :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          radiusLeQuarter (by decide)
      _ = distanceSq * (2 * (1 / 4 : Coordinate)) := by ring1
      _ = distanceSq * (1 / 2 : Coordinate) := by
        rw [show (2 : Coordinate) * (1 / 4) = 1 / 2 by decide]
  calc
    2 * radiusWithinDistanceSq distanceSq ^ 2 ≤
        2 * radiusWithinDistanceSq distanceSq :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        squareLeRadius (by decide)
    _ ≤ distanceSq * (1 / 2 : Coordinate) := doubledRadiusBound
    _ < distanceSq * 1 :=
      RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct positive
        (by decide)
    _ = distanceSq := by ring1

/-- Side radius obtained by intersecting the existing violation box with the
common consecutive-best neighborhood. -/
def robustRunRadius
    {threshold : Coordinate}
    (certificate :
      RFAP.FiniteWindowSharpness.IsSharperWindowThreshold threshold)
    (requestedScale count : Nat) : Coordinate :=
  let run := RFAP.CriticalBadWindowRun.criticalBadWindowRun
    certificate requestedScale count
  min (RFAP.CriticalRunBox.runBoxRadius run)
    (radiusWithinDistanceSq
      (runExteriorDistanceSq threshold requestedScale count))

theorem robustRunRadius_pos
    {threshold : Coordinate}
    (certificate :
      RFAP.FiniteWindowSharpness.IsSharperWindowThreshold threshold)
    (requestedScale count : Nat) :
    0 < robustRunRadius certificate requestedScale count := by
  unfold robustRunRadius
  exact lt_min
    (RFAP.CriticalRunBox.runBoxRadius_pos _)
    (radiusWithinDistanceSq_pos
      (runExteriorDistanceSq_pos threshold requestedScale count))

/-- One proper rational box retaining both the violations and the complete
consecutive-best status of every run window. -/
def robustRunBox
    {threshold : Coordinate}
    (certificate :
      RFAP.FiniteWindowSharpness.IsSharperWindowThreshold threshold)
    (requestedScale count : Nat) : Box :=
  let run := RFAP.CriticalBadWindowRun.criticalBadWindowRun
    certificate requestedScale count
  { xLower := run.source.value.re
    xUpper := run.source.value.re +
      robustRunRadius certificate requestedScale count
    yLower := run.source.value.im
    yUpper := run.source.value.im +
      robustRunRadius certificate requestedScale count
    x_valid := le_add_of_nonneg_right
      (robustRunRadius_pos certificate requestedScale count).le
    y_valid := le_add_of_nonneg_right
      (robustRunRadius_pos certificate requestedScale count).le }

theorem robustRunBox_proper
    {threshold : Coordinate}
    (certificate :
      RFAP.FiniteWindowSharpness.IsSharperWindowThreshold threshold)
    (requestedScale count : Nat) :
    (robustRunBox certificate requestedScale count).Proper := by
  unfold RFAP.Boxes.Box.Proper robustRunBox
  dsimp only
  constructor
  · calc
      _ = _ + 0 := by ring1
      _ < _ + robustRunRadius certificate requestedScale count :=
        RFAP.ConstructiveFraction.add_lt_add_left_direct
          (robustRunRadius_pos certificate requestedScale count) _
  · calc
      _ = _ + 0 := by ring1
      _ < _ + robustRunRadius certificate requestedScale count :=
        RFAP.ConstructiveFraction.add_lt_add_left_direct
          (robustRunRadius_pos certificate requestedScale count) _

@[simp] theorem robustRunBox_anchor
    {threshold : Coordinate}
    (certificate :
      RFAP.FiniteWindowSharpness.IsSharperWindowThreshold threshold)
    (requestedScale count : Nat) :
    (robustRunBox certificate requestedScale count).anchor =
      (RFAP.CriticalBadWindowRun.criticalBadWindowRun
        certificate requestedScale count).source.value := by
  apply RFAP.ConstructiveGaussian.Gaussian.ext <;> rfl

private theorem robustRunBox_diagonalSq
    {threshold : Coordinate}
    (certificate :
      RFAP.FiniteWindowSharpness.IsSharperWindowThreshold threshold)
    (requestedScale count : Nat) :
    (robustRunBox certificate requestedScale count).diagonalSq =
      2 * robustRunRadius certificate requestedScale count ^ 2 := by
  unfold robustRunBox RFAP.Boxes.Box.diagonalSq
  ring1

private theorem robustRunRadius_le_exteriorRadius
    {threshold : Coordinate}
    (certificate :
      RFAP.FiniteWindowSharpness.IsSharperWindowThreshold threshold)
    (requestedScale count : Nat) :
    robustRunRadius certificate requestedScale count ≤
      radiusWithinDistanceSq
        (runExteriorDistanceSq threshold requestedScale count) := by
  unfold robustRunRadius
  exact min_le_right _ _

private theorem robustRunBox_distance_lt_offset
    {threshold : Coordinate}
    (certificate :
      RFAP.FiniteWindowSharpness.IsSharperWindowThreshold threshold)
    (requestedScale count : Nat) (sample : Gaussian)
    (inside : (robustRunBox certificate requestedScale count).Contains sample)
    (offset : Fin count) :
    RFAP.ConstructiveGaussian.Gaussian.normSq
        (sample -
          (RFAP.CriticalBadWindowRun.criticalBadWindowRun
            certificate requestedScale count).source.value) <
      exteriorDistanceAtOffset threshold requestedScale count offset := by
  let exteriorRadius := radiusWithinDistanceSq
    (runExteriorDistanceSq threshold requestedScale count)
  have radiusLe : robustRunRadius certificate requestedScale count ≤
      exteriorRadius := by
    simpa only [exteriorRadius] using
      robustRunRadius_le_exteriorRadius certificate requestedScale count
  have radiusNonnegative :=
    (robustRunRadius_pos certificate requestedScale count).le
  have exteriorRadiusNonnegative :=
    (radiusWithinDistanceSq_pos
      (runExteriorDistanceSq_pos threshold requestedScale count)).le
  have squareLe : robustRunRadius certificate requestedScale count ^ 2 ≤
      exteriorRadius ^ 2 :=
    RFAP.ConstructiveFraction.pow_le_pow_direct radiusNonnegative radiusLe 2
  calc
    RFAP.ConstructiveGaussian.Gaussian.normSq
        (sample -
          (RFAP.CriticalBadWindowRun.criticalBadWindowRun
            certificate requestedScale count).source.value) =
      RFAP.ConstructiveGaussian.Gaussian.normSq
        (sample - (robustRunBox certificate requestedScale count).anchor) := by
          rw [robustRunBox_anchor]
    _ ≤ (robustRunBox certificate requestedScale count).diagonalSq :=
      (robustRunBox certificate requestedScale count).normSq_sub_anchor_le
        inside
    _ = 2 * robustRunRadius certificate requestedScale count ^ 2 :=
      robustRunBox_diagonalSq certificate requestedScale count
    _ ≤ 2 * exteriorRadius ^ 2 :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct squareLe
        (by decide)
    _ < runExteriorDistanceSq threshold requestedScale count := by
      simpa only [exteriorRadius] using
        two_mul_radiusWithinDistanceSq_sq_lt
          (runExteriorDistanceSq_pos threshold requestedScale count)
    _ ≤ exteriorDistanceAtOffset threshold requestedScale count offset :=
      runExteriorDistanceSq_le_offset threshold requestedScale count offset

theorem robustRunBox_consecutiveAtOffset
    {threshold : Coordinate}
    (certificate :
      RFAP.FiniteWindowSharpness.IsSharperWindowThreshold threshold)
    (requestedScale count : Nat) (sample : Gaussian)
    (inside : (robustRunBox certificate requestedScale count).Contains sample)
    (offset : Fin count) :
    AreConsecutiveBest sample
      (RFAP.CriticalBadWindowRun.badWindowAtOffset
        certificate requestedScale count offset).1.lower
      (RFAP.CriticalBadWindowRun.badWindowAtOffset
        certificate requestedScale count offset).1.upper := by
  let offsetBound : offset.val ≤ count := Nat.le_of_lt offset.isLt
  let normal := RFAP.CriticalBadWindowRun.normalFormAtOffset threshold
    requestedScale count offset.val offsetBound
  apply RFAP.RobustCriticalExterior.transportedPairs_areConsecutiveBest_of_distance
    normal sample
  simpa only [normal, exteriorDistanceAtOffset, offsetBound,
    RFAP.CriticalBadWindowRun.criticalBadWindowRun_source] using
    robustRunBox_distance_lt_offset certificate requestedScale count sample
      inside offset

private theorem robustRunRadius_le_violationRadius
    {threshold : Coordinate}
    (certificate :
      RFAP.FiniteWindowSharpness.IsSharperWindowThreshold threshold)
    (requestedScale count : Nat) :
    robustRunRadius certificate requestedScale count ≤
      RFAP.CriticalRunBox.runBoxRadius
        (RFAP.CriticalBadWindowRun.criticalBadWindowRun
          certificate requestedScale count) := by
  unfold robustRunRadius
  exact min_le_left _ _

private theorem robustRunBox_refinesViolationBox
    {threshold : Coordinate}
    (certificate :
      RFAP.FiniteWindowSharpness.IsSharperWindowThreshold threshold)
    (requestedScale count : Nat) :
    (robustRunBox certificate requestedScale count).Refines
      (RFAP.CriticalRunBox.runViolationBox
        (RFAP.CriticalBadWindowRun.criticalBadWindowRun
          certificate requestedScale count)) := by
  let run := RFAP.CriticalBadWindowRun.criticalBadWindowRun
    certificate requestedScale count
  unfold RFAP.Boxes.Box.Refines robustRunBox
    RFAP.CriticalRunBox.runViolationBox
  dsimp only [run]
  have radiusBound :=
    robustRunRadius_le_violationRadius certificate requestedScale count
  let center := (RFAP.CriticalBadWindowRun.criticalBadWindowRun
    certificate requestedScale count).source.value
  have realUpper : center.re + robustRunRadius certificate requestedScale count ≤
      center.re + RFAP.CriticalRunBox.runBoxRadius
        (RFAP.CriticalBadWindowRun.criticalBadWindowRun
          certificate requestedScale count) := by
    calc
      _ = robustRunRadius certificate requestedScale count + center.re := by
        ring1
      _ ≤ RFAP.CriticalRunBox.runBoxRadius
          (RFAP.CriticalBadWindowRun.criticalBadWindowRun
            certificate requestedScale count) + center.re :=
        add_le_add_left radiusBound center.re
      _ = _ := by ring1
  have imaginaryUpper :
      center.im + robustRunRadius certificate requestedScale count ≤
        center.im + RFAP.CriticalRunBox.runBoxRadius
          (RFAP.CriticalBadWindowRun.criticalBadWindowRun
            certificate requestedScale count) := by
    calc
      _ = robustRunRadius certificate requestedScale count + center.im := by
        ring1
      _ ≤ RFAP.CriticalRunBox.runBoxRadius
          (RFAP.CriticalBadWindowRun.criticalBadWindowRun
            certificate requestedScale count) + center.im :=
        add_le_add_left radiusBound center.im
      _ = _ := by ring1
  exact ⟨le_rfl, realUpper, le_rfl, imaginaryUpper⟩

/-- Every window in the exact run remains consecutive best throughout the
common robust box. -/
theorem robustRunBox_uniformConsecutive
    {threshold : Coordinate}
    (certificate :
      RFAP.FiniteWindowSharpness.IsSharperWindowThreshold threshold)
    (requestedScale count : Nat) (sample : Gaussian)
    (inside : (robustRunBox certificate requestedScale count).Contains sample)
    (window : { window : BadWindow threshold requestedScale //
      window.source =
        (RFAP.CriticalBadWindowRun.criticalBadWindowRun
          certificate requestedScale count).source })
    (member : window ∈
      (RFAP.CriticalBadWindowRun.criticalBadWindowRun
        certificate requestedScale count).windows) :
    AreConsecutiveBest sample window.1.lower window.1.upper := by
  unfold RFAP.CriticalBadWindowRun.criticalBadWindowRun at member
  rw [List.mem_ofFn] at member
  rcases member with ⟨offset, equal⟩
  rw [← equal]
  exact robustRunBox_consecutiveAtOffset certificate requestedScale count
    sample inside offset

/-- Every window's strict threshold violation also persists throughout the
same common robust box. -/
theorem robustRunBox_uniformViolation
    {threshold : Coordinate}
    (certificate :
      RFAP.FiniteWindowSharpness.IsSharperWindowThreshold threshold)
    (requestedScale count : Nat) (sample : Gaussian)
    (inside : (robustRunBox certificate requestedScale count).Contains sample)
    (window : { window : BadWindow threshold requestedScale //
      window.source =
        (RFAP.CriticalBadWindowRun.criticalBadWindowRun
          certificate requestedScale count).source })
    (member : window ∈
      (RFAP.CriticalBadWindowRun.criticalBadWindowRun
        certificate requestedScale count).windows) :
    1 < threshold * dirichletWindowQuadrance sample
      window.1.lower window.1.upper := by
  apply RFAP.CriticalRunBox.runViolationBox_uniform
    (RFAP.CriticalBadWindowRun.criticalBadWindowRun
      certificate requestedScale count) sample
  · exact (robustRunBox_refinesViolationBox certificate requestedScale count).contains
      inside
  · exact member

/-- Offset-indexed form of the common threshold-violation theorem. -/
theorem robustRunBox_violationAtOffset
    {threshold : Coordinate}
    (certificate :
      RFAP.FiniteWindowSharpness.IsSharperWindowThreshold threshold)
    (requestedScale count : Nat) (sample : Gaussian)
    (inside : (robustRunBox certificate requestedScale count).Contains sample)
    (offset : Fin count) :
    1 < threshold * dirichletWindowQuadrance sample
      (RFAP.CriticalBadWindowRun.badWindowAtOffset
        certificate requestedScale count offset).1.lower
      (RFAP.CriticalBadWindowRun.badWindowAtOffset
        certificate requestedScale count offset).1.upper := by
  apply robustRunBox_uniformViolation certificate requestedScale count
    sample inside
    (RFAP.CriticalBadWindowRun.badWindowAtOffset
      certificate requestedScale count offset)
  unfold RFAP.CriticalBadWindowRun.criticalBadWindowRun
  rw [List.mem_ofFn]
  exact ⟨offset, rfl⟩

/-- Returned arbitrary-length robust run certificate. -/
structure FullyRobustRun
    (threshold : Coordinate) (requestedScale count : Nat) where
  exact : RFAP.CriticalBadWindowRun.SameSourceBadWindowRun
    threshold requestedScale count
  box : Box
  proper : box.Proper
  sourceAtAnchor : box.anchor = exact.source.value
  uniformConsecutive : ∀ sample : Gaussian, box.Contains sample →
    ∀ window, window ∈ exact.windows →
      AreConsecutiveBest sample window.1.lower window.1.upper
  uniformViolation : ∀ sample : Gaussian, box.Contains sample →
    ∀ window, window ∈ exact.windows →
      1 < threshold * dirichletWindowQuadrance sample
        window.1.lower window.1.upper

/-- For every sharper rational threshold, requested scale, and finite count,
construct exactly that many same-source bad windows and one proper rational
box on which all of them remain genuine consecutive-best violations. -/
def criticalFullyRobustRun
    {threshold : Coordinate}
    (certificate :
      RFAP.FiniteWindowSharpness.IsSharperWindowThreshold threshold)
    (requestedScale count : Nat) :
    FullyRobustRun threshold requestedScale count := by
  let run := RFAP.CriticalBadWindowRun.criticalBadWindowRun
    certificate requestedScale count
  exact
    { exact := run
      box := robustRunBox certificate requestedScale count
      proper := robustRunBox_proper certificate requestedScale count
      sourceAtAnchor := robustRunBox_anchor certificate requestedScale count
      uniformConsecutive := fun sample inside window member =>
        robustRunBox_uniformConsecutive certificate requestedScale count
          sample inside window member
      uniformViolation := fun sample inside window member =>
        robustRunBox_uniformViolation certificate requestedScale count
          sample inside window member }

end RFAP.RobustCriticalRun
