module
import Purelib.Data.List.OfFn.Basic
import Purelib.Data.List.Membership
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.NumberTheory.Approximation.Best.Consecutive.Basic
public import Purelib.NumberTheory.Approximation.Dirichlet.Critical.Robust.Exterior
public import Purelib.NumberTheory.Approximation.Dirichlet.Critical.Robust.Violation
import Purelib.NumberTheory.Approximation.Dirichlet.Critical.Run
import Purelib.NumberTheory.Approximation.Dirichlet.Critical.Sharpness
import Purelib.NumberTheory.Approximation.Dirichlet.Sharpness.BadWindow
import Purelib.NumberTheory.Approximation.Dirichlet.Window.SourceBound
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.GaussianInt.Fraction.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.NumberTheory.Approximation.Dirichlet.Critical.Adjacent.Tower
import Purelib.NumberTheory.Approximation.Dirichlet.Critical.Pair
import Purelib.Tactic.Ring

open Purelib.Data.Rat.Fraction.Order

open Purelib.Data

open Purelib.Data.Rat

open Purelib

open Purelib.NumberTheory.Approximation

section
public section

/-!
# Fully robust arbitrary finite critical runs

Each transported window has a positive rational squared-distance budget for
retaining its complete consecutive-best certificate.  This module takes the
finite minimum across the requested offsets and intersects the resulting box
with the existing common threshold-violation box.  The returned proper box
therefore preserves both properties for every member of the exact same-source
run.
-/

namespace Purelib.NumberTheory.Approximation.Dirichlet.Critical.Robust.Run

/-- The complete exterior-stability budget at one run offset. -/
@[expose] def exteriorDistanceAtOffset
    (threshold : Fraction.Rational) (requestedScale count : Nat)
    (offset : Fin count) : Fraction.Rational :=
  let offsetBound : offset.val ≤ count := Nat.le_of_lt offset.isLt
  Exterior.robustExteriorDistanceSq
    (Run.normalFormAtOffset threshold requestedScale
      count offset.val offsetBound)

/-- The complete exterior-stability distance budget at each bounded run offset is positive. -/
theorem exteriorDistanceAtOffset_pos
    (threshold : Fraction.Rational) (requestedScale count : Nat)
    (offset : Fin count) :
    0 < exteriorDistanceAtOffset threshold requestedScale count offset := by
  unfold exteriorDistanceAtOffset
  exact Exterior.robustExteriorDistanceSq_pos _

/-- The ordered list of complete exterior-stability budgets for all bounded run offsets. -/
@[expose] def exteriorDistances
    (threshold : Fraction.Rational) (requestedScale count : Nat) : List Fraction.Rational :=
  List.ofFn (exteriorDistanceAtOffset threshold requestedScale count)

/-- The recursive minimum of a rational list, capped by one and equal to one on the empty list. -/
private def minimumPositiveDistance : List Fraction.Rational → Fraction.Rational
  | [] => 1
  | value :: remaining => min value
    (Run.minimumPositiveDistance remaining)

/-- The exposed finite minimum used for a run-wide distance budget.

It returns one for an empty list and takes successive minima for nonempty lists; positivity follows separately when
every entry is positive. -/
@[expose] def minimumRunPositiveDistance : List Fraction.Rational → Fraction.Rational
  | [] => 1
  | value :: remaining => min value
    (Run.minimumRunPositiveDistance remaining)

/-- The exposed run-minimum computation agrees with the private recursive minimum. -/
private theorem minimumRunPositiveDistance_eq (values : List Fraction.Rational) :
    minimumRunPositiveDistance values =
      minimumPositiveDistance values := by
  induction values with
  | nil => rfl
  | cons head remaining ih =>
      change min head (minimumRunPositiveDistance remaining) =
        min head (minimumPositiveDistance remaining)
      rw [ih]

/-- A finite list of positive rational distances has a positive capped minimum. -/
private theorem minimumPositiveDistance_pos
    (values : List Fraction.Rational) (positive : ∀ value, value ∈ values → 0 < value) :
    0 < minimumPositiveDistance values := by
  induction values with
  | nil => exact (show (0 : Fraction.Rational) < 1 by decide)
  | cons head remaining inductionHypothesis =>
      unfold minimumPositiveDistance
      apply Basic.lt_min
      · exact positive head (List.mem_cons_self)
      · apply inductionHypothesis
        intro value member
        exact positive value (List.mem_cons_of_mem head member)

/-- The capped finite minimum is bounded by each list member. -/
private theorem minimumPositiveDistance_le_of_mem
    {value : Fraction.Rational} (values : List Fraction.Rational) (member : value ∈ values) :
    minimumPositiveDistance values ≤ value := by
  induction values with
  | nil => cases member
  | cons head remaining inductionHypothesis =>
      rcases Data.List.Membership.mem_cons.mp member with equal | tailMember
      · rw [equal]
        exact Basic.min_le_left _ _
      · exact (Basic.min_le_right _ _).trans
          (inductionHypothesis tailMember)

/-- Positive squared-distance budget shared by every requested run offset. -/
@[expose] def runExteriorDistanceSq
    (threshold : Fraction.Rational) (requestedScale count : Nat) : Fraction.Rational :=
  minimumRunPositiveDistance (exteriorDistances threshold
    requestedScale count)

/-- The shared exterior-stability distance budget is positive for every finite run length. -/
theorem runExteriorDistanceSq_pos
    (threshold : Fraction.Rational) (requestedScale count : Nat) :
    0 < runExteriorDistanceSq threshold requestedScale count := by
  unfold runExteriorDistanceSq
  rw [minimumRunPositiveDistance_eq]
  apply minimumPositiveDistance_pos
  intro value member
  unfold exteriorDistances at member
  have member := Data.List.OfFn.Basic.mem_ofFn.mp member
  rcases member with ⟨offset, rfl⟩
  exact exteriorDistanceAtOffset_pos threshold requestedScale count offset

/-- The shared distance budget is no larger than the budget at any bounded run offset. -/
private theorem runExteriorDistanceSq_le_offset
    (threshold : Fraction.Rational) (requestedScale count : Nat)
    (offset : Fin count) :
    runExteriorDistanceSq threshold requestedScale count ≤
      exteriorDistanceAtOffset threshold requestedScale count offset := by
  unfold runExteriorDistanceSq
  rw [minimumRunPositiveDistance_eq]
  apply minimumPositiveDistance_le_of_mem
  unfold exteriorDistances
  exact Data.List.OfFn.Basic.mem_ofFn.mpr ⟨offset, rfl⟩

/-- Positive side radius whose square-box diagonal is strictly inside a
supplied positive squared-distance budget. -/
@[expose] def radiusWithinDistanceSq (distanceSq : Fraction.Rational) : Fraction.Rational :=
  min 1 (distanceSq * (1 / 4 : Fraction.Rational))

/-- A positive squared-distance budget gives a positive selected box side length. -/
theorem radiusWithinDistanceSq_pos
    {distanceSq : Fraction.Rational} (positive : 0 < distanceSq) :
    0 < radiusWithinDistanceSq distanceSq := by
  unfold radiusWithinDistanceSq
  exact Basic.lt_min (by decide)
    (Arithmetic.mul_pos_direct positive (by decide))

/-- The selected square-box diagonal quadrance is strictly smaller than its positive distance budget. -/
theorem two_mul_radiusWithinDistanceSq_sq_lt
    {distanceSq : Fraction.Rational} (positive : 0 < distanceSq) :
    2 * radiusWithinDistanceSq distanceSq ^ 2 < distanceSq := by
  have radiusPositive := radiusWithinDistanceSq_pos positive
  have radiusLeOne : radiusWithinDistanceSq distanceSq ≤ 1 :=
    Basic.min_le_left _ _
  have squareLeRadius :
      radiusWithinDistanceSq distanceSq ^ 2 ≤
        radiusWithinDistanceSq distanceSq := by
    rw [pow_two]
    calc
      radiusWithinDistanceSq distanceSq *
          radiusWithinDistanceSq distanceSq ≤
        radiusWithinDistanceSq distanceSq * 1 :=
          Arithmetic.mul_le_mul_of_nonneg_left_direct
            radiusLeOne radiusPositive.le
      _ = radiusWithinDistanceSq distanceSq := by ring1
  have radiusLeQuarter :
      radiusWithinDistanceSq distanceSq ≤
        distanceSq * (1 / 4 : Fraction.Rational) := Basic.min_le_right _ _
  have doubledRadiusBound :
      2 * radiusWithinDistanceSq distanceSq ≤
        distanceSq * (1 / 2 : Fraction.Rational) := by
    calc
      2 * radiusWithinDistanceSq distanceSq ≤
          2 * (distanceSq * (1 / 4 : Fraction.Rational)) :=
        Arithmetic.mul_le_mul_of_nonneg_left_direct
          radiusLeQuarter (by decide)
      _ = distanceSq * (2 * (1 / 4 : Fraction.Rational)) := by ring1
      _ = distanceSq * (1 / 2 : Fraction.Rational) := by
        rw [show (2 : Fraction.Rational) * (1 / 4) = 1 / 2 by decide]
  calc
    2 * radiusWithinDistanceSq distanceSq ^ 2 ≤
        2 * radiusWithinDistanceSq distanceSq :=
      Arithmetic.mul_le_mul_of_nonneg_left_direct
        squareLeRadius (by decide)
    _ ≤ distanceSq * (1 / 2 : Fraction.Rational) := doubledRadiusBound
    _ < distanceSq * 1 :=
      Arithmetic.mul_lt_mul_of_pos_left_direct positive
        (by decide)
    _ = distanceSq := by ring1

/-- Side radius obtained by intersecting the existing violation box with the
common consecutive-best neighborhood. -/
@[expose] def robustRunRadius
    {threshold : Fraction.Rational}
    (certificate :
      Sharpness.IsSharperWindowThreshold threshold)
    (requestedScale count : Nat) : Fraction.Rational :=
  let run := Run.criticalBadWindowRun
    certificate requestedScale count
  min (Violation.runBoxRadius run)
    (radiusWithinDistanceSq
      (runExteriorDistanceSq threshold requestedScale count))

/-- The intersection radius preserving both exclusion and violation is positive. -/
theorem robustRunRadius_pos
    {threshold : Fraction.Rational}
    (certificate :
      Sharpness.IsSharperWindowThreshold threshold)
    (requestedScale count : Nat) :
    0 < robustRunRadius certificate requestedScale count := by
  unfold robustRunRadius
  exact Basic.lt_min
    (Violation.runBoxRadius_pos _)
    (radiusWithinDistanceSq_pos
      (runExteriorDistanceSq_pos threshold requestedScale count))

/-- One proper rational box retaining both the violations and the complete
consecutive-best status of every run window. -/
@[expose] def robustRunBox
    {threshold : Fraction.Rational}
    (certificate :
      Sharpness.IsSharperWindowThreshold threshold)
    (requestedScale count : Nat) : Geometry.Rational.Box :=
  let run := Run.criticalBadWindowRun
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

/-- The common robust run box has strictly positive width and height. -/
theorem robustRunBox_proper
    {threshold : Fraction.Rational}
    (certificate :
      Sharpness.IsSharperWindowThreshold threshold)
    (requestedScale count : Nat) :
    (robustRunBox certificate requestedScale count).Proper := by
  unfold Geometry.Rational.Box.Proper robustRunBox
  dsimp only
  constructor
  · calc
      _ = _ + 0 := by ring1
      _ < _ + robustRunRadius certificate requestedScale count :=
        Arithmetic.add_lt_add_left_direct
          (robustRunRadius_pos certificate requestedScale count) _
  · calc
      _ = _ + 0 := by ring1
      _ < _ + robustRunRadius certificate requestedScale count :=
        Arithmetic.add_lt_add_left_direct
          (robustRunRadius_pos certificate requestedScale count) _

/-- The robust run box is anchored at the exact retained run source. -/
@[simp] theorem robustRunBox_anchor
    {threshold : Fraction.Rational}
    (certificate :
      Sharpness.IsSharperWindowThreshold threshold)
    (requestedScale count : Nat) :
    (robustRunBox certificate requestedScale count).anchor =
      (Run.criticalBadWindowRun
        certificate requestedScale count).source.value := by
  apply Gaussian.Basic.ext <;> rfl

/-- The robust run box diagonal quadrance is twice the square of its side length. -/
private theorem robustRunBox_diagonalSq
    {threshold : Fraction.Rational}
    (certificate :
      Sharpness.IsSharperWindowThreshold threshold)
    (requestedScale count : Nat) :
    (robustRunBox certificate requestedScale count).diagonalSq =
      2 * robustRunRadius certificate requestedScale count ^ 2 := by
  rewrite [Geometry.Rational.Box.diagonalSq_eq_original]
  unfold robustRunBox
  ring1

/-- The common robust radius is bounded by the radius selected from the exterior-stability budget. -/
private theorem robustRunRadius_le_exteriorRadius
    {threshold : Fraction.Rational}
    (certificate :
      Sharpness.IsSharperWindowThreshold threshold)
    (requestedScale count : Nat) :
    robustRunRadius certificate requestedScale count ≤
      radiusWithinDistanceSq
        (runExteriorDistanceSq threshold requestedScale count) := by
  unfold robustRunRadius
  exact Basic.min_le_right _ _

/-- Every sample in the robust box lies strictly within each offset-specific exterior budget.

The box diagonal bounds source displacement, and the common finite minimum is bounded by the chosen offset budget. -/
private theorem robustRunBox_distance_lt_offset
    {threshold : Fraction.Rational}
    (certificate :
      Sharpness.IsSharperWindowThreshold threshold)
    (requestedScale count : Nat) (sample : Gaussian.Basic.Canonical)
    (inside : (robustRunBox certificate requestedScale count).Contains sample)
    (offset : Fin count) :
    Gaussian.Norm.Basic.normSq
        (sample -
          (Run.criticalBadWindowRun
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
    Arithmetic.pow_le_pow_direct radiusNonnegative radiusLe 2
  calc
    Gaussian.Norm.Basic.normSq
        (sample -
          (Run.criticalBadWindowRun
            certificate requestedScale count).source.value) =
      Gaussian.Norm.Basic.normSq
        (sample - (robustRunBox certificate requestedScale count).anchor) := by
          rw [robustRunBox_anchor]
    _ ≤ (robustRunBox certificate requestedScale count).diagonalSq :=
      (robustRunBox certificate requestedScale count).normSq_sub_anchor_le
        inside
    _ = 2 * robustRunRadius certificate requestedScale count ^ 2 :=
      robustRunBox_diagonalSq certificate requestedScale count
    _ ≤ 2 * exteriorRadius ^ 2 :=
      Arithmetic.mul_le_mul_of_nonneg_left_direct squareLe
        (by decide)
    _ < runExteriorDistanceSq threshold requestedScale count := by
      simpa only [exteriorRadius] using
        two_mul_radiusWithinDistanceSq_sq_lt
          (runExteriorDistanceSq_pos threshold requestedScale count)
    _ ≤ exteriorDistanceAtOffset threshold requestedScale count offset :=
      runExteriorDistanceSq_le_offset threshold requestedScale count offset

/-- The offset window remains consecutive best at every sample inside the common robust box. -/
theorem robustRunBox_consecutiveAtOffset
    {threshold : Fraction.Rational}
    (certificate :
      Sharpness.IsSharperWindowThreshold threshold)
    (requestedScale count : Nat) (sample : Gaussian.Basic.Canonical)
    (inside : (robustRunBox certificate requestedScale count).Contains sample)
    (offset : Fin count) :
    Best.Consecutive.Basic.AreConsecutiveBest sample
      (Run.badWindowAtOffset
        certificate requestedScale count offset).1.lower
      (Run.badWindowAtOffset
        certificate requestedScale count offset).1.upper := by
  let offsetBound : offset.val ≤ count := Nat.le_of_lt offset.isLt
  let normal := Run.normalFormAtOffset threshold
    requestedScale count offset.val offsetBound
  apply Exterior.transportedPairs_areConsecutiveBest_of_distance
    normal sample
  simpa only [normal, exteriorDistanceAtOffset, offsetBound,
    Run.criticalBadWindowRun_source] using
    robustRunBox_distance_lt_offset certificate requestedScale count sample
      inside offset

/-- The common robust radius is bounded by the run-wide violation radius. -/
private theorem robustRunRadius_le_violationRadius
    {threshold : Fraction.Rational}
    (certificate :
      Sharpness.IsSharperWindowThreshold threshold)
    (requestedScale count : Nat) :
    robustRunRadius certificate requestedScale count ≤
      Violation.runBoxRadius
        (Run.criticalBadWindowRun
          certificate requestedScale count) := by
  unfold robustRunRadius
  exact Basic.min_le_left _ _

/-- The common robust box refines the run-wide violation box.

Both boxes retain the same exact source anchor, and the robust radius is bounded by the violation radius. -/
private theorem robustRunBox_refinesViolationBox
    {threshold : Fraction.Rational}
    (certificate :
      Sharpness.IsSharperWindowThreshold threshold)
    (requestedScale count : Nat) :
    (robustRunBox certificate requestedScale count).Refines
      (Violation.runViolationBox
        (Run.criticalBadWindowRun
          certificate requestedScale count)) := by
  let run := Run.criticalBadWindowRun
    certificate requestedScale count
  unfold Geometry.Rational.Box.Refines robustRunBox
    Violation.runViolationBox
  dsimp only [run]
  have radiusBound :=
    robustRunRadius_le_violationRadius certificate requestedScale count
  let center := (Run.criticalBadWindowRun
    certificate requestedScale count).source.value
  have realUpper : center.re + robustRunRadius certificate requestedScale count ≤
      center.re + Violation.runBoxRadius
        (Run.criticalBadWindowRun
          certificate requestedScale count) := by
    calc
      _ = robustRunRadius certificate requestedScale count + center.re := by
        ring1
      _ ≤ Violation.runBoxRadius
          (Run.criticalBadWindowRun
            certificate requestedScale count) + center.re :=
        add_le_add_left radiusBound center.re
      _ = _ := by ring1
  have imaginaryUpper :
      center.im + robustRunRadius certificate requestedScale count ≤
        center.im + Violation.runBoxRadius
          (Run.criticalBadWindowRun
            certificate requestedScale count) := by
    calc
      _ = robustRunRadius certificate requestedScale count + center.im := by
        ring1
      _ ≤ Violation.runBoxRadius
          (Run.criticalBadWindowRun
            certificate requestedScale count) + center.im :=
        add_le_add_left radiusBound center.im
      _ = _ := by ring1
  exact ⟨le_rfl, realUpper, le_rfl, imaginaryUpper⟩

/-- Every window in the exact run remains consecutive best throughout the
common robust box. -/
theorem robustRunBox_uniformConsecutive
    {threshold : Fraction.Rational}
    (certificate :
      Sharpness.IsSharperWindowThreshold threshold)
    (requestedScale count : Nat) (sample : Gaussian.Basic.Canonical)
    (inside : (robustRunBox certificate requestedScale count).Contains sample)
    (window : { window : Sharpness.BadWindow threshold requestedScale //
      window.source =
        (Run.criticalBadWindowRun
          certificate requestedScale count).source })
    (member : window ∈
      (Run.criticalBadWindowRun
        certificate requestedScale count).windows) :
    Best.Consecutive.Basic.AreConsecutiveBest sample window.1.lower window.1.upper := by
  unfold Run.criticalBadWindowRun at member
  have member := Data.List.OfFn.Basic.mem_ofFn.mp member
  rcases member with ⟨offset, equal⟩
  rw [← equal]
  exact robustRunBox_consecutiveAtOffset certificate requestedScale count
    sample inside offset

/-- Every window's strict threshold violation also persists throughout the
same common robust box. -/
theorem robustRunBox_uniformViolation
    {threshold : Fraction.Rational}
    (certificate :
      Sharpness.IsSharperWindowThreshold threshold)
    (requestedScale count : Nat) (sample : Gaussian.Basic.Canonical)
    (inside : (robustRunBox certificate requestedScale count).Contains sample)
    (window : { window : Sharpness.BadWindow threshold requestedScale //
      window.source =
        (Run.criticalBadWindowRun
          certificate requestedScale count).source })
    (member : window ∈
      (Run.criticalBadWindowRun
        certificate requestedScale count).windows) :
    1 < threshold * Window.SourceBound.dirichletWindowQuadrance sample
      window.1.lower window.1.upper := by
  apply Violation.runViolationBox_uniform
    (Run.criticalBadWindowRun
      certificate requestedScale count) sample
  · exact (robustRunBox_refinesViolationBox certificate requestedScale count).contains
      inside
  · exact member

/-- Offset-indexed form of the common threshold-violation theorem. -/
theorem robustRunBox_violationAtOffset
    {threshold : Fraction.Rational}
    (certificate :
      Sharpness.IsSharperWindowThreshold threshold)
    (requestedScale count : Nat) (sample : Gaussian.Basic.Canonical)
    (inside : (robustRunBox certificate requestedScale count).Contains sample)
    (offset : Fin count) :
    1 < threshold * Window.SourceBound.dirichletWindowQuadrance sample
      (Run.badWindowAtOffset
        certificate requestedScale count offset).1.lower
      (Run.badWindowAtOffset
        certificate requestedScale count offset).1.upper := by
  apply robustRunBox_uniformViolation certificate requestedScale count
    sample inside
    (Run.badWindowAtOffset
      certificate requestedScale count offset)
  unfold Run.criticalBadWindowRun
  apply Data.List.OfFn.Basic.mem_ofFn.mpr
  exact ⟨offset, rfl⟩

set_option genInjectivity false in
/-- A finite same-source bad-window run with a common proper rational stability box.

The certificate retains the original windows and proves both consecutive-best status and threshold violation uniformly
throughout the displayed box. -/
structure FullyRobustRun
    (threshold : Fraction.Rational) (requestedScale count : Nat) where
  /-- The exact same-source bad-window run with its retained windows, count and strict scale growth. -/ exact :
    Run.SameSourceBadWindowRun
    threshold requestedScale count
  /-- The shared rational box preserving consecutive-best status and threshold violations. -/ box :
    Geometry.Rational.Box
  /-- The common robust box has strictly positive width and height. -/ proper : box.Proper
  /-- The box anchor is exactly the retained run source. -/ sourceAtAnchor : box.anchor = exact.source.value
  /-- Every retained window remains consecutive best at every sample inside the box. -/ uniformConsecutive : ∀ sample :
    Gaussian.Basic.Canonical, box.Contains sample →
    ∀ window, window ∈ exact.windows →
      Best.Consecutive.Basic.AreConsecutiveBest sample window.1.lower window.1.upper
  /-- Every retained window violates the threshold inequality at every sample inside the box. -/ uniformViolation : ∀
    sample : Gaussian.Basic.Canonical, box.Contains sample →
    ∀ window, window ∈ exact.windows →
      1 < threshold * Window.SourceBound.dirichletWindowQuadrance sample
        window.1.lower window.1.upper

constructive_injectivity FullyRobustRun

/-- For every sharper rational threshold, requested scale, and finite count,
construct exactly that many same-source bad windows and one proper rational
box on which all of them remain genuine consecutive-best violations. -/
@[expose] def criticalFullyRobustRun
    {threshold : Fraction.Rational}
    (certificate :
      Sharpness.IsSharperWindowThreshold threshold)
    (requestedScale count : Nat) :
    FullyRobustRun threshold requestedScale count := by
  let run := Run.criticalBadWindowRun
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

end Purelib.NumberTheory.Approximation.Dirichlet.Critical.Robust.Run

end
