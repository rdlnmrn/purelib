module

public import Purelib.NumberTheory.Approximation.Dirichlet.Critical.Run.Placement
public import Purelib.NumberTheory.Approximation.Dirichlet.Critical.Robust.Violation
public import Purelib.NumberTheory.Approximation.Best.Cylinder.Stability
public import Purelib.Data.Rat.List.Minimum
import Purelib.Data.Rat.Fraction.Order.Arithmetic

/-!
# Proper robust neighbourhoods of placed critical runs

One retained homographic placement supplies the exact source and all window
pairs. A finite minimum of their complete-cylinder and violation clearances
determines a proper neighbourhood strictly inside the original box. Every
cached window keeps both certificates throughout that same neighbourhood.
-/

public section

namespace Purelib.NumberTheory.Approximation.Dirichlet.Critical.Robust

open Purelib.Data
open Purelib.Data.Rat
open Purelib.Geometry.Rational
open Purelib.NumberTheory.Approximation
open Purelib.NumberTheory.Approximation.Dirichlet.Critical

/-- Compute the shared complete-cylinder and strict-violation clearance for one actual cached window. -/
def windowClearance {center : GaussianInt.Fraction.Reduced} {threshold : Fraction.Rational}
    {certificate : Sharpness.IsSharperWindowThreshold threshold} {requestedScale count : Nat}
    {distanceSq : Fraction.Rational}
    (placement : Run.HomographicPlacement center threshold certificate requestedScale count distanceSq)
    (offset : Fin count) : Fraction.Rational :=
  let window := (placement.windowAt offset).1
  min (Best.Cylinder.Stability.exteriorDistanceSq window.source.value window.lower window.upper)
    (Violation.allowedSourceDistanceSq window)

/-- Every retained homographic window has a positive complete shared clearance. -/
theorem windowClearance_pos {center : GaussianInt.Fraction.Reduced} {threshold : Fraction.Rational}
    {certificate : Sharpness.IsSharperWindowThreshold threshold} {requestedScale count : Nat}
    {distanceSq : Fraction.Rational}
    (placement : Run.HomographicPlacement center threshold certificate requestedScale count distanceSq)
    (offset : Fin count) : 0 < windowClearance placement offset :=
  Fraction.Order.Basic.lt_min
    (Best.Cylinder.Stability.exteriorDistanceSq_pos (placement.strictExteriorCertificateAt offset))
    (Violation.allowedSourceDistanceSq_pos (placement.windowAt offset).1)

/-- The shared clearance pays the actual cached window's complete-cylinder distance request. -/
theorem windowClearance_le_exterior {center : GaussianInt.Fraction.Reduced} {threshold : Fraction.Rational}
    {certificate : Sharpness.IsSharperWindowThreshold threshold} {requestedScale count : Nat}
    {distanceSq : Fraction.Rational}
    (placement : Run.HomographicPlacement center threshold certificate requestedScale count distanceSq)
    (offset : Fin count) : windowClearance placement offset ≤
      Best.Cylinder.Stability.exteriorDistanceSq (placement.windowAt offset).1.source.value
        (placement.windowAt offset).1.lower (placement.windowAt offset).1.upper :=
  Fraction.Order.Basic.min_le_left _ _

/-- The shared clearance pays the actual cached window's strict-violation distance request. -/
theorem windowClearance_le_violation {center : GaussianInt.Fraction.Reduced} {threshold : Fraction.Rational}
    {certificate : Sharpness.IsSharperWindowThreshold threshold} {requestedScale count : Nat}
    {distanceSq : Fraction.Rational}
    (placement : Run.HomographicPlacement center threshold certificate requestedScale count distanceSq)
    (offset : Fin count) : windowClearance placement offset ≤
      Violation.allowedSourceDistanceSq (placement.windowAt offset).1 :=
  Fraction.Order.Basic.min_le_right _ _

set_option genInjectivity false in
/-- Retain one homographic run and a proper nested box uniformly certifying every actual cached window.

The clearance list and its positive minimum belong to this exact placement.
The retained box is the neighbourhood computed from that minimum and the
source's original interior certificate. Full strict exterior and threshold
violation laws hold for every bounded window and every rational sample in it.
-/
structure PlacedRun (threshold : Fraction.Rational) (certificate : Sharpness.IsSharperWindowThreshold threshold)
    (requestedScale count : Nat) (outer : Box) where
  /-- The original placement and all its retained numerical caches. -/ placement :
    Run.HomographicPlacement (Run.boxCenter outer) threshold certificate requestedScale count
      (Run.boxPlacementDistanceSq outer)
  /-- The exact placed source lies strictly inside the original outer box. -/ sourceInside :
    outer.StrictContains placement.run.source.value
  /-- The shared clearances for the original bounded windows. -/ clearances : List Fraction.Rational
  /-- The clearance cache has exactly one entry for each original offset. -/ clearancesLength :
    clearances.length = count
  /-- Each cached entry is the original window's complete shared clearance. -/ clearanceSpec : ∀ offset : Fin count,
    Run.offsetValue clearances clearancesLength offset = windowClearance placement offset
  /-- The cached common squared-distance request. -/ allowedDistanceSq : Fraction.Rational
  /-- The common request is the computed finite minimum of the actual cached clearances. -/ distanceSpec :
    allowedDistanceSq = List.Minimum.positiveMinimum clearances
  /-- The actual common distance request is positive. -/ allowedPositive : 0 < allowedDistanceSq
  /-- The proper nested robust box around the original placed source. -/ box : Box
  /-- The box is the neighbourhood computed from the actual source, clearance and interior certificate. -/ boxSpec :
    box = Box.Neighborhood.innerBox outer placement.run.source.value sourceInside allowedDistanceSq allowedPositive
  /-- The cached box has positive width and height. -/ proper : box.Proper
  /-- The cached box lies strictly inside the retained original outer box. -/ nested : box.StrictInterior outer
  /-- Every original window has its full strict exterior certificate at every sample inside the cached box. -/
  uniformExterior : ∀ offset : Fin count, ∀ sample : Gaussian.Basic.Canonical, box.Contains sample →
    Best.Cylinder.Basis.StrictExteriorCertificate sample
      (placement.windowAt offset).1.lower (placement.windowAt offset).1.upper
  /-- Every original window keeps its strict threshold violation throughout the same cached box. -/
  uniformViolation : ∀ offset : Fin count, ∀ sample : Gaussian.Basic.Canonical, box.Contains sample →
    1 < threshold * Dirichlet.Window.SourceBound.dirichletWindowQuadrance sample
      (placement.windowAt offset).1.lower (placement.windowAt offset).1.upper

/-- Construct a proper nested robust neighbourhood using one exact retained placement and interior certificate.

The builder computes each actual window clearance once, takes their finite
minimum and constructs one neighbourhood. Its returned equality certificate
retains the original placement parent, including its matrix and window caches.
-/
def robustPlacementInBox {threshold : Fraction.Rational}
    {certificate : Sharpness.IsSharperWindowThreshold threshold} {requestedScale count : Nat} {outer : Box}
    (placement : Run.HomographicPlacement (Run.boxCenter outer) threshold certificate requestedScale count
      (Run.boxPlacementDistanceSq outer)) (sourceInside : outer.StrictContains placement.run.source.value) :
    {robust : PlacedRun threshold certificate requestedScale count outer // robust.placement = placement} := by
  let clearances := List.ofFn (windowClearance placement)
  have clearancesLength : clearances.length = count := List.OfFn.Basic.length_ofFn
  have clearanceSpec : ∀ offset : Fin count,
      Run.offsetValue clearances clearancesLength offset = windowClearance placement offset := by
    intro offset
    exact List.OfFn.Basic.getElem_ofFn _ offset _
  let allowed := List.Minimum.positiveMinimum clearances
  have positive : 0 < allowed := by
    apply List.Minimum.positiveMinimum_pos clearances
    intro clearance member
    rcases List.OfFn.Basic.mem_ofFn.mp member with ⟨offset, equal⟩
    rewrite [← equal]
    exact windowClearance_pos placement offset
  let box := Box.Neighborhood.innerBox outer placement.run.source.value sourceInside allowed positive
  have nearAt : ∀ offset : Fin count, ∀ sample : Gaussian.Basic.Canonical, box.Contains sample →
      Gaussian.Norm.Basic.normSq (sample - (placement.windowAt offset).1.source.value) <
        windowClearance placement offset := by
    intro offset sample inside
    rewrite [(placement.windowAt offset).property]
    exact (Box.Neighborhood.innerBox_distance_lt sourceInside positive inside).trans_le
      (List.Minimum.positiveMinimum_le_of_mem (List.OfFn.Basic.mem_ofFn.mpr ⟨offset, rfl⟩))
  refine ⟨
    { placement := placement
      sourceInside := sourceInside
      clearances := clearances
      clearancesLength := clearancesLength
      clearanceSpec := clearanceSpec
      allowedDistanceSq := allowed
      distanceSpec := rfl
      allowedPositive := positive
      box := box
      boxSpec := rfl
      proper := Box.Neighborhood.innerBox_proper sourceInside positive
      nested := Box.Neighborhood.innerBox_strictInterior sourceInside positive
      uniformExterior := ?_
      uniformViolation := ?_ }, rfl⟩
  · intro offset sample inside
    have windowBound := placement.windowQuadranceAt_le_nineHalves offset
    rewrite [Dirichlet.Window.SourceBound.dirichletWindowQuadrance_eq_cast] at windowBound
    exact Best.Cylinder.Stability.strictExteriorCertificate_of_distance
      (placement.strictExteriorCertificateAt offset) windowBound
      ((nearAt offset sample inside).trans_le (windowClearance_le_exterior placement offset))
  · intro offset sample inside
    exact Violation.one_lt_threshold_mul_window_of_distance (placement.windowAt offset).1 sample
      ((nearAt offset sample inside).trans_le (windowClearance_le_violation placement offset))

/-- Compute a finite placed run and its proper nested robust box inside any retained proper outer box. -/
def placedRobustRunInBox {threshold : Fraction.Rational}
    (certificate : Sharpness.IsSharperWindowThreshold threshold) (requestedScale count : Nat)
    (outer : Box) (proper : outer.Proper) : PlacedRun threshold certificate requestedScale count outer :=
  let placement := Run.placeHomographicRunInBox certificate requestedScale count outer proper
  (robustPlacementInBox placement (placement.source_strictContains proper)).1

namespace PlacedRun

/-- Every cached window keeps its complete consecutive-best certificate throughout the retained robust box. -/
theorem uniformConsecutive {threshold : Fraction.Rational}
    {certificate : Sharpness.IsSharperWindowThreshold threshold} {requestedScale count : Nat} {outer : Box}
    (robust : PlacedRun threshold certificate requestedScale count outer) (sample : Gaussian.Basic.Canonical)
    (inside : robust.box.Contains sample)
    (window : {window : Sharpness.BadWindow threshold requestedScale // window.source = robust.placement.run.source})
    (member : window ∈ robust.placement.run.windows) :
    Best.Consecutive.Basic.AreConsecutiveBest sample window.1.lower window.1.upper := by
  rcases (robust.placement.mem_windows window).mp member with ⟨offset, equal⟩
  rewrite [← equal]
  exact (robust.uniformExterior offset sample inside).areConsecutiveBest

/-- Every cached window keeps its strict threshold violation throughout the retained robust box. -/
theorem uniformWindowViolation {threshold : Fraction.Rational}
    {certificate : Sharpness.IsSharperWindowThreshold threshold} {requestedScale count : Nat} {outer : Box}
    (robust : PlacedRun threshold certificate requestedScale count outer) (sample : Gaussian.Basic.Canonical)
    (inside : robust.box.Contains sample)
    (window : {window : Sharpness.BadWindow threshold requestedScale // window.source = robust.placement.run.source})
    (member : window ∈ robust.placement.run.windows) :
    1 < threshold * Dirichlet.Window.SourceBound.dirichletWindowQuadrance sample window.1.lower window.1.upper := by
  rcases (robust.placement.mem_windows window).mp member with ⟨offset, equal⟩
  rewrite [← equal]
  exact robust.uniformViolation offset sample inside

end PlacedRun

end Purelib.NumberTheory.Approximation.Dirichlet.Critical.Robust
