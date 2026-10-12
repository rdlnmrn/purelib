module

public import Purelib.NumberTheory.Approximation.Dirichlet.Critical.Run.Homography
public import Purelib.Data.GaussianInt.Fraction.Reduced.Homography
public import Purelib.Data.Rat.List.Maximum
public import Purelib.Geometry.Rational.Box.Neighborhood
import Purelib.Data.Rat.Fraction.Order.Arithmetic

/-!
# Finite placement payments for one critical run

The original offset budgets are materialized once. Each denominator payment
uses its retained budget, and one finite maximum pays every perturbation and
scale requirement. The resulting integral matrix and same-source window run
are retained together with their actual cached payment lists.
-/

public section

namespace Purelib.NumberTheory.Approximation.Dirichlet.Critical.Run

open Purelib.Data
open Purelib.Data.Rat
open Purelib.Geometry.Projective
open Purelib.Geometry.Rational
open Purelib.LinearAlgebra.Coordinates2
open Purelib.NumberTheory.Approximation
open Purelib.NumberTheory.Approximation.Dirichlet.Critical

/-- Read one original finite-table occurrence using its retained exact length certificate. -/
@[expose] def offsetValue {count : Nat} (values : List Fraction.Rational)
    (lengthEq : values.length = count) (offset : Fin count) : Fraction.Rational :=
  values[offset.val]'(lengthEq.symm ▸ offset.isLt)

/-- Compute the affine-denominator payment for one retained correction budget and requested scale. -/
@[expose] def offsetDenominatorPayment (threshold : Fraction.Rational) (requestedScale count : Nat)
    (lowerLeftCoefficient : GaussianInt) (budget : Fraction.Rational) (offset : Fin count) : Fraction.Rational :=
  max ((normalAtIndex threshold count offset).homographicPerturbationDenominatorBound
    lowerLeftCoefficient budget)
    ((normalAtIndex threshold count offset).homographicScaleDenominatorBound requestedScale)

set_option genInjectivity false in
/-- Retain one placed run with the exact numerical budgets, payments and integral matrix used to construct it.

The retained centre and positive distance request determine the spatial
constraint. Each bounded offset reads the original budget and denominator
payment caches. The same matrix supplies the shared exact source and all
window pairs, with paid correction and scale certificates.
-/
structure HomographicPlacement (center : GaussianInt.Fraction.Reduced)
    (threshold : Fraction.Rational) (certificate : Sharpness.IsSharperWindowThreshold threshold)
    (requestedScale count : Nat) (distanceSq : Fraction.Rational) where
  /-- The original bounded offset correction budgets. -/ offsetBudgets : List Fraction.Rational
  /-- The budget cache contains exactly the original number of offsets. -/ budgetsLength : offsetBudgets.length = count
  /-- Each cached budget reads as the original offset correction budget. -/ budgetSpec : ∀ offset : Fin count,
    offsetValue offsetBudgets budgetsLength offset = homographicOffsetBudget threshold count offset
  /-- The denominator payments computed from those exact cached budgets. -/ denominatorPayments : List Fraction.Rational
  /-- The payment cache contains exactly the original number of offsets. -/ paymentsLength :
    denominatorPayments.length = count
  /-- Each payment uses its original offset and cached budget. -/ paymentSpec : ∀ offset : Fin count,
    offsetValue denominatorPayments paymentsLength offset =
      offsetDenominatorPayment threshold requestedScale count center.denominator
        (offsetValue offsetBudgets budgetsLength offset) offset
  /-- The retained common denominator floor. -/ denominatorFloor : Fraction.Rational
  /-- The floor is the computed nonnegative maximum of the actual payment cache. -/ floorSpec :
    denominatorFloor = List.Maximum.nonnegativeMaximum denominatorPayments
  /-- The one retained integral placement matrix. -/ matrix : Matrix GaussianInt
  /-- The matrix uses the actual floor, centre, source tail and spatial request. -/ matrixSpec :
    matrix = center.placementHomography (sourceAtCount threshold count).value
      distanceSq denominatorFloor
  /-- The original Bézout completion certifies determinant one. -/ unitDeterminant : matrix.determinant = 1
  /-- The retained matrix excludes the pole at the original shared source. -/ poleExcluded :
    Homography.Basic.denominator (Matrix.map GaussianInt.toGaussian matrix)
      (sourceAtCount threshold count).value ≠ 0
  /-- Every original offset correction budget is paid by the retained matrix. -/ small : ∀ offset : Fin count,
    Gaussian.Norm.Basic.normSq
      ((normalAtIndex threshold count offset).homographicPerturbation matrix) <
        homographicOffsetBudget threshold count offset
  /-- The same denominator pays the requested scale for every original offset. -/ scalePaid : ∀ offset : Fin count,
    (normalAtIndex threshold count offset).homographicScaleDenominatorBound requestedScale <
      Gaussian.Norm.Basic.normSq (Homography.Basic.denominator (Matrix.map GaussianInt.toGaussian matrix)
        (sourceAtCount threshold count).value)
  /-- The complete cached run with its one source and strictly ordered windows. -/ run :
    SameSourceBadWindowRun threshold requestedScale count
  /-- The run uses this matrix and these exact correction and scale certificates. -/ runSpec :
    run = homographicBadWindowRun certificate
      requestedScale count matrix unitDeterminant poleExcluded small scalePaid
  /-- The retained run source is strictly within the requested distance from its retained centre. -/ sourceNear :
    Gaussian.Norm.Basic.normSq (run.source.value - center.value) < distanceSq

/-- Place a requested finite critical run inside a positive rational distance budget around a retained reduced centre.

The executable builder first materializes each correction budget, then its
denominator payment, then their nonnegative maximum. One placement matrix
uses that retained maximum and produces one shared transformed source for
the retained window run. All certificates refer to these computed caches.
-/
@[expose] def placeHomographicRun (center : GaussianInt.Fraction.Reduced) {threshold : Fraction.Rational}
    (certificate : Sharpness.IsSharperWindowThreshold threshold) (requestedScale count : Nat)
    (distanceSq : Fraction.Rational) (positive : 0 < distanceSq) :
    HomographicPlacement center threshold certificate requestedScale count distanceSq := by
  let budgets := List.ofFn (homographicOffsetBudget threshold count)
  have budgetsLength : budgets.length = count := List.OfFn.Basic.length_ofFn
  have readBudget : ∀ offset : Fin count,
      offsetValue budgets budgetsLength offset = homographicOffsetBudget threshold count offset := by
    intro offset
    exact List.OfFn.Basic.getElem_ofFn _ offset _
  let payments := List.ofFn (fun offset : Fin count => offsetDenominatorPayment
    threshold requestedScale count center.denominator (offsetValue budgets budgetsLength offset) offset)
  have paymentsLength : payments.length = count := List.OfFn.Basic.length_ofFn
  have readPayment : ∀ offset : Fin count, offsetValue payments paymentsLength offset =
      offsetDenominatorPayment threshold requestedScale count center.denominator
        (offsetValue budgets budgetsLength offset) offset := by
    intro offset
    exact List.OfFn.Basic.getElem_ofFn _ offset _
  let floor := List.Maximum.nonnegativeMaximum payments
  have floorNonnegative : 0 ≤ floor := List.Maximum.nonnegativeMaximum_nonneg payments
  let matrix := center.placementHomography (sourceAtCount threshold count).value distanceSq floor
  have unitDeterminant : matrix.determinant = 1 := center.placementHomography_determinant _ _ _
  have poleExcluded := center.placementHomography_poleExcluded
    (sourceAtCount threshold count).value positive floorNonnegative
  have floorPaid := center.placementHomography_denominator_normSq_gt
    (sourceAtCount threshold count).value positive floorNonnegative
  have paymentLeFloor : ∀ offset : Fin count, offsetDenominatorPayment
      threshold requestedScale count center.denominator (offsetValue budgets budgetsLength offset) offset ≤ floor := by
    intro offset
    exact List.Maximum.le_nonnegativeMaximum_of_mem (List.OfFn.Basic.mem_ofFn.mpr ⟨offset, rfl⟩)
  have small : ∀ offset : Fin count, Gaussian.Norm.Basic.normSq
      ((normalAtIndex threshold count offset).homographicPerturbation matrix) <
        homographicOffsetBudget threshold count offset := by
    intro offset
    let normal := normalAtIndex threshold count offset
    have budgetPositive : 0 < offsetValue budgets budgetsLength offset := by
      rewrite [readBudget offset]
      exact homographicOffsetBudget_pos certificate count offset
    have perturbationPaid :
        normal.homographicPerturbationDenominatorBound matrix.c (offsetValue budgets budgetsLength offset) <
        Gaussian.Norm.Basic.normSq (Homography.Basic.denominator (Matrix.map GaussianInt.toGaussian matrix)
          (sourceAtCount threshold count).value) :=
      ((Fraction.Order.Basic.le_max_left _ _).trans (paymentLeFloor offset)).trans_lt floorPaid
    have paid := normal.homographicPerturbation_normSq_lt_of_denominator_gt
      matrix poleExcluded budgetPositive perturbationPaid
    rewrite [readBudget offset] at paid
    exact paid
  have scalePaid : ∀ offset : Fin count,
      (normalAtIndex threshold count offset).homographicScaleDenominatorBound requestedScale <
        Gaussian.Norm.Basic.normSq (Homography.Basic.denominator (Matrix.map GaussianInt.toGaussian matrix)
          (sourceAtCount threshold count).value) := by
    intro offset
    exact ((Fraction.Order.Basic.le_max_right _ _).trans (paymentLeFloor offset)).trans_lt floorPaid
  let run := homographicBadWindowRun certificate requestedScale count
    matrix unitDeterminant poleExcluded small scalePaid
  have sourceValue := homographicBadWindowRun_source_value certificate requestedScale count
    matrix unitDeterminant poleExcluded small scalePaid
  have sourceNear : Gaussian.Norm.Basic.normSq (run.source.value - center.value) < distanceSq := by
    rewrite [sourceValue]
    exact center.placementHomography_distance_lt
      (sourceAtCount threshold count).value positive floorNonnegative
  exact
    { offsetBudgets := budgets
      budgetsLength := budgetsLength
      budgetSpec := readBudget
      denominatorPayments := payments
      paymentsLength := paymentsLength
      paymentSpec := readPayment
      denominatorFloor := floor
      floorSpec := rfl
      matrix := matrix
      matrixSpec := rfl
      unitDeterminant := unitDeterminant
      poleExcluded := poleExcluded
      small := small
      scalePaid := scalePaid
      run := run
      runSpec := rfl
      sourceNear := sourceNear }

namespace HomographicPlacement

variable {center : GaussianInt.Fraction.Reduced} {threshold : Fraction.Rational}
  {certificate : Sharpness.IsSharperWindowThreshold threshold} {requestedScale count : Nat}
  {distanceSq : Fraction.Rational}

/-- Read the actual cached window at its original bounded offset. -/
@[expose] def windowAt
    (placement : HomographicPlacement center threshold certificate requestedScale count distanceSq)
    (offset : Fin count) :
    {window : Sharpness.BadWindow threshold requestedScale // window.source = placement.run.source} :=
  placement.run.windows[offset.val]'(placement.run.length_eq.symm ▸ offset.isLt)

/-- The lower endpoint at a retained offset is the image of that offset's original critical pair. -/
theorem windowAt_lower
    (placement : HomographicPlacement center threshold certificate requestedScale count distanceSq)
    (offset : Fin count) :
    (placement.windowAt offset).1.lower =
      (Pair.criticalLowerPair (runSourceStage threshold 0 count + offset.val)).transform placement.matrix := by
  unfold windowAt
  refine (congrArg (fun run : SameSourceBadWindowRun threshold requestedScale count =>
    (run.windows[offset.val]'(run.length_eq.symm ▸ offset.isLt)).1.lower) placement.runSpec).trans ?_
  unfold homographicBadWindowRun
  rewrite [List.OfFn.Basic.getElem_ofFn]
  rfl

/-- The upper endpoint at a retained offset is the image of that offset's original critical pair. -/
theorem windowAt_upper
    (placement : HomographicPlacement center threshold certificate requestedScale count distanceSq)
    (offset : Fin count) :
    (placement.windowAt offset).1.upper =
      (Pair.criticalUpperPair (runSourceStage threshold 0 count + offset.val)).transform placement.matrix := by
  unfold windowAt
  refine (congrArg (fun run : SameSourceBadWindowRun threshold requestedScale count =>
    (run.windows[offset.val]'(run.length_eq.symm ▸ offset.isLt)).1.upper) placement.runSpec).trans ?_
  unfold homographicBadWindowRun
  rewrite [List.OfFn.Basic.getElem_ofFn]
  rfl

/-- Membership in the cached run is exactly occurrence at one of its original bounded offsets. -/
theorem mem_windows
    (placement : HomographicPlacement center threshold certificate requestedScale count distanceSq)
    (window : {window : Sharpness.BadWindow threshold requestedScale // window.source = placement.run.source}) :
    window ∈ placement.run.windows ↔ ∃ offset : Fin count, placement.windowAt offset = window := by
  constructor
  · intro member
    have enumeratedMember : window ∈ List.ofFn (fun index : Fin placement.run.windows.length =>
        placement.run.windows[index.val]'index.isLt) :=
      (List.OfFn.Basic.ofFn_getElem placement.run.windows).symm ▸ member
    rcases List.OfFn.Basic.mem_ofFn.mp enumeratedMember with ⟨index, equal⟩
    exact ⟨Fin.cast placement.run.length_eq index, equal⟩
  · intro occurrence
    rcases occurrence with ⟨offset, equal⟩
    rewrite [← equal]
    exact List.getElem_mem (placement.run.length_eq.symm ▸ offset.isLt)

/-- The cached run source reads as the homographic image under this placement's retained matrix. -/
theorem source_value {center : GaussianInt.Fraction.Reduced} {threshold : Fraction.Rational}
    {certificate : Sharpness.IsSharperWindowThreshold threshold} {requestedScale count : Nat}
    {distanceSq : Fraction.Rational}
    (placement : HomographicPlacement center threshold certificate requestedScale count distanceSq) :
    placement.run.source.value = Homography.Basic.homographic
      (Matrix.map GaussianInt.toGaussian placement.matrix) (sourceAtCount threshold count).value := by
  rewrite [placement.runSpec]
  exact homographicBadWindowRun_source_value certificate requestedScale count
    placement.matrix placement.unitDeterminant placement.poleExcluded placement.small placement.scalePaid

/-- Every original cached offset budget is positive under the retained sharper-threshold certificate. -/
theorem offsetBudget_pos {center : GaussianInt.Fraction.Reduced} {threshold : Fraction.Rational}
    {certificate : Sharpness.IsSharperWindowThreshold threshold} {requestedScale count : Nat}
    {distanceSq : Fraction.Rational}
    (placement : HomographicPlacement center threshold certificate requestedScale count distanceSq)
    (offset : Fin count) :
    0 < offsetValue placement.offsetBudgets placement.budgetsLength offset := by
  rewrite [placement.budgetSpec offset]
  exact homographicOffsetBudget_pos certificate count offset

/-- The actual cached window retains the complete strict exterior certificate at its original source. -/
theorem strictExteriorCertificateAt
    (placement : HomographicPlacement center threshold certificate requestedScale count distanceSq)
    (offset : Fin count) :
    Best.Cylinder.Basis.StrictExteriorCertificate (placement.windowAt offset).1.source.value
      (placement.windowAt offset).1.lower (placement.windowAt offset).1.upper := by
  rewrite [(placement.windowAt offset).property, placement.source_value,
    placement.windowAt_lower, placement.windowAt_upper]
  exact (normalAtIndex threshold count offset).homographic_strictExteriorCertificate
    placement.matrix placement.unitDeterminant placement.poleExcluded
      ((placement.small offset).trans_le (homographicOffsetBudget_le_cylinder threshold count offset))

/-- The actual cached window product satisfies the complete-cylinder stability normalization bound. -/
theorem windowQuadranceAt_le_nineHalves
    (placement : HomographicPlacement center threshold certificate requestedScale count distanceSq)
    (offset : Fin count) :
    Dirichlet.Window.SourceBound.dirichletWindowQuadrance (placement.windowAt offset).1.source.value
      (placement.windowAt offset).1.lower (placement.windowAt offset).1.upper ≤ 9 / 2 := by
  rewrite [(placement.windowAt offset).property, placement.source_value,
    placement.windowAt_lower, placement.windowAt_upper]
  exact (normalAtIndex threshold count offset).homographic_windowQuadrance_le_nineHalves
    placement.matrix placement.unitDeterminant placement.poleExcluded
      (((placement.small offset).trans_le ((homographicOffsetBudget_le_cylinder threshold count offset).trans
        (Cylinder.TwoParameter.denominatorPerturbationDistanceSq_le_oneEighth _ _))).le)

end HomographicPlacement

/-- Retain the reduced Gaussian fraction representing the midpoint of the original box. -/
@[expose] def boxCenter (outer : Box) : GaussianInt.Fraction.Reduced :=
  GaussianInt.Fraction.Reduced.reduce (GaussianInt.Fraction.ofGaussian outer.midpoint)

/-- The retained reduced centre reads exactly as the original box midpoint. -/
theorem boxCenter_value (outer : Box) : (boxCenter outer).value = outer.midpoint :=
  (GaussianInt.Fraction.Reduced.reduce_value _).trans (GaussianInt.Fraction.ofGaussian_value _)

/-- Compute the squared coordinate-radius payment keeping a placed source strictly inside the original box. -/
@[expose] def boxPlacementDistanceSq (outer : Box) : Fraction.Rational :=
  Box.Neighborhood.radius outer outer.midpoint 1 ^ 2

/-- A proper retained box has a positive spatial placement budget. -/
theorem boxPlacementDistanceSq_pos {outer : Box} (proper : outer.Proper) :
    0 < boxPlacementDistanceSq outer := by
  have positive := Box.Neighborhood.radius_pos (Box.midpoint_strictContains proper) (by decide :
    (0 : Fraction.Rational) < 1)
  exact Fraction.Order.Arithmetic.pow_pos_direct positive 2

/-- Place the requested finite run using the exact retained midpoint and interior-clearance budget of a proper box.

The result retains its placement matrix, all computed correction and
denominator payment caches, and the actual same-source window run. The
source containment law transports this same result into the original box.
-/
@[expose] def placeHomographicRunInBox {threshold : Fraction.Rational}
    (certificate : Sharpness.IsSharperWindowThreshold threshold) (requestedScale count : Nat)
    (outer : Box) (proper : outer.Proper) :
    HomographicPlacement (boxCenter outer) threshold certificate requestedScale count (boxPlacementDistanceSq outer) :=
  placeHomographicRun (boxCenter outer) certificate requestedScale count
    (boxPlacementDistanceSq outer) (boxPlacementDistanceSq_pos proper)

/-- Any retained placement using the original box centre and spatial payment lies strictly inside that box. -/
theorem HomographicPlacement.source_strictContains {threshold : Fraction.Rational}
    {certificate : Sharpness.IsSharperWindowThreshold threshold} {requestedScale count : Nat}
    {outer : Box}
    (placement : HomographicPlacement (boxCenter outer) threshold certificate requestedScale count
      (boxPlacementDistanceSq outer)) (proper : outer.Proper) : outer.StrictContains placement.run.source.value := by
  have near := placement.sourceNear
  rewrite [boxCenter_value] at near
  exact Box.Neighborhood.strictContains_of_distance_le (Box.midpoint_strictContains proper)
    (by decide : (0 : Fraction.Rational) < 1) near.le

/-- The actual source of the cached placed run lies strictly inside the retained proper outer box. -/
theorem placeHomographicRunInBox_source_strictContains {threshold : Fraction.Rational}
    (certificate : Sharpness.IsSharperWindowThreshold threshold) (requestedScale count : Nat)
    (outer : Box) (proper : outer.Proper) :
    outer.StrictContains (placeHomographicRunInBox certificate requestedScale count outer proper).run.source.value := by
  exact (placeHomographicRunInBox certificate requestedScale count outer proper).source_strictContains proper

end Purelib.NumberTheory.Approximation.Dirichlet.Critical.Run
