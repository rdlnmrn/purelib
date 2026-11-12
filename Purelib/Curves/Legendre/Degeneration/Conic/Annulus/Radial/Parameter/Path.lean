module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Parameter
public import Purelib.Riemann.RootContinuation.FixedRootBoxPath
import Purelib.Data.Rat.Fraction.Cast
import Purelib.Data.Rat.Interval.Bounds
import Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence
import Purelib.RootIsolation.SquareRoot.Owner.Transport
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Ordinate
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Parameter.Bounds
import Purelib.Data.Rat.Interval.ConvexCombination
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Norm.Power
import Purelib.Tactic.Ring

/-!
# Nonlinear changed-parameter paths on retained original radial spans

The original rational chart span parametrizes the unchanged source spatial
curve. Its changed normalized quadratic has independently derived movement,
variation and nonzero certificates. Original endpoint Seed owners supply
two cached fixed-box budgets; no advanced target-owner clearance is reused.
The retained parameter Step owners remain separate endpoint inputs.

The existing PathData represents two fixed-box root branches. Comparing
those branches across the two original windows remains distinct evidence.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Parameter.Path

open Purelib.RootIsolation.SquareRoot.Owner

open Purelib.Data.Rat.Fraction.Order

open Purelib
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Riemann.RootContinuation
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence (ownerRootName ownerRootName_castOwnerParameter)
open Purelib.RootIsolation

/-- Read the original span's affine chart time at the supplied unit parameter. -/
@[expose] def time (span : Interval.Bounds) (parameter : Fraction.Rational) : Fraction.Rational :=
  span.lower + parameter * span.width

/-- The original lower chart endpoint is retained at the zero path parameter. -/
theorem time_zero (span : Interval.Bounds) : time span 0 = span.lower := by unfold time; ring1

/-- The original upper chart endpoint is retained at the one path parameter. -/
theorem time_one (span : Interval.Bounds) : time span 1 = span.upper := by
  change span.lower + 1 * (span.upper - span.lower) = span.upper
  ring1

/-- Every unit parameter reads a time in the same original closed chart span. -/
theorem time_inside (span : Interval.Bounds) {parameter : Fraction.Rational}
    (inside : FixedRootBoxPath.Inside parameter) : span.Contains (time span parameter) :=
  Geometry.Rational.Box.coordinate_between
    ⟨Fraction.Order.Basic.le_refl _, span.valid⟩ ⟨span.valid, Fraction.Order.Basic.le_refl _⟩ inside

/-- The difference of retained chart times has its exact original span-width factor. -/
theorem time_sub (span : Interval.Bounds) (first last : Fraction.Rational) :
    time span first - time span last = (first - last) * span.width := by unfold time; ring1

/-- The changed normalized quadratic follows the unchanged original spatial radial chart. -/
@[expose] def point (site : Fin 2) (parameter increment : Canonical) (quarter : UnitCircuitQuarter)
    (span : Interval.Bounds) (index : Fraction.Rational) : Canonical :=
  radicand site parameter (Waist.direction quarter (time span index)) increment

/-- The nonlinear path starts at the actual changed radicand of the original lower chart point. -/
theorem point_zero (site : Fin 2) (parameter increment : Canonical) (quarter : UnitCircuitQuarter)
    (span : Interval.Bounds) : point site parameter increment quarter span 0 =
      radicand site parameter (Waist.direction quarter span.lower) increment := by
  unfold point
  rewrite [time_zero]
  rfl

/-- The nonlinear path finishes at the actual changed radicand of the original upper chart point. -/
theorem point_one (site : Fin 2) (parameter increment : Canonical) (quarter : UnitCircuitQuarter)
    (span : Interval.Bounds) : point site parameter increment quarter span 1 =
      radicand site parameter (Waist.direction quarter span.upper) increment := by
  unfold point
  rewrite [time_one]
  rfl

/-- Every path radicand is the changed centered quadratic at the same original physical spatial point. -/
theorem point_quadratic (site : Fin 2) (parameter increment : Canonical) (quarter : UnitCircuitQuarter)
    (span : Interval.Bounds) (index : Fraction.Rational) :
    point site parameter increment quarter span index =
      coordinate site (parameter + increment)
        (sourcePoint site parameter (Waist.direction quarter (time span index))).base ^ 2 -
        smoothing site (parameter + increment) :=
  radicand_eq site parameter (Waist.direction quarter (time span index)) increment

/-- The fixed increment retains one common changed-radicand chart-time variation scale. -/
@[expose] def chartScale (site : Fin 2) (parameter : Canonical) : Fraction.Rational :=
  (Fraction.Cast.fromInt 40025 / Fraction.Cast.fromInt 512) * Norm.Basic.normSq (halfGap site parameter) ^ 2

/-- The original normalized-radicand variation scale is nonnegative. -/
theorem chartScale_nonnegative (site : Fin 2) (parameter : Canonical) : 0 ≤ chartScale site parameter :=
  Arithmetic.mul_nonneg_direct (by decide +kernel)
    (Arithmetic.sq_nonneg_direct _)

/-- Admitted increments pay changed normalized-radicand variation between arbitrary original chart times.

The original squared-ordinate variation and spatial branch-factor variation
retain the same half-gap. Their actual difference decomposition pays the bound.
-/
theorem radicand_variation (site : Fin 2) (parameter increment : Canonical) (quarter : UnitCircuitQuarter)
    (admitted : IncrementBound site parameter increment) (first last : Fraction.Rational) :
    Norm.Basic.normSq (radicand site parameter (Waist.direction quarter first) increment -
        radicand site parameter (Waist.direction quarter last) increment) ≤
      chartScale site parameter * (first - last) ^ 2 := by
  let firstPoint := sourcePoint site parameter (Waist.direction quarter first)
  let lastPoint := sourcePoint site parameter (Waist.direction quarter last)
  have source := quarter_ordinate_square_distance_le site parameter 2 quarter
    (by decide +kernel) (by decide +kernel) (by decide +kernel) first last
  have base := quarter_base_distance_le site parameter 2 quarter
    (by decide +kernel) (by decide +kernel) (by decide +kernel) first last
  have factor : branchFactor site parameter (Waist.direction quarter first) -
      branchFactor site parameter (Waist.direction quarter last) = firstPoint.base - lastPoint.base := by
    unfold branchFactor
    change (firstPoint.base - criticalValue site) - (lastPoint.base - criticalValue site) = _
    ring1
  have shifted : radicand site parameter (Waist.direction quarter first) increment -
      radicand site parameter (Waist.direction quarter last) increment =
      (firstPoint.ordinate ^ 2 - lastPoint.ordinate ^ 2) - (firstPoint.base - lastPoint.base) * increment := by
    unfold radicand
    rewrite [← factor]
    ring1
  have incrementBound : Norm.Basic.normSq increment ≤
      (1 / Fraction.Cast.fromInt 256) * Norm.Basic.normSq (halfGap site parameter) := by
    have cast256 : (256 : Fraction.Rational) = Fraction.Cast.fromInt (256 : Int) :=
      (Fraction.Cast.natCast_eq_fromInt (256 : Nat)).trans (by decide +kernel)
    have paid := admitted
    unfold IncrementBound at paid
    rewrite [cast256] at paid
    exact paid
  have upperNonnegative : (0 : Fraction.Rational) ≤
      (25 / 4) * Norm.Basic.normSq (halfGap site parameter) * (first - last) ^ 2 :=
    Arithmetic.mul_nonneg_direct
      (Arithmetic.mul_nonneg_direct (by decide +kernel) (Norm.Basic.normSq_nonneg _))
      (Arithmetic.sq_nonneg_direct _)
  have branch : Norm.Basic.normSq ((firstPoint.base - lastPoint.base) * increment) ≤
      ((25 / 4) * Norm.Basic.normSq (halfGap site parameter) * (first - last) ^ 2) *
        ((1 / Fraction.Cast.fromInt 256) * Norm.Basic.normSq (halfGap site parameter)) := by
    rewrite [Norm.Basic.normSq_mul]
    exact Arithmetic.mul_le_mul_direct base incrementBound (Norm.Basic.normSq_nonneg _)
      upperNonnegative
  rewrite [shifted]
  calc
    _ ≤ 2 * (Norm.Basic.normSq (firstPoint.ordinate ^ 2 - lastPoint.ordinate ^ 2) +
        Norm.Basic.normSq ((firstPoint.base - lastPoint.base) * increment)) := Norm.Bounds.normSq_sub_le_two _ _
    _ ≤ 2 * ((625 / 16) * Norm.Basic.normSq (halfGap site parameter) ^ 2 * (first - last) ^ 2 +
        ((25 / 4) * Norm.Basic.normSq (halfGap site parameter) * (first - last) ^ 2) *
          ((1 / Fraction.Cast.fromInt 256) * Norm.Basic.normSq (halfGap site parameter))) :=
      Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Arithmetic.add_le_add_direct source branch) (by decide +kernel)
    _ = (2 * (625 / 16 + (25 / 4) * (1 / Fraction.Cast.fromInt 256))) *
        Norm.Basic.normSq (halfGap site parameter) ^ 2 * (first - last) ^ 2 := by ring1
    _ = _ := by
      rewrite [show (2 * (625 / 16 + (25 / 4) * (1 / Fraction.Cast.fromInt 256)) : Fraction.Rational) =
        Fraction.Cast.fromInt 40025 / Fraction.Cast.fromInt 512 by decide +kernel]
      rfl

/-- The same span multiplies the chart variation scale by its exact original squared width. -/
@[expose] def scale (site : Fin 2) (parameter : Canonical) (span : Interval.Bounds) : Fraction.Rational :=
  chartScale site parameter * span.width ^ 2

/-- The nonlinear path's original squared variation scale is nonnegative. -/
theorem scale_nonnegative (site : Fin 2) (parameter : Canonical) (span : Interval.Bounds) :
    0 ≤ scale site parameter span :=
  Arithmetic.mul_nonneg_direct (chartScale_nonnegative site parameter)
    (Arithmetic.sq_nonneg_direct _)

/-- The nonlinear path retains its same original span-width squared variation budget. -/
theorem variation (site : Fin 2) (parameter increment : Canonical) (quarter : UnitCircuitQuarter)
    (span : Interval.Bounds) (admitted : IncrementBound site parameter increment)
    (first last : Fraction.Rational) :
    Norm.Basic.normSq (point site parameter increment quarter span first -
        point site parameter increment quarter span last) ≤ scale site parameter span * (last - first) ^ 2 := by
  have bound := radicand_variation site parameter increment quarter admitted (time span first) (time span last)
  rewrite [time_sub] at bound
  exact bound.trans_eq (by
    unfold scale
    ring1)

/-- The exact original geometric movement request for the two endpoint Seed boxes. -/
@[expose] def movement (site : Fin 2) (parameter : Canonical) : Fraction.Rational :=
  (11 / Fraction.Cast.fromInt 256) * Norm.Basic.normSq (halfGap site parameter) ^ 2

/-- The original movement request is nonnegative. -/
theorem movement_nonnegative (site : Fin 2) (parameter : Canonical) : 0 ≤ movement site parameter :=
  Arithmetic.mul_nonneg_direct (by decide +kernel)
    (Arithmetic.sq_nonneg_direct _)

variable {site : Fin 2} {parameter increment : Canonical} {quarter : UnitCircuitQuarter}
variable {span : Interval.Bounds} {reference : Fraction.Rational}
variable {unit : Owner
  ((unitPolynomial site).eval (sourcePoint site parameter (Waist.direction quarter reference)).base)}
variable {source : Lift (sourcePoint site parameter (Waist.direction quarter reference)) unit}

/-- The original anchor's exact source Seed clearance strictly pays the retained movement request. -/
theorem movement_small (anchor : Anchor source) :
    movement site parameter < anchor.seed.owner.track.initial.clearance.bound := by
  have coefficient : (11 / Fraction.Cast.fromInt 256 : Fraction.Rational) < 729 / 16384 := by
    change (11 / Fraction.Cast.fromInt 256 : Fraction.Rational) <
      ((729 : Nat) : Fraction.Rational) / ((16384 : Nat) : Fraction.Rational)
    rewrite [Fraction.Cast.natCast_eq_fromInt 729, Fraction.Cast.natCast_eq_fromInt 16384]
    decide +kernel
  exact (Arithmetic.mul_lt_mul_of_pos_right_direct coefficient
    (Arithmetic.pow_pos_direct anchor.gapNorm_positive 2)).trans_le anchor.clearance_lower

/-- The original source normalized square has its intrinsic half-gap fourth-power norm floor. -/
private theorem source_normSq_lower (anchor : Anchor source) :
    (81 / Fraction.Cast.fromInt 256) * Norm.Basic.normSq (halfGap site parameter) ^ 2 ≤
      Norm.Basic.normSq ((sourcePoint site parameter (Waist.direction quarter reference)).ordinate ^ 2) := by
  have floor := parallel_ordinate_lower site parameter (Waist.direction quarter reference)
  have squared := Arithmetic.pow_le_pow_direct
    (Arithmetic.mul_nonneg_direct (by decide +kernel) anchor.gapNorm_positive.le) floor 2
  rewrite [Norm.Power.normSq_pow]
  calc
    _ = (9 / 16 : Fraction.Rational) ^ 2 * Norm.Basic.normSq (halfGap site parameter) ^ 2 := by
      rewrite [show (81 / Fraction.Cast.fromInt 256 : Fraction.Rational) = (9 / 16) ^ 2 by decide +kernel]
      rfl
    _ = ((9 / 16) * Norm.Basic.normSq (halfGap site parameter)) ^ 2 := by ring1
    _ ≤ Norm.Basic.normSq (sourcePoint site parameter (Waist.direction quarter reference)).ordinate ^ 2 := squared
    _ = _ := by ring1

/-- The actual endpoint source Seed pays movement to every changed radicand of the original small span.

The original parameter move and changed-radicand spatial variation are paid
separately before their triangle. Both retained chart times lie in the same
original Bounds; no root or continuation owner is reconstructed.
-/
theorem reference_movement (anchor : Anchor source) (increment : Canonical)
    (admitted : IncrementBound site parameter increment) (referenceInside : span.Contains reference)
    (width : span.width ^ 2 ≤ 1 / Fraction.Cast.fromInt 65536)
    (index : Fraction.Rational) (inside : FixedRootBoxPath.Inside index) :
    Norm.Basic.normSq ((sourcePoint site parameter (Waist.direction quarter reference)).ordinate ^ 2 -
      point site parameter increment quarter span index) ≤ movement site parameter := by
  have parameterMove := anchor.movement_le increment admitted
  have spatial := radicand_variation site parameter increment quarter admitted reference (time span index)
  have timeBound := Interval.parameter_sub_sq_le_width_sq span referenceInside (time_inside span inside)
  have spatialBound := spatial.trans (Arithmetic.mul_le_mul_of_nonneg_left_direct
    (timeBound.trans width) (chartScale_nonnegative site parameter))
  have triangle := Norm.Bounds.normSq_sub_le_via
    ((sourcePoint site parameter (Waist.direction quarter reference)).ordinate ^ 2)
    (radicand site parameter (Waist.direction quarter reference) increment)
    (point site parameter increment quarter span index)
  have combined := triangle.trans (Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Arithmetic.add_le_add_direct parameterMove spatialBound) (by decide +kernel))
  have coefficient : (2 * (41 / 2048 +
      (Fraction.Cast.fromInt 40025 / Fraction.Cast.fromInt 512) *
        (1 / Fraction.Cast.fromInt 65536)) : Fraction.Rational) ≤
      11 / Fraction.Cast.fromInt 256 := by
    change (2 * (41 / ((2048 : Nat) : Fraction.Rational) +
        (Fraction.Cast.fromInt 40025 / Fraction.Cast.fromInt 512) *
          (1 / Fraction.Cast.fromInt 65536)) : Fraction.Rational) ≤
      11 / Fraction.Cast.fromInt 256
    rewrite [Fraction.Cast.natCast_eq_fromInt 2048]
    decide +kernel
  calc
    _ ≤ 2 * ((41 / 2048) * Norm.Basic.normSq (halfGap site parameter) ^ 2 +
        chartScale site parameter * (1 / Fraction.Cast.fromInt 65536)) := combined
    _ = (2 * (41 / 2048 + (Fraction.Cast.fromInt 40025 / Fraction.Cast.fromInt 512) *
        (1 / Fraction.Cast.fromInt 65536))) *
        Norm.Basic.normSq (halfGap site parameter) ^ 2 := by unfold chartScale; ring1
    _ ≤ _ := Arithmetic.mul_le_mul_of_nonneg_right_direct coefficient
      (Arithmetic.sq_nonneg_direct _)

/-- The original endpoint Seed and its paid movement prove every changed path radicand is nonzero. -/
theorem nonzero (anchor : Anchor source) (increment : Canonical)
    (admitted : IncrementBound site parameter increment) (referenceInside : span.Contains reference)
    (width : span.width ^ 2 ≤ 1 / Fraction.Cast.fromInt 65536)
    (index : Fraction.Rational) (inside : FixedRootBoxPath.Inside index) :
    point site parameter increment quarter span index ≠ 0 := by
  have bounded := reference_movement anchor increment admitted referenceInside width index inside
  have small : movement site parameter <
      Norm.Basic.normSq ((sourcePoint site parameter (Waist.direction quarter reference)).ordinate ^ 2) :=
    (Arithmetic.mul_lt_mul_of_pos_right_direct
      (show (11 / Fraction.Cast.fromInt 256 : Fraction.Rational) < 81 / Fraction.Cast.fromInt 256 by decide +kernel)
      (Arithmetic.pow_pos_direct anchor.gapNorm_positive 2)).trans_le (source_normSq_lower anchor)
  intro zero
  rewrite [zero, Basic.sub_zero] at bounded
  exact small.2 bounded

/-- Cache the original endpoint Seed's fixed-box movement and majorant budget. -/
def budget (anchor : Anchor source) : FixedRootBoxBudget.Budget anchor.seed.owner :=
  FixedRootBoxBudget.Budget.acquire anchor.seed.owner (movement site parameter)
    (movement_nonnegative site parameter) (movement_small anchor)

/-- The original cached Seed budget retains exactly the computed geometric movement request. -/
theorem budget_movement (anchor : Anchor source) : (budget anchor).movement = movement site parameter := by
  unfold budget
  rfl

variable {lastReference : Fraction.Rational}
variable {lastUnit : Owner
  ((unitPolynomial site).eval (sourcePoint site parameter (Waist.direction quarter lastReference)).base)}
variable {lastSource : Lift (sourcePoint site parameter (Waist.direction quarter lastReference)) lastUnit}

/-- Construct the original nonlinear PathData from two retained endpoint Seed budgets and exact movement readbacks.

Both original chart references lie in the same small retained Bounds. The
supplied budget values keep their original Seed owners; every movement and
nonzero obligation is derived from those same anchors and geometric payment.
-/
def ofBudgets (first : Anchor source) (last : Anchor lastSource)
    (increment : Canonical) (admitted : IncrementBound site parameter increment)
    (firstInside : span.Contains reference) (lastInside : span.Contains lastReference)
    (width : span.width ^ 2 ≤ 1 / Fraction.Cast.fromInt 65536)
    (firstBudget : FixedRootBoxBudget.Budget first.seed.owner)
    (firstMovement : firstBudget.movement = movement site parameter)
    (lastBudget : FixedRootBoxBudget.Budget last.seed.owner)
    (lastMovement : lastBudget.movement = movement site parameter) :
    FixedRootBoxPath.PathData firstBudget lastBudget :=
  { point := point site parameter increment quarter span
    nonzero index inside := nonzero first increment admitted firstInside width index inside
    firstMovement index inside := by
      rewrite [firstMovement]
      have bounded := reference_movement first increment admitted firstInside width index inside
      rewrite [Norm.Basic.normSq_eq_canonical] at bounded
      exact bounded
    secondMovement index inside := by
      rewrite [lastMovement]
      have bounded := reference_movement last increment admitted lastInside width index inside
      rewrite [Norm.Basic.normSq_eq_canonical] at bounded
      exact bounded
    scale := scale site parameter span
    scale_nonnegative := scale_nonnegative site parameter span
    variation left right _ _ := by
      have bounded := variation site parameter increment quarter span admitted left right
      rewrite [Norm.Basic.normSq_eq_canonical] at bounded
      exact bounded }

/-- The constructed nonlinear PathData uses the same original changed-radicand point function. -/
theorem ofBudgets_point (first : Anchor source) (last : Anchor lastSource)
    (increment : Canonical) (admitted : IncrementBound site parameter increment)
    (firstInside : span.Contains reference) (lastInside : span.Contains lastReference)
    (width : span.width ^ 2 ≤ 1 / Fraction.Cast.fromInt 65536)
    (firstBudget : FixedRootBoxBudget.Budget first.seed.owner)
    (firstMovement : firstBudget.movement = movement site parameter)
    (lastBudget : FixedRootBoxBudget.Budget last.seed.owner)
    (lastMovement : lastBudget.movement = movement site parameter) (index : Fraction.Rational) :
    (ofBudgets first last increment admitted firstInside lastInside width
      firstBudget firstMovement lastBudget lastMovement).point index =
      point site parameter increment quarter span index := by
  unfold ofBudgets
  rfl

/-- Cache the two original Seed budgets once and the nonlinear PathData on those identical retained budget values.

The exact factory equations preserve both original anchors and all budget
majorants. Path readbacks consume these stored values rather than requesting
another Seed or rebuilding either budget for each root comparison.
-/
@[expose] def Cache (first : Anchor source) (last : Anchor lastSource)
    (increment : Canonical) (admitted : IncrementBound site parameter increment)
    (firstInside : span.Contains reference) (lastInside : span.Contains lastReference)
    (width : span.width ^ 2 ≤ 1 / Fraction.Cast.fromInt 65536) :=
  Σ firstBudget : { retained : FixedRootBoxBudget.Budget first.seed.owner // retained = budget first },
    Σ lastBudget : { retained : FixedRootBoxBudget.Budget last.seed.owner // retained = budget last },
      { path : FixedRootBoxPath.PathData firstBudget.val lastBudget.val //
        path = ofBudgets first last increment admitted firstInside lastInside width
          firstBudget.val
            ((congrArg (fun retained : FixedRootBoxBudget.Budget first.seed.owner => retained.movement)
              firstBudget.property).trans (budget_movement first))
          lastBudget.val
            ((congrArg (fun retained : FixedRootBoxBudget.Budget last.seed.owner => retained.movement)
              lastBudget.property).trans (budget_movement last)) }

/-- Construct both original Seed budget caches once, then retain their actual nonlinear PathData. -/
def build (first : Anchor source) (last : Anchor lastSource)
    (increment : Canonical) (admitted : IncrementBound site parameter increment)
    (firstInside : span.Contains reference) (lastInside : span.Contains lastReference)
    (width : span.width ^ 2 ≤ 1 / Fraction.Cast.fromInt 65536) :
    Cache first last increment admitted firstInside lastInside width :=
  let firstBudget := budget first
  let lastBudget := budget last
  let path := ofBudgets first last increment admitted firstInside lastInside width
    firstBudget (budget_movement first) lastBudget (budget_movement last)
  ⟨⟨firstBudget, rfl⟩, ⟨lastBudget, rfl⟩, ⟨path, rfl⟩⟩

namespace Cache

variable {first : Anchor source} {last : Anchor lastSource}
variable {admitted : IncrementBound site parameter increment}
variable {firstInside : span.Contains reference} {lastInside : span.Contains lastReference}
variable {width : span.width ^ 2 ≤ 1 / Fraction.Cast.fromInt 65536}

/-- Read the actual original first Seed budget retained in the nonlinear path cache. -/
@[expose] def firstBudget (cache : Cache first last increment admitted firstInside lastInside width) :
    FixedRootBoxBudget.Budget first.seed.owner := cache.1.val

/-- Read the actual distinct original last Seed budget retained in the same path cache. -/
@[expose] def lastBudget (cache : Cache first last increment admitted firstInside lastInside width) :
    FixedRootBoxBudget.Budget last.seed.owner := cache.2.1.val

/-- The retained first budget is the exact original factory on the same source Seed owner. -/
theorem firstBudget_eq (cache : Cache first last increment admitted firstInside lastInside width) :
    cache.firstBudget = budget first := cache.1.property

/-- The retained last budget is the exact original factory on the same distinct source Seed owner. -/
theorem lastBudget_eq (cache : Cache first last increment admitted firstInside lastInside width) :
    cache.lastBudget = budget last := cache.2.1.property

/-- Read the identical original nonlinear PathData on the two actual stored Seed budget values. -/
@[expose] def path (cache : Cache first last increment admitted firstInside lastInside width) :
    FixedRootBoxPath.PathData cache.firstBudget cache.lastBudget := cache.2.2.val

/-- The cached first budget retains the same internally paid geometric movement. -/
theorem firstBudget_movement (cache : Cache first last increment admitted firstInside lastInside width) :
    cache.firstBudget.movement = movement site parameter := by
  rewrite [cache.firstBudget_eq]
  exact budget_movement first

/-- The cached last budget retains the same geometric movement on its original separate Seed. -/
theorem lastBudget_movement (cache : Cache first last increment admitted firstInside lastInside width) :
    cache.lastBudget.movement = movement site parameter := by
  rewrite [cache.lastBudget_eq]
  exact budget_movement last

/-- The nonlinear PathData is exactly the completed factory on its two actual retained Seed budgets. -/
theorem path_eq (cache : Cache first last increment admitted firstInside lastInside width) :
    cache.path = ofBudgets first last increment admitted firstInside lastInside width
      cache.firstBudget cache.firstBudget_movement cache.lastBudget cache.lastBudget_movement := cache.2.2.property

/-- Every cached path point is the actual changed radicand at the same retained original chart time. -/
theorem point_eq (cache : Cache first last increment admitted firstInside lastInside width)
    (index : Fraction.Rational) :
    cache.path.point index = point site parameter increment quarter span index := by
  rewrite [cache.path_eq]
  exact ofBudgets_point _ _ _ _ _ _ _ _ _ _ _ _

/-- The cached nonlinear path starts at the original span's actual changed lower-endpoint radicand. -/
theorem point_zero (cache : Cache first last increment admitted firstInside lastInside width) :
    cache.path.point 0 = radicand site parameter (Waist.direction quarter span.lower) increment :=
  (cache.point_eq 0).trans (Path.point_zero site parameter increment quarter span)

/-- The cached nonlinear path finishes at the original span's actual changed upper-endpoint radicand. -/
theorem point_one (cache : Cache first last increment admitted firstInside lastInside width) :
    cache.path.point 1 = radicand site parameter (Waist.direction quarter span.upper) increment :=
  (cache.point_eq 1).trans (Path.point_one site parameter increment quarter span)

/-- Every first-branch nonlinear path owner keeps the identical original first Seed box. -/
theorem first_box (cache : Cache first last increment admitted firstInside lastInside width)
    (index : Fraction.Rational) (inside : FixedRootBoxPath.Inside index) :
    (cache.path.First index inside).track.initial.box = first.seed.owner.track.initial.box :=
  cache.path.first_box index inside

/-- Every second-branch nonlinear path owner keeps the identical original last Seed box. -/
theorem last_box (cache : Cache first last increment admitted firstInside lastInside width)
    (index : Fraction.Rational) (inside : FixedRootBoxPath.Inside index) :
    (cache.path.Second index inside).track.initial.box = last.seed.owner.track.initial.box :=
  cache.path.second_box index inside

/-- The original first Step parameter is the exact nonlinear start parameter at the retained initial chart reference. -/
theorem start_parameter (cache : Cache first last increment admitted firstInside lastInside width)
    (start : span.lower = reference) :
    cache.path.point 0 = radicand site parameter (Waist.direction quarter reference) increment :=
  cache.point_zero.trans (congrArg (fun time => radicand site parameter (Waist.direction quarter time) increment) start)

/-- The original last Step parameter is the exact nonlinear finish parameter at the retained final chart reference. -/
theorem finish_parameter (cache : Cache first last increment admitted firstInside lastInside width)
    (finish : span.upper = lastReference) :
    cache.path.point 1 = radicand site parameter (Waist.direction quarter lastReference) increment :=
  cache.point_one.trans (congrArg (fun time => radicand site parameter (Waist.direction quarter time) increment) finish)

/-- Reindex the entire original first Step target owner at the exact cached nonlinear start parameter. -/
@[expose] def startOwner (cache : Cache first last increment admitted firstInside lastInside width)
    (step : Step first increment) (start : span.lower = reference) : Owner (cache.path.point 0) :=
  Transport.castOwnerParameter (cache.start_parameter start).symm step.target

/-- The complete original first Step target owner is retained by the exact nonlinear start reindexing. -/
theorem startOwner_heq (cache : Cache first last increment admitted firstInside lastInside width)
    (step : Step first increment) (start : span.lower = reference) : HEq (cache.startOwner step start) step.target :=
  Transport.castOwnerParameter_heq (cache.start_parameter start).symm step.target

/-- The reindexed nonlinear start owner keeps the original first Step's exact initial box. -/
theorem startOwner_box (cache : Cache first last increment admitted firstInside lastInside width)
    (step : Step first increment) (start : span.lower = reference) :
    (cache.startOwner step start).track.initial.box = step.target.track.initial.box :=
  Transport.castOwnerParameter_initial_box (cache.start_parameter start).symm step.target

/-- Reindex the entire original last Step target owner at the exact cached nonlinear finish parameter. -/
@[expose] def finishOwner (cache : Cache first last increment admitted firstInside lastInside width)
    (step : Step last increment) (finish : span.upper = lastReference) : Owner (cache.path.point 1) :=
  Transport.castOwnerParameter (cache.finish_parameter finish).symm step.target

/-- The complete original last Step target owner is retained by the exact nonlinear finish reindexing. -/
theorem finishOwner_heq (cache : Cache first last increment admitted firstInside lastInside width)
    (step : Step last increment) (finish : span.upper = lastReference) :
    HEq (cache.finishOwner step finish) step.target :=
  Transport.castOwnerParameter_heq (cache.finish_parameter finish).symm step.target

/-- The reindexed nonlinear finish owner keeps the original last Step's exact initial box. -/
theorem finishOwner_box (cache : Cache first last increment admitted firstInside lastInside width)
    (step : Step last increment) (finish : span.upper = lastReference) :
    (cache.finishOwner step finish).track.initial.box = step.target.track.initial.box :=
  Transport.castOwnerParameter_initial_box (cache.finish_parameter finish).symm step.target

/-- Compare the first fixed-box branch at the start with the identical original first Step root cache.

The original Step target refines its own source Seed box. The existing
fixed-budget comparison therefore identifies these same-radicand channels
without changing the Step owner, sampled states or retained root certificate.
-/
def startEquivalent (cache : Cache first last increment admitted firstInside lastInside width)
    (step : Step first increment) (start : span.lower = reference) :
    NamedEquivalent
      (ownerRootName (cache.path.nonzero 0 (by decide +kernel)) (cache.path.First 0 (by decide +kernel)))
      step.root.value.name := by
  have refines : (cache.startOwner step start).track.initial.box.Refines first.seed.owner.track.initial.box := by
    rewrite [cache.startOwner_box]
    exact step.target_refines
  have compared := cache.path.firstRetained 0 (by decide +kernel) (cache.startOwner step start) refines
  have retained : ownerRootName (cache.startOwner step start).parameterNonzero (cache.startOwner step start) =
      step.root.value.name := by
    unfold startOwner
    rewrite [ownerRootName_castOwnerParameter, step.root_eq]
    rfl
  exact NamedEquivalent.transport rfl retained compared

/-- Compare the second fixed-box branch at the finish with the identical original last Step root cache.

This uses the original last Step's own source Seed refinement. Agreement
between the first and second nonlinear branches requires separate cross-window
evidence and is not asserted by this endpoint comparison.
-/
def finishEquivalent (cache : Cache first last increment admitted firstInside lastInside width)
    (step : Step last increment) (finish : span.upper = lastReference) :
    NamedEquivalent
      (ownerRootName (cache.path.nonzero 1 (by decide +kernel)) (cache.path.Second 1 (by decide +kernel)))
      step.root.value.name := by
  have refines : (cache.finishOwner step finish).track.initial.box.Refines last.seed.owner.track.initial.box := by
    rewrite [cache.finishOwner_box]
    exact step.target_refines
  have compared := cache.path.secondRetained 1 (by decide +kernel) (cache.finishOwner step finish) refines
  have retained : ownerRootName (cache.finishOwner step finish).parameterNonzero (cache.finishOwner step finish) =
      step.root.value.name := by
    unfold finishOwner
    rewrite [ownerRootName_castOwnerParameter, step.root_eq]
    rfl
  exact NamedEquivalent.transport rfl retained compared

end Cache

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Parameter.Path

end
