module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Budgets
public import Purelib.Riemann.RootContinuation.FixedRootBoxPath.Preparation.Reading
public import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.RootContinuation.FixedRootBoxPath
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring

/-! # Actual factor preparations on retained spatial segments

Each original sharp-box ClearSegment supplies its physical affine points and
ambient containment. The normalized quadratic and remaining affine cofactor
use those same points, original budgets and internally derived time variation.
Their complete original preparation results are cached, not represented by
new paths or by a chart-time affine witness.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.RootContinuation

variable {site : Fin 2} {parameter : Canonical} {quarter : UnitCircuitQuarter}
variable {positive : (0 : Fraction.Rational) < 2}
variable {actual : Transport.Quarter site parameter 2 quarter positive}
variable {first : Fraction.Rational} {firstInside : FixedRootBoxPath.Inside first}
variable {source : Transport.Reading actual first firstInside} {anchor : Parameter.Anchor source.lift}
variable {start finish : Canonical}

/-- The exact original normalized fixed-box path type on the supplied source seed and cached budget. -/
@[expose] def NormalPath (budgets : Budgets anchor) :=
  FixedRootBoxPath.PathData budgets.normalized budgets.normalized

/-- The exact original cofactor fixed-box path type on the identical prepared quarter reference budget. -/
@[expose] def UnitPath (budgets : Budgets anchor) :=
  FixedRootBoxPath.PathData budgets.unit budgets.unit

/-- Construct the actual normalized quadratic path along the unchanged retained physical spatial segment.

Every original segment point belongs to the same sharp source square. The
computed movement budget and nonzero certificate are paid there; the actual
affine spatial edge and common quadratic coefficient pay time variation.
-/
def normalPath (budgets : Budgets anchor)
    (segment : ClearSegment (Paths.polynomial parameter) (sourceBox anchor) start finish)
    (within : segment.WithinAmbient) : NormalPath budgets :=
  { point := fun time => Clearance.normalizedRadicand site parameter (segment.pointAt time)
    nonzero := fun time inside => budgets.normalized_nonzero (segment.pointAt_contains within time inside)
    firstMovement := fun time inside => by
      have paid := budgets.normalized_movement (segment.pointAt_contains within time inside)
      rewrite [Norm.Basic.normSq_eq_canonical] at paid
      exact paid
    secondMovement := fun time inside => by
      have paid := budgets.normalized_movement (segment.pointAt_contains within time inside)
      rewrite [Norm.Basic.normSq_eq_canonical] at paid
      exact paid
    scale := ((Fraction.Cast.fromInt 801 / 64) * Norm.Basic.normSq (halfGap site parameter)) *
      Norm.Basic.normSq (finish - start)
    scale_nonnegative := Fraction.Order.Arithmetic.mul_nonneg_direct
      (Fraction.Order.Arithmetic.mul_nonneg_direct
        (by decide +kernel : (0 : Fraction.Rational) ≤ Fraction.Cast.fromInt 801 / 64)
        (Norm.Basic.normSq_nonneg _)) (Norm.Basic.normSq_nonneg _)
    variation := by
      intro left right leftInside rightInside
      have spatial := Clearance.normalized_distance_le site parameter (Waist.direction quarter first)
        anchor.regular (segment.pointAt_contains within left leftInside)
        (segment.pointAt_contains within right rightInside)
      rewrite [segment.normSq_pointAt_sub_pointAt] at spatial
      rewrite [Norm.Basic.normSq_eq_canonical
        (Clearance.normalizedRadicand site parameter (segment.pointAt left) -
          Clearance.normalizedRadicand site parameter (segment.pointAt right))] at spatial
      have scale_eq : ((Fraction.Cast.fromInt 801 / 64) * Norm.Basic.normSq (halfGap site parameter)) *
          ((left - right) ^ 2 * Norm.Basic.normSq (finish - start)) =
        (((Fraction.Cast.fromInt 801 / 64) * Norm.Basic.normSq (halfGap site parameter)) *
          Norm.Basic.normSq (finish - start)) * (right - left) ^ 2 := by
        rewrite [show (left - right) ^ 2 = (right - left) ^ 2 by ring1]
        ring1
      exact spatial.trans_eq scale_eq }

/-- Construct the actual affine cofactor path on that same original spatial segment and original reference budget. -/
def unitPath (budgets : Budgets anchor)
    (segment : ClearSegment (Paths.polynomial parameter) (sourceBox anchor) start finish)
    (within : segment.WithinAmbient) : UnitPath budgets :=
  { point := fun time => (unitPolynomial site).eval (segment.pointAt time)
    nonzero := fun time inside => budgets.unit_nonzero (segment.pointAt_contains within time inside)
    firstMovement := fun time inside => by
      have paid := budgets.unit_movement (segment.pointAt_contains within time inside)
      rewrite [Norm.Basic.normSq_eq_canonical] at paid
      exact paid
    secondMovement := fun time inside => by
      have paid := budgets.unit_movement (segment.pointAt_contains within time inside)
      rewrite [Norm.Basic.normSq_eq_canonical] at paid
      exact paid
    scale := Norm.Basic.normSq (finish - start)
    scale_nonnegative := Norm.Basic.normSq_nonneg _
    variation := by
      intro left right _ _
      have distance := Clearance.cofactor_distance site (segment.pointAt left) (segment.pointAt right)
      rewrite [segment.normSq_pointAt_sub_pointAt] at distance
      rewrite [Norm.Basic.normSq_eq_canonical
        ((unitPolynomial site).eval (segment.pointAt left) -
          (unitPolynomial site).eval (segment.pointAt right))] at distance
      have scale_eq : (left - right) ^ 2 * Norm.Basic.normSq (finish - start) =
          Norm.Basic.normSq (finish - start) * (right - left) ^ 2 := by
        rewrite [show (left - right) ^ 2 = (right - left) ^ 2 by ring1]
        exact Fraction.Field.mul_comm _ _
      exact distance.le.trans_eq scale_eq }

/-- The normalized path reads the original normalized quadratic at the identical actual spatial segment point. -/
theorem normalPath_point (budgets : Budgets anchor)
    (segment : ClearSegment (Paths.polynomial parameter) (sourceBox anchor) start finish)
    (within : segment.WithinAmbient) (time : Fraction.Rational) :
    (normalPath budgets segment within).point time =
      Clearance.normalizedRadicand site parameter (segment.pointAt time) := by
  unfold normalPath
  rfl

/-- The cofactor path reads the original affine factor at that same retained spatial segment point. -/
theorem unitPath_point (budgets : Budgets anchor)
    (segment : ClearSegment (Paths.polynomial parameter) (sourceBox anchor) start finish)
    (within : segment.WithinAmbient) (time : Fraction.Rational) :
    (unitPath budgets segment within).point time = (unitPolynomial site).eval (segment.pointAt time) := by
  unfold unitPath
  rfl

/-- The normalized path cache retains its entire original factory on the identical physical segment. -/
@[irreducible, expose] def NormalCache (budgets : Budgets anchor)
    (segment : ClearSegment (Paths.polynomial parameter) (sourceBox anchor) start finish)
    (within : segment.WithinAmbient) (path : NormalPath budgets) : Prop :=
  path = normalPath budgets segment within

/-- The cofactor path cache retains its entire original factory on that same physical segment. -/
@[irreducible, expose] def UnitCache (budgets : Budgets anchor)
    (segment : ClearSegment (Paths.polynomial parameter) (sourceBox anchor) start finish)
    (within : segment.WithinAmbient) (path : UnitPath budgets) : Prop :=
  path = unitPath budgets segment within

/-- A retained original fixed-box preparation is the completed factory on its identical supplied path data. -/
@[irreducible, expose] def PreparationCache
    {firstSource secondSource : Canonical}
    {firstOwner : FixedRootBoxBudget.Owner firstSource} {secondOwner : FixedRootBoxBudget.Owner secondSource}
    {firstBudget : FixedRootBoxBudget.Budget firstOwner} {secondBudget : FixedRootBoxBudget.Budget secondOwner}
    (path : FixedRootBoxPath.PathData firstBudget secondBudget)
    (prepared : FixedRootBoxPath.Preparation.Result path) : Prop :=
  prepared = FixedRootBoxPath.Preparation.Result.build path

/-- Complete original path data and preparation caches for both factors on one unchanged physical spatial segment.

The sigma and subtype retain both original PathData values and whole factory
identities. Each preparation belongs to that exact cached path data, including
its original endpoint owners, accepted advances and internal handoffs.
-/
@[expose] def Segment (budgets : Budgets anchor)
    (segment : ClearSegment (Paths.polynomial parameter) (sourceBox anchor) start finish)
    (within : segment.WithinAmbient) :=
  Σ normal : { path : NormalPath budgets // NormalCache budgets segment within path },
    Σ unit : { path : UnitPath budgets // UnitCache budgets segment within path },
      { retained : FixedRootBoxPath.Preparation.Result normal.val × FixedRootBoxPath.Preparation.Result unit.val //
          PreparationCache normal.val retained.1 ∧ PreparationCache unit.val retained.2 }

namespace Segment

/-- Retain completed original factor path/preparation caches without repeating any factory. -/
@[expose] def ofCompleted (budgets : Budgets anchor)
    (segment : ClearSegment (Paths.polynomial parameter) (sourceBox anchor) start finish)
    (within : segment.WithinAmbient)
    (normal : NormalPath budgets) (normal_eq : NormalCache budgets segment within normal)
    (unit : UnitPath budgets) (unit_eq : UnitCache budgets segment within unit)
    (preparedNormal : FixedRootBoxPath.Preparation.Result normal)
    (preparedNormal_eq : PreparationCache normal preparedNormal)
    (preparedUnit : FixedRootBoxPath.Preparation.Result unit)
    (preparedUnit_eq : PreparationCache unit preparedUnit) : Segment budgets segment within :=
  ⟨⟨normal, normal_eq⟩, ⟨⟨unit, unit_eq⟩, ⟨⟨preparedNormal, preparedUnit⟩, preparedNormal_eq, preparedUnit_eq⟩⟩⟩

/-- Prepare both actual factor paths once on the identical retained spatial segment and cached original budgets. -/
def build (budgets : Budgets anchor)
    (segment : ClearSegment (Paths.polynomial parameter) (sourceBox anchor) start finish)
    (within : segment.WithinAmbient) : Segment budgets segment within :=
  let normal := normalPath budgets segment within
  let unit := unitPath budgets segment within
  let preparedNormal := FixedRootBoxPath.Preparation.Result.build normal
  let preparedUnit := FixedRootBoxPath.Preparation.Result.build unit
  ofCompleted budgets segment within normal (by unfold NormalCache; rfl)
    unit (by unfold UnitCache; rfl) preparedNormal (by unfold PreparationCache; rfl)
    preparedUnit (by unfold PreparationCache; rfl)

variable {budgets : Budgets anchor}
variable {segment : ClearSegment (Paths.polynomial parameter) (sourceBox anchor) start finish}
variable {within : segment.WithinAmbient}

/-- Read the entire original normalized path-data cache without rebuilding its physical point function or budget. -/
@[expose] def normal (completed : Segment budgets segment within) : NormalPath budgets := completed.1.val

/-- Read the entire original cofactor path-data cache on the identical original reference owner and budget. -/
@[expose] def unit (completed : Segment budgets segment within) : UnitPath budgets := completed.2.1.val

/-- Read the complete original normalized preparation, including its endpoint caches and genuine accepted moves. -/
@[expose] def preparedNormal (completed : Segment budgets segment within) :
    FixedRootBoxPath.Preparation.Result completed.normal := completed.2.2.val.1

/-- Read the complete original cofactor preparation on its unchanged cached actual physical path. -/
@[expose] def preparedUnit (completed : Segment budgets segment within) :
    FixedRootBoxPath.Preparation.Result completed.unit := completed.2.2.val.2

/-- The normalized path is the completed original factory on the identical retained physical segment. -/
theorem normal_eq (completed : Segment budgets segment within) :
    completed.normal = normalPath budgets segment within := by
  have retained := completed.1.property
  unfold NormalCache at retained
  exact retained

/-- The cofactor path is the completed original factory on the same retained physical segment. -/
theorem unit_eq (completed : Segment budgets segment within) : completed.unit = unitPath budgets segment within := by
  have retained := completed.2.1.property
  unfold UnitCache at retained
  exact retained

/-- The normalized preparation retains the whole original factory on its identical cached normalized path. -/
theorem preparedNormal_eq (completed : Segment budgets segment within) :
    completed.preparedNormal = FixedRootBoxPath.Preparation.Result.build completed.normal := by
  have retained := completed.2.2.property.1
  unfold PreparationCache at retained
  exact retained

/-- The cofactor preparation retains the whole original factory on its identical cached cofactor path. -/
theorem preparedUnit_eq (completed : Segment budgets segment within) :
    completed.preparedUnit = FixedRootBoxPath.Preparation.Result.build completed.unit := by
  have retained := completed.2.2.property.2
  unfold PreparationCache at retained
  exact retained

/-- The actual retained normalized path evaluates the original quadratic at the original physical point. -/
theorem normal_point (completed : Segment budgets segment within) (time : Fraction.Rational) :
    completed.normal.point time = Clearance.normalizedRadicand site parameter (segment.pointAt time) := by
  rewrite [completed.normal_eq]
  exact normalPath_point budgets segment within time

/-- The actual retained cofactor path evaluates the original unit factor at the identical physical point. -/
theorem unit_point (completed : Segment budgets segment within) (time : Fraction.Rational) :
    completed.unit.point time = (unitPolynomial site).eval (segment.pointAt time) := by
  rewrite [completed.unit_eq]
  exact unitPath_point budgets segment within time

end Segment

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors
