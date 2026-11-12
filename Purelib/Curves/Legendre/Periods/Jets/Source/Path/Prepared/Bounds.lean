module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field

/-! # Initial-patch ratio on an actual retained prepared source

The ratio reads the SAME original Cell.patch, not its selected Request.model.
The complete original cell equation identifies that initial owner across
independent numerical floors/Targets on one retained patch and count.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent

open Purelib
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis} {patch : PreparedPatch parent} {count floor : Nat}
    {covered : (patch.neighborhood count).box.Contains (parent.edge.point 1)}
    {start finish : LiftedPoint 2} {original : LiftedPath 2 start finish} {stage : Nat}
    {targets : CellEndpoints.Targets original stage}

/-- Read the initial-model bound ratio from the SAME retained original source patch, without any new acquisition. -/
def initialRatio (prepared : PreparedParent patch count floor covered targets) : Rational :=
  prepared.preparation.cell.patch.base.model.bound / (2 * prepared.preparation.cell.patch.inverseErrorScale)

/-- The ratio reads that actual retained initial patch, not its selected numerical model. -/
theorem initialRatio_eq (prepared : PreparedParent patch count floor covered targets) :
    prepared.initialRatio = prepared.preparation.cell.patch.base.model.bound /
      (2 * prepared.preparation.cell.patch.inverseErrorScale) := by
  unfold initialRatio
  rfl

/-- The original initial bound and positive inverse-error scale give a nonnegative actual ratio. -/
theorem initialRatio_nonnegative (prepared : PreparedParent patch count floor covered targets) :
    0 ≤ prepared.initialRatio :=
  Order.Field.div_nonneg_direct prepared.preparation.cell.patch.base.model.bound_nonnegative
    (Order.Arithmetic.mul_pos_direct (by decide +kernel)
      prepared.preparation.cell.patch.inverseErrorScale_positive).le

/-- The complete original cell equation retains the SAME patch/count ratio across numerical preparations. -/
theorem initialRatio_eq_neighborhood (prepared : PreparedParent patch count floor covered targets) :
    prepared.initialRatio = (patch.neighborhood count).base.model.bound /
      (2 * (patch.neighborhood count).inverseErrorScale) :=
  congrArg (fun cell : Cell (parameter := parameter) (liftedCell parent) =>
    cell.patch.base.model.bound / (2 * cell.patch.inverseErrorScale)) prepared.preparation.cell_eq

/-- Independent original preparations on the SAME actual patch and count have the same initial ratio.

Only their complete original cell equations are used. No Frame/curve
identity is inferred from coefficient equality, and neither source model,
neighborhood, Point nor request is constructed by this readback.
-/
theorem initialRatio_eq_of_patch
    {firstStart firstFinish lastStart lastFinish : LiftedPoint 2}
    {firstPath : LiftedPath 2 firstStart firstFinish} {lastPath : LiftedPath 2 lastStart lastFinish}
    {firstStage lastStage firstFloor lastFloor : Nat}
    {firstTargets : CellEndpoints.Targets firstPath firstStage}
    {lastTargets : CellEndpoints.Targets lastPath lastStage}
    (first : PreparedParent patch count firstFloor covered firstTargets)
    (last : PreparedParent patch count lastFloor covered lastTargets) :
    first.initialRatio = last.initialRatio :=
  first.initialRatio_eq_neighborhood.trans last.initialRatio_eq_neighborhood.symm

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent

end
