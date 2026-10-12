module
import Purelib.Data.Gaussian.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Topology.Polygon.Stokes

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedSourceSplits
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockParameters
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Geometry.Rectangle.SourceIntervals
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockPoints
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryTraceParameters
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentQueries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Topology.Surface.Cut.PrimitiveJumps
meta import Mathlib.Tactic.Linter.Lint

public section

/-! Physical interval endpoints determine exact source parameters. These
readbacks apply in either orientation and do not equate distinct source owners. -/
section

open Purelib
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockParameters
open Purelib.Data.Rat
open Purelib.Geometry.Rectangle
open Purelib.Topology.Polygon.Stokes

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences (PairedSourcePlan)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences.PairedSourcePlan
  (ParentEvaluation)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedSourceSplits (indexedEntry)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues (sourceValues)
open Purelib.Geometry.Rectangle.SourceIntervals (axisCoordinate)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
  (SurfaceOccurrence)
open Purelib.Riemann.Normalization
open Purelib.Data.Gaussian.Basic.Canonical
variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {differential other :
    Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    FaceDomainBank lifted.frames base.faces.regulars}
  {occurrence :
    SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence
    regular domains differential} {target : Coordinate} {minimum
    stage fine : Nat}
  {box otherBox : Purelib.Geometry.Rational.Box}
  {sample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential stage box}
  {otherSample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap other stage otherBox}
  {plan : PairedSourcePlan occurrence
    other target minimum}

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryTraceParameters (parent_parameter_eq
  parent_signed_bounds)
open Purelib.Data.Rat.Fraction.Compatibility

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockParameters
variable {evaluated :
  ParentEvaluation
  plan sample otherSample fine} {vertical : Bool}
  {beforeForward afterForward : Bool}
  {beforePhysical afterPhysical : Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions.Interval}

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockParameters

/-- Consecutive original physical intervals with the identical retained source parent have equal adjoining parameters.
-/
theorem same_parent_parameters
    (before : SourceBlockParameters evaluated vertical beforeForward beforePhysical)
    (after : SourceBlockParameters evaluated vertical afterForward afterPhysical)
    (same : after.index = before.index) (consecutive : afterPhysical.lower = beforePhysical.upper) :
    (SourceBlockParameters.firstParameter after) = (SourceBlockParameters.lastParameter before) := by
  have equal := (SourceBlockParameters.first_axis after).trans (consecutive.trans (SourceBlockParameters.last_axis
    before).symm)
  rw [same] at equal
  exact BoundaryTraceParameters.parent_parameter_eq before.ordered equal

/-- A repeated-coordinate source junction within one parent contributes exactly zero. The two physical point owners need
not be identified. -/
theorem same_parent_source_join
    (before : SourceBlockParameters evaluated vertical beforeForward beforePhysical)
    (after : SourceBlockParameters evaluated vertical afterForward afterPhysical)
    (same : after.index = before.index) (consecutive : afterPhysical.lower = beforePhysical.upper) :
    (PairedFragmentValues.sourceValues (IndexedSourceSplits.indexedEntry evaluated after.index)
      (SourceBlockParameters.firstParameter after)).sub
      (PairedFragmentValues.sourceValues (IndexedSourceSplits.indexedEntry evaluated before.index)
        (SourceBlockParameters.lastParameter before)) = PrimitivePoint.zero := by
  have parameters :=
    same_parent_parameters
    before after same consecutive
  rw [parameters, same]
  apply congrArg₂ PrimitivePoint.mk <;> exact _root_.sub_self _

/-- Matching the physical start to its parent endpoint determines the full run's initial parameter, including reversed
physical sides. -/
theorem first_parameter_of_parent_endpoint
    (block : SourceBlockParameters evaluated vertical beforeForward beforePhysical)
    (aligned : beforePhysical.lower = SourceIntervals.axisCoordinate vertical
      ((IndexedSourceSplits.indexedEntry evaluated block.index).plan.parent.edge.point (if beforeForward then 0 else
        1))) :
    (SourceBlockParameters.firstParameter block) = if beforeForward then 0 else 1 :=
  BoundaryTraceParameters.parent_parameter_eq block.ordered ((SourceBlockParameters.first_axis block).trans aligned)

/-- Alignment with the original parent's final physical endpoint determines the retained last source parameter. -/
theorem last_parameter_of_parent_endpoint
    (block : SourceBlockParameters evaluated vertical beforeForward beforePhysical)
    (aligned : beforePhysical.upper = SourceIntervals.axisCoordinate vertical
      ((IndexedSourceSplits.indexedEntry evaluated block.index).plan.parent.edge.point (if beforeForward then 1 else
        0))) :
    (SourceBlockParameters.lastParameter block) = if beforeForward then 1 else 0 :=
  BoundaryTraceParameters.parent_parameter_eq block.ordered ((SourceBlockParameters.last_axis block).trans aligned)

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockParameters

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockJunctions.SourceBlockParameters

/-- Every unit source parameter lies between the direction-selected physical endpoints of its original parent. -/
private theorem parameter_physical_bounds
    (block : SourceBlockParameters evaluated vertical beforeForward beforePhysical)
    {parameter : InverseRootPolynomial.Coordinate} (inside : 0 ≤ parameter ∧ parameter ≤ 1) :
    SourceIntervals.axisCoordinate vertical ((IndexedSourceSplits.indexedEntry evaluated
      block.index).plan.parent.edge.point (if beforeForward then 0 else 1)) ≤
      SourceIntervals.axisCoordinate vertical ((IndexedSourceSplits.indexedEntry evaluated
        block.index).plan.parent.edge.point parameter) ∧
    SourceIntervals.axisCoordinate vertical ((IndexedSourceSplits.indexedEntry evaluated
      block.index).plan.parent.edge.point parameter) ≤
      SourceIntervals.axisCoordinate vertical ((IndexedSourceSplits.indexedEntry evaluated
        block.index).plan.parent.edge.point (if beforeForward then 1 else 0)) := by
  have bounds := BoundaryTraceParameters.parent_signed_bounds block.ordered inside
  cases beforeForward with
  | true => exact bounds
  | false =>
    have lower := Fraction.Order.Arithmetic.neg_le_neg_direct bounds.2
    have upper := Fraction.Order.Arithmetic.neg_le_neg_direct bounds.1
    simpa only [SourceBlockParameters.signedAxis, if_neg (show (false : Bool) ≠ true from Bool.noConfusion), if_pos
      (show (true : Bool) = true from rfl), neg_neg, -eq_self, -iff_self] using And.intro lower upper

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockJunctions.SourceBlockParameters

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockParameters

/-- The retained physical interval lies within its exact original source parent's physical span. -/
theorem physical_inside (block : SourceBlockParameters evaluated vertical beforeForward
  beforePhysical) :
    SourceIntervals.axisCoordinate vertical ((IndexedSourceSplits.indexedEntry evaluated
      block.index).plan.parent.edge.point (if beforeForward then 0 else 1)) ≤
      beforePhysical.lower ∧ beforePhysical.upper ≤
      SourceIntervals.axisCoordinate vertical ((IndexedSourceSplits.indexedEntry evaluated
        block.index).plan.parent.edge.point (if beforeForward then 1 else 0)) := by
  have lowUnit : 0 ≤ block.parameters.range.lower ∧ block.parameters.range.lower ≤ 1 :=
    ⟨block.parameters.within.1, block.parameters.range.ordered.le.trans block.parameters.within.2⟩
  have highUnit : 0 ≤ block.parameters.range.upper ∧ block.parameters.range.upper ≤ 1 :=
    ⟨block.parameters.within.1.trans block.parameters.range.ordered.le, block.parameters.within.2⟩
  have firstUnit : 0 ≤ (SourceBlockParameters.firstParameter block) ∧ (SourceBlockParameters.firstParameter block) ≤ 1
    := by
    cases beforeForward with
    | true => exact lowUnit
    | false => exact highUnit
  have lastUnit : 0 ≤ (SourceBlockParameters.lastParameter block) ∧ (SourceBlockParameters.lastParameter block) ≤ 1 :=
    by
    cases beforeForward with
    | true => exact highUnit
    | false => exact lowUnit
  exact
    ⟨(SourceBlockJunctions.SourceBlockParameters.parameter_physical_bounds
    block firstUnit).1.trans_eq (SourceBlockParameters.first_axis block),
    (SourceBlockParameters.last_axis block).symm.trans_le
      (SourceBlockJunctions.SourceBlockParameters.parameter_physical_bounds
      block lastUnit).2⟩

/-- A shared physical endpoint that is the end of both selected parent intervals retains both parameter certificates; no
primitive jump is cancelled. -/
theorem parent_handoff_parameters
    (before : SourceBlockParameters evaluated vertical beforeForward beforePhysical)
    (after : SourceBlockParameters evaluated vertical afterForward afterPhysical)
    (consecutive : afterPhysical.lower = beforePhysical.upper)
    (beforeEnd : beforePhysical.upper = SourceIntervals.axisCoordinate vertical
      ((IndexedSourceSplits.indexedEntry evaluated before.index).plan.parent.edge.point (if beforeForward then 1 else
        0)))
    (parentJoin : SourceIntervals.axisCoordinate vertical
      ((IndexedSourceSplits.indexedEntry evaluated before.index).plan.parent.edge.point (if beforeForward then 1 else
        0)) =
      SourceIntervals.axisCoordinate vertical ((IndexedSourceSplits.indexedEntry evaluated
        after.index).plan.parent.edge.point (if afterForward then 0 else 1))) :
    (SourceBlockParameters.lastParameter before) = (if beforeForward then 1 else 0) ∧
      (SourceBlockParameters.firstParameter after) = (if afterForward then 0 else 1) :=
  ⟨last_parameter_of_parent_endpoint before beforeEnd,

      first_parameter_of_parent_endpoint
      after (consecutive.trans (beforeEnd.trans parentJoin))⟩

/-- Adjacent physical pieces selected from separated parent spans must meet at both parent endpoints. This supplies the
run boundaries geometrically. -/
theorem handoff_of_separated
    (before : SourceBlockParameters evaluated vertical beforeForward beforePhysical)
    (after : SourceBlockParameters evaluated vertical afterForward afterPhysical)
    (consecutive : afterPhysical.lower = beforePhysical.upper)
    (separated : SourceIntervals.axisCoordinate vertical
      ((IndexedSourceSplits.indexedEntry evaluated before.index).plan.parent.edge.point (if beforeForward then 1 else
        0)) ≤
      SourceIntervals.axisCoordinate vertical ((IndexedSourceSplits.indexedEntry evaluated
        after.index).plan.parent.edge.point (if afterForward then 0 else 1))) :
    (SourceBlockParameters.lastParameter before) = (if beforeForward then 1 else 0) ∧
      (SourceBlockParameters.firstParameter after) = (if afterForward then 0 else 1) := by
  have left :=
    (physical_inside
    before).2
  have right :=
    (physical_inside
    after).1.trans_eq consecutive
  have beforeEnd := _root_.le_antisymm left (separated.trans right)
  have parentJoin := _root_.le_antisymm separated (right.trans left)
  exact
    parent_handoff_parameters
    before after consecutive beforeEnd parentJoin

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockParameters

end
