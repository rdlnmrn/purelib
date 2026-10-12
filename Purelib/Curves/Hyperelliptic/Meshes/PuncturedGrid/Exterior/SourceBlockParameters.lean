module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceCuts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedSegmentCuts
import Purelib.Geometry.Rectangle.SourceIntervals
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.RectangularSegmentRefinement
import Purelib.Riemann.Paths.RectangularSegmentSplitting
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedSourceSplits
public import Purelib.Riemann.Integration.RectangularAxisParameterRange
import Mathlib.Algebra.Ring.Defs
import Mathlib.Order.Defs.PartialOrder
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentQueries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Integration.PreparedParentSplitSelection
import Purelib.Riemann.Integration.PreparedParentSplitting
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Tactic.Ring

public section

/-! Midpoint search selects a source occurrence; the actual mesh cuts then
certify the whole side block and its executable parent-parameter interval. -/
section

open Purelib.Curves
open Purelib.Geometry
open Purelib.Riemann

open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian)

open Purelib.Riemann.Normalization

open Purelib.Data.Rat.Fraction.Compatibility
variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {differential other : Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
  {occurrence :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence
    regular domains differential} {target : Normalization.InverseRootPolynomial.Coordinate} {minimum stage fine : Nat}
  {box otherBox : Rational.Box}
  {sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential stage box}
  {otherSample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap other stage otherBox}
  {plan : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences.PairedSourcePlan occurrence other target
    minimum}

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior

namespace SourceBlockParameters

/-- Read the selected coordinate with the sign of the chosen traversal orientation. -/
@[expose] def signedAxis (vertical forward : Bool) (point : Normalization.InverseRootPolynomial.Gaussian) : Coordinate
  :=
  if forward then Rectangle.SourceIntervals.axisCoordinate vertical point else -Rectangle.SourceIntervals.axisCoordinate
    vertical point

/-- Orient a physical interval by preserving it forward or negating and exchanging its endpoints in reverse. -/
@[expose] def signedInterval (forward : Bool) (physical : Rectangle.Partition.PreparedAxisPartitions.Interval) :
  Rectangle.Partition.PreparedAxisPartitions.Interval :=

  open Purelib.Data.Rat in if forward then physical else ⟨-physical.upper, -physical.lower,
    Fraction.Order.Arithmetic.neg_lt_neg_direct physical.ordered⟩

end SourceBlockParameters

namespace SourceBlockParameters

/-- The midpoint of the physical block in the selected signed orientation. -/
@[expose] def blockMidpoint (forward : Bool) (physical : Rectangle.Partition.PreparedAxisPartitions.Interval) :
  Coordinate :=
  ((Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockParameters.signedInterval forward physical).lower +
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockParameters.signedInterval forward physical).upper) / 2

/-- Every retained mesh cut lies outside the interior of an original physical block in either orientation. -/
theorem signed_outside {columns rows : Nat} {geometry : Normalization.RectangularInverseModels.Geometry columns rows}
    {cuts : Paths.RectangularSegmentSplitting.GridCuts geometry} {meshBox : Rational.Box}
    (mesh : Meshes.RectangularObservationMesh.ObservationMesh cuts meshBox) (vertical forward : Bool)
    {physical : Rectangle.Partition.PreparedAxisPartitions.Interval} (member : physical ∈
      Rectangle.SourceIntervals.axisIntervals mesh vertical)
    {point : Normalization.InverseRootPolynomial.Gaussian} (present : point ∈ mesh.points) :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockParameters.signedAxis vertical forward point ≤
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockParameters.signedInterval forward physical).lower ∨
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockParameters.signedInterval forward physical).upper ≤
        Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockParameters.signedAxis vertical forward point := open
        Purelib.Data.Rat in by
  have outside := Rectangle.SourceIntervals.axis_cut_outside mesh vertical member present
  cases forward with
  | true => exact outside
  | false =>
    exact outside.elim (fun bound => Or.inr (Fraction.Order.Arithmetic.neg_le_neg_direct bound))
      (fun bound => Or.inl (Fraction.Order.Arithmetic.neg_le_neg_direct bound))

/-- Read the signed initial coordinate of the parent at the original paired source index. -/
@[expose] def sourceAxisFirst (evaluated :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences.PairedSourcePlan.ParentEvaluation plan sample
  otherSample fine) (index : Fin evaluated.retained.length)
    (vertical forward : Bool) : Coordinate :=
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockParameters.signedAxis vertical forward
      ((Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedSourceSplits.indexedEntry evaluated
      index).plan.parent.edge.point 0)

/-- Read the signed final coordinate of that same retained source parent. -/
@[expose] def sourceAxisLast (evaluated :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences.PairedSourcePlan.ParentEvaluation plan sample
  otherSample fine) (index : Fin evaluated.retained.length)
    (vertical forward : Bool) : Coordinate :=
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockParameters.signedAxis vertical forward
      ((Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedSourceSplits.indexedEntry evaluated
      index).plan.parent.edge.point 1)

end SourceBlockParameters

set_option genInjectivity false in
/-- The original paired source occurrence and executable parameter range covering one physical side block.

The retained finite index, strict signed endpoint order and parameter correspondence preserve the selected parent. -/
structure SourceBlockParameters (evaluated :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences.PairedSourcePlan.ParentEvaluation plan sample
  otherSample fine)
    (vertical forward : Bool) (physical : Rectangle.Partition.PreparedAxisPartitions.Interval) where
  /-- The original paired source occurrence index selected for the physical block. -/ index : Fin
    evaluated.retained.length
  /-- The selected parent's signed endpoints are strictly increasing. -/ ordered :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockParameters.sourceAxisFirst evaluated index vertical forward <
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockParameters.sourceAxisLast evaluated index vertical forward
  /-- The executable parent parameter range corresponding to the signed physical interval. -/ parameters :
    Integration.RectangularAxisParameterRange.AxisParameterRange
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockParameters.sourceAxisFirst evaluated index vertical forward)
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockParameters.sourceAxisLast evaluated index vertical forward)
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockParameters.signedInterval forward physical)

constructive_injectivity SourceBlockParameters

namespace SourceBlockParameters

/-- Find the original source parent crossing the physical block midpoint and construct its complete parameter range.

Retained mesh cuts certify that both physical endpoints lie in the selected parent interval. -/
@[expose] def sourceBlockParameters
    {prepared :
      SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation
      regular domains differential} {previous :
      Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.CommonCuts domains}
    (selected : SourceCuts prepared previous) (member :
      occurrence ∈ prepared.occurrences)
    {coarseDepth : Nat} {fixed : (sheet : Fin 2) →
      Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Preflights domains sheet} {meshTarget :
      Normalization.InverseRootPolynomial.Coordinate}
    (request : Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest.TwoSheetRequest (fun sheet =>
      Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.build domains selected.cuts sheet
      coarseDepth) fixed meshTarget)
    (sheet : Fin 2) (position : Fin base.faces.regulars.length)
    (evaluated : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences.PairedSourcePlan.ParentEvaluation
      plan sample otherSample fine) (vertical forward : Bool) (physical :
      Rectangle.Partition.PreparedAxisPartitions.Interval)
    (present : physical ∈ Rectangle.SourceIntervals.axisIntervals ((request.entries.get sheet).meshes.entries.get
      position) vertical)
    (lower : Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockParameters.signedAxis vertical forward
      occurrence.start ≤ Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockParameters.blockMidpoint forward
      physical)
    (upper : Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockParameters.blockMidpoint forward physical <
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockParameters.signedAxis vertical forward occurrence.finish) :
    SourceBlockParameters evaluated vertical forward
      physical := by
  let found := Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedSourceSplits.locateSourceAxis evaluated
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockParameters.signedAxis vertical forward)
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockParameters.blockMidpoint forward physical) lower upper
  let split := Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedSourceSplits.sourceSplit evaluated found.index
  have firstPoint := Paths.RectangularSegmentRefinement.coordinate_point_mem
    split.split split.split.partition.lower_mem
  have lastPoint := Paths.RectangularSegmentRefinement.coordinate_point_mem
    split.split split.split.partition.upper_mem
  rw [Rectangle.Partition.PreparedSegmentCuts.point_zero] at firstPoint
  rw [Rectangle.Partition.PreparedSegmentCuts.point_one] at lastPoint
  have firstOutside := Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockParameters.signed_outside
    ((request.entries.get sheet).meshes.entries.get position) vertical forward present
    (selected.requested_split_points request sheet position member split.member firstPoint)
  have lastOutside := Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockParameters.signed_outside
    ((request.entries.get sheet).meshes.entries.get position) vertical forward present
    (selected.requested_split_points request sheet position member split.member lastPoint)
  have between := Rectangle.Partition.PreparedSegmentCuts.midpoint_bounds
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockParameters.signedInterval forward physical)
  have firstBound : Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockParameters.sourceAxisFirst evaluated
    found.index vertical forward ≤ (Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockParameters.signedInterval
    forward physical).lower := by
    rcases firstOutside with bound | bound
    · exact bound
    · exact (not_lt_of_ge (bound.trans found.lower) between.2).elim
  have lastBound : (Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockParameters.signedInterval forward
    physical).upper ≤ Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockParameters.sourceAxisLast evaluated
    found.index vertical forward := by
    rcases lastOutside with bound | bound
    · exact (not_lt_of_ge (bound.trans between.1.le) found.upper).elim
    · exact bound
  have ordered := found.lower.trans_lt found.upper
  exact ⟨found.index, ordered, Integration.RectangularAxisParameterRange.AxisParameterRange.build _ _ _ ordered
    ⟨firstBound, lastBound⟩⟩

end SourceBlockParameters

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockParameters

/-- The retained signed parameter range gives the actual forward or reverse physical-axis correspondence. -/
theorem correspondence {evaluated :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences.PairedSourcePlan.ParentEvaluation plan sample
  otherSample fine}
    {vertical forward : Bool} {physical : Rectangle.Partition.PreparedAxisPartitions.Interval}
    (block : SourceBlockParameters evaluated vertical
      forward physical) :
    Rectangle.SourceIntervals.AxisCorrespondence vertical
      ((Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedSourceSplits.indexedEntry evaluated
        block.index).plan.parent.edge.point 0)
      ((Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedSourceSplits.indexedEntry evaluated
        block.index).plan.parent.edge.point 1) block.parameters.range physical := open Purelib.Data.Rat in by
  cases forward with
  | true =>
    exact Or.inl ⟨Fraction.Order.Arithmetic.sub_pos_direct block.ordered, block.parameters.first_eq,
      block.parameters.last_eq⟩
  | false =>
    have ordered := Fraction.Order.Arithmetic.neg_lt_neg_direct block.ordered
    change -(-Rectangle.SourceIntervals.axisCoordinate vertical
      ((Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedSourceSplits.indexedEntry evaluated
      block.index).plan.parent.edge.point 1)) <
      -(-Rectangle.SourceIntervals.axisCoordinate vertical
        ((Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedSourceSplits.indexedEntry evaluated
        block.index).plan.parent.edge.point 0)) at ordered
    rw [neg_neg, neg_neg] at ordered
    have negative := Fraction.Order.Arithmetic.sub_lt_sub_right_direct ordered (Rectangle.SourceIntervals.axisCoordinate
      vertical ((Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedSourceSplits.indexedEntry evaluated
      block.index).plan.parent.edge.point 0))
    rw [sub_self] at negative
    exact Or.inr ⟨negative, Fraction.Field.unneg_affine block.parameters.first_eq, Fraction.Field.unneg_affine
      block.parameters.last_eq⟩

/-- Locate the retained parameter range in its original source split on the requested shared mesh. -/
@[expose] def locate {evaluated :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences.PairedSourcePlan.ParentEvaluation plan sample
  otherSample fine}
    {vertical forward : Bool} {physical : Rectangle.Partition.PreparedAxisPartitions.Interval}
    (block : SourceBlockParameters evaluated vertical
      forward physical)
    {prepared :
      SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation
      regular domains differential} {previous :
      Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.CommonCuts domains}
    (selected : SourceCuts prepared previous) (member :
      occurrence ∈ prepared.occurrences)
    {coarseDepth : Nat} {fixed : (sheet : Fin 2) →
      Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Preflights domains sheet} {meshTarget :
      Normalization.InverseRootPolynomial.Coordinate}
    (request : Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest.TwoSheetRequest (fun sheet =>
      Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.build domains selected.cuts sheet
      coarseDepth) fixed meshTarget)
    (sheet : Fin 2) (position : Fin base.faces.regulars.length)
    (present : physical ∈ Rectangle.SourceIntervals.axisIntervals ((request.entries.get sheet).meshes.entries.get
      position) vertical) :
    Paths.RectangularSegmentRefinement.Subinterval
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedSourceSplits.sourceSplit evaluated block.index).split
      block.parameters.range :=
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedSourceSplits.locateIndexedSourceInterval selected member request
    sheet position evaluated block.index vertical physical present
    block.parameters.range block.parameters.within block.correspondence

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockParameters

end
