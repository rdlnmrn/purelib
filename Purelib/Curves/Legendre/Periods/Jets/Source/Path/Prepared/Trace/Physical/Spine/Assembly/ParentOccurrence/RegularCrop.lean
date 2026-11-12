module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Physical.Spine.Assembly.ParentOccurrence.Trace
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFragmentCells.Comparison.Endpoints.Physical
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFragmentCells.Comparison.Endpoints.Physical.Entries
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Riemann.Integration.PreparedConstantModels.Query
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Readings.UniformPreparedRequests
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames

/-! # The actual selected paid physical crop on a regular leaf's two original Points

One original physical occurrence lookup supplies its exact crop operation.
The regular leaf consumer reuses both endpoint Queries and old Point/Entry
caches. It creates two explicit new stationary joins, not another paid path,
query, Point, classification, domain, analytic split or reading bank.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell

namespace PreparedParents.Trace.Physical.Spine.Sources.ParentOccurrence

open Purelib
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits (PrimitiveAxes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFragmentCells (PrimitiveFragmentCell)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFragmentCells.PrimitiveFragmentCell (RegularRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFragmentCells.PrimitiveFragmentCell.RegularRequest
  (UpperEndpoint)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Geometry.Rectangle (AxisPartition)
open Purelib.Geometry.Rectangle.Partition
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Riemann.Integration.PreparedConstantModels (PreparedEdge)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces RegularLocation)
open Purelib.Riemann.Readings.UniformPreparedRequests (LocalRequest)

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
variable {count floor : Nat} {sheet : Fin 2}
variable {baseStart baseFinish : LiftedPoint 2} {original : LiftedPath 2 baseStart baseFinish} {stage : Nat}
variable {targets : CellEndpoints.Targets original stage}
variable {parent : CenteredEdge (Fibre.frameCurve frame) basis}
variable (occurrence : ParentOccurrence (frame := frame) (basis := basis) (count := count) (floor := floor)
  (sheet := sheet) (targets := targets) parent)

variable {branches : BranchIsolation.Data (Fibre.frameCurve frame)}
variable {higher : 1 < (Fibre.frameCurve frame).polynomial.natDegree}
variable {bank : BranchCellBank (Fibre.frameCurve frame) branches higher} {faces : PuncturedFaces bank}
variable {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {axes : PrimitiveAxes bank.grid}
variable {localCount : Nat} {requestTarget : Rational} {request : LocalRequest parent localCount requestTarget}
variable {cuts : List Rational} {partition : AxisPartition 0 1 cuts}
variable {interval : PreparedAxisPartitions.Interval} {domains : FaceDomainBank frames faces.regulars}
variable {fragment : PrimitiveFragmentCell axes parent partition interval}
variable {location : RegularLocation faces.regulars fragment.cell}

/-- Select the SAME actual paid Trace occurrence once and construct its Point-owned regular-leaf crop.

The complete original frame, basis, sheet, targets, parent, selected Segment
and child index determine the actual View. The retained lower Query and
upper endpoint Query are consumed unchanged; all signed endpoint evidence
is derived from their original request and the SAME old Points.
-/
def cropSamples (retained : RegularRequest domains request fragment location) (upper : retained.UpperEndpoint)
    (query : PreparedEdge.Query parent.edge interval.lower fragment.lower_inside) :
    upper.SampleCrop
      (occurrence.cropComparisons interval.lower interval.upper fragment.lower_inside fragment.upper_inside
        interval.ordered.le) query :=
  let physical := occurrence.cropComparisons interval.lower interval.upper fragment.lower_inside fragment.upper_inside
    interval.ordered.le
  UpperEndpoint.SampleCrop.build upper physical query

/-- The same selected crop derives an upper Entry from the actual lower Entry and retained Point-owned path.

The crop's one-vertex geometry follows its original stored View and whole
parent transport. That proof is erased: it does not execute a second
lookup or read the old source/moving/reset comparison functions at runtime.
The supplied SampleCrop certifies the erased path relation; the original
lower sheet is the only runtime output retained by this Entry operation.
-/
def cropEntry (retained : RegularRequest domains request fragment location) (upper : retained.UpperEndpoint)
    (query : PreparedEdge.Query parent.edge interval.lower fragment.lower_inside)
    (cropped : upper.SampleCrop
      (occurrence.cropComparisons interval.lower interval.upper fragment.lower_inside fragment.upper_inside
        interval.ordered.le) query) :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.FaceModels.Entry retained.compared.shared.models
      fragment.last upper.sample.owner :=
  cropped.entry (occurrence.cropComparisons_vertices interval.lower interval.upper fragment.lower_inside
    fragment.upper_inside interval.ordered.le query upper.query)

/-- The automatic physical occurrence consumer preserves its original lower face-sheet index. -/
theorem cropEntry_sheet (retained : RegularRequest domains request fragment location) (upper : retained.UpperEndpoint)
    (query : PreparedEdge.Query parent.edge interval.lower fragment.lower_inside)
    (cropped : upper.SampleCrop
      (occurrence.cropComparisons interval.lower interval.upper fragment.lower_inside fragment.upper_inside
        interval.ordered.le) query) :
    (occurrence.cropEntry retained upper query cropped).sheet = retained.compared.acquired.entry.sheet :=
  cropped.entry_sheet (occurrence.cropComparisons_vertices interval.lower interval.upper fragment.lower_inside
    fragment.upper_inside interval.ordered.le query upper.query)

end PreparedParents.Trace.Physical.Spine.Sources.ParentOccurrence

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell

end
