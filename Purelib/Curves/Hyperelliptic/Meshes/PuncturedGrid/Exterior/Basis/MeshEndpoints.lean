module
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBlocks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockParameters
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceGeometry
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Geometry.Rectangle.SourceIntervals
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.RectangularSegmentSplitting
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentEndpoints
import Purelib.Riemann.Readings.RectangularObservationEndpoints
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentJunctions
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SideRemainders
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentSideSources
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Vector.Dependent
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Readings.RectangularObservationAssembly

public section

/-! Canonical mesh endpoints determine exhaustive common-parent run boundaries. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.MeshEndpoints

open Purelib
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
open Purelib.Geometry.Rectangle
open Purelib.Geometry.Rectangle.Partition
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes (RegularMeshes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes (CommonCuts Preflights)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest (TwoSheetRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
  (SurfaceOccurrence AllSurfacePreparation)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBlocks (ParentBlock)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockParameters (signedAxis signedInterval
  blockMidpoint)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.FragmentFamilies (signedMeshSpan
  blockMidpoint_mesh_bounds)
open
  Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence
  (sourceVertical sourceForward source_span_endpoints)
open Purelib.Riemann.Normalization
open Purelib.Riemann.Normalization.RectangularInverseModels (Geometry)
open Purelib.Riemann.Paths.RectangularSegmentSplitting (GridCuts)
open Purelib.Riemann.Integration.RectangularAxisParameterRange (AxisParameterRange)
open Purelib.Geometry.Rectangle.SourceIntervals (axisCoordinate)
open Purelib.Data.Rat.Fraction.Compatibility
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBank (ParentBlockBank)
variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Purelib.Riemann.Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Purelib.Riemann.Meshes.LiftedPuncturedGrid base} {differential other :
    Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
  {occurrence :
    SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence
    regular domains differential}

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockParameters (signedAxis signedInterval)

/-- A forward block at the original occurrence's initial axis coordinate starts at retained parent zero and parameter
zero. -/
private theorem at_axis_start {vertical : Bool} {physical : PreparedAxisPartitions.Interval}
    (block : ParentBlocks.ParentBlock occurrence vertical true physical) (axis : vertical = occurrence.sourceVertical)
    (forward : occurrence.sourceForward = true)
    (start : physical.lower = SourceIntervals.axisCoordinate vertical occurrence.start) :
    block.index.val = 0 ∧ block.firstParameter = 0 := by
  cases axis
  exact block.at_occurrence_start forward start

/-- A forward block at the original occurrence's terminal axis coordinate ends at the final retained parent and
parameter one. -/
private theorem at_axis_finish {vertical : Bool} {physical : PreparedAxisPartitions.Interval}
    (block : ParentBlocks.ParentBlock occurrence vertical true physical) (axis : vertical = occurrence.sourceVertical)
    (forward : occurrence.sourceForward = true)
    (finish : physical.upper = SourceIntervals.axisCoordinate vertical occurrence.finish) :
    block.index.val + 1 = occurrence.compared.entered.cache.parents.length ∧ block.lastParameter = 1 := by
  cases axis
  exact block.at_occurrence_finish forward finish

namespace ParentBlockBank
open Purelib.Riemann.Meshes.RectangularObservationMesh (ObservationMesh)
variable {columns rows : Nat} {geometry : Purelib.Riemann.Normalization.RectangularInverseModels.Geometry columns rows}
  {cuts : Purelib.Riemann.Paths.RectangularSegmentSplitting.GridCuts geometry}
  {meshBox : Purelib.Geometry.Rational.Box} {mesh :
    Purelib.Riemann.Meshes.RectangularObservationMesh.ObservationMesh cuts meshBox}

/-- The actual face box identifies the first and last physical intervals with the occurrence span and supplies both
terminal parent certificates. -/
theorem horizontal_endpoints (bank : ParentBank.ParentBlockBank occurrence mesh false true)
    (axis : occurrence.sourceVertical = false) (forward : occurrence.sourceForward = true)
    (boxEq : meshBox =
      (base.faces.regulars[occurrence.sideOccurrence.position.val]'occurrence.sideOccurrence.position.isLt).cell.box) :
    let first := bank.get (Fin.cast mesh.boundaryColumns_eq 0)
    let last := bank.get (Fin.cast mesh.boundaryColumns_eq (Fin.last mesh.boundaryColumns))
    first.index.val = 0 ∧ first.firstParameter = 0 ∧
      last.index.val + 1 = occurrence.compared.entered.cache.parents.length ∧ last.lastParameter = 1 := by
  have start := occurrence.source_span_endpoints.1
  have finish := occurrence.source_span_endpoints.2
  simp only [SurfaceOccurrence.sourceSpan, axis, forward, SourceBlockParameters.signedAxis,
    SourceBlockParameters.signedInterval, if_pos (rfl : true = true), if_neg Bool.false_ne_true, -eq_self, -iff_self]
      at start finish
  have initial := Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.MeshEndpoints.at_axis_start (bank.get
    (Fin.cast mesh.boundaryColumns_eq 0)) axis.symm forward
    (mesh.x_first.trans (by rw [boxEq]; exact start.symm))
  have final := Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.MeshEndpoints.at_axis_finish (bank.get
    (Fin.cast mesh.boundaryColumns_eq (Fin.last mesh.boundaryColumns))) axis.symm forward
    (mesh.x_last.trans (by rw [boxEq]; exact finish.symm))
  exact ⟨initial.1, initial.2, final.1, final.2⟩

/-- The actual face box identifies the first and last physical intervals with the occurrence span and supplies both
terminal parent certificates. -/
theorem vertical_endpoints (bank : ParentBank.ParentBlockBank occurrence mesh true true)
    (axis : occurrence.sourceVertical = true) (forward : occurrence.sourceForward = true)
    (boxEq : meshBox =
      (base.faces.regulars[occurrence.sideOccurrence.position.val]'occurrence.sideOccurrence.position.isLt).cell.box) :
    let first := bank.get (Fin.cast mesh.boundaryRows_eq 0)
    let last := bank.get (Fin.cast mesh.boundaryRows_eq (Fin.last mesh.boundaryRows))
    first.index.val = 0 ∧ first.firstParameter = 0 ∧
      last.index.val + 1 = occurrence.compared.entered.cache.parents.length ∧ last.lastParameter = 1 := by
  have start := occurrence.source_span_endpoints.1
  have finish := occurrence.source_span_endpoints.2
  simp only [SurfaceOccurrence.sourceSpan, axis, forward, SourceBlockParameters.signedAxis,
    SourceBlockParameters.signedInterval, if_pos (rfl : true = true), -eq_self, -iff_self] at start finish
  have initial := Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.MeshEndpoints.at_axis_start (bank.get
    (Fin.cast mesh.boundaryRows_eq 0)) axis.symm forward
    (mesh.y_first.trans (by rw [boxEq]; exact start.symm))
  have final := Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.MeshEndpoints.at_axis_finish (bank.get
    (Fin.cast mesh.boundaryRows_eq (Fin.last mesh.boundaryRows))) axis.symm forward
    (mesh.y_last.trans (by rw [boxEq]; exact finish.symm))
  exact ⟨initial.1, initial.2, final.1, final.2⟩

end ParentBlockBank
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.MeshEndpoints
