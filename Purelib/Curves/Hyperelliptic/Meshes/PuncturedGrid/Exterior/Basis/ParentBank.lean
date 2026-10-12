module
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.FragmentFamilies
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockParameters
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceCuts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest
import Purelib.Data.Vector.Dependent
import Purelib.Geometry.Rectangle.SourceIntervals
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.RectangularSegmentSplitting
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBlocks
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceGeometry
import Init.GetElem
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.PartialOrder
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SideRemainders
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentSideSources
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Meshes.PuncturedGridFaces

open Purelib

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBlocks

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes

open Purelib.Data.Vector

open Purelib.Geometry

open Purelib.Geometry.Rectangle

open Purelib.Riemann.Meshes

open Purelib.Riemann.Paths

@[expose] public section

/-! Prepare the complete common-parent assignment bank on the physical mesh. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBank
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
  PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence
  (sourceVertical sourceForward source_span_endpoints)
open Purelib.Riemann.Normalization
open Purelib.Riemann.Normalization.RectangularInverseModels (Geometry)
open Purelib.Riemann.Paths.RectangularSegmentSplitting (GridCuts)
open Purelib.Riemann.Integration.RectangularAxisParameterRange (AxisParameterRange)
open Purelib.Geometry.Rectangle.SourceIntervals (axisCoordinate)
open Purelib.Data.Rat.Fraction.Compatibility
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

/-- Every physical axis interval retains its original-parent index and split. The finite bank is prepared before
acquiring numerical source samples. -/
def ParentBlockBank (occurrence : ExteriorProgram.SurfaceOccurrence regular domains differential)
    {columns rows : Nat} {geometry : RectangularInverseModels.Geometry columns rows}
    {cuts : RectangularSegmentSplitting.GridCuts geometry} {meshBox : Rational.Box}
    (mesh : RectangularObservationMesh.ObservationMesh cuts meshBox) (vertical forward : Bool) :=
  Data.Vector.DependentVector (fun i : Fin (SourceIntervals.axisIntervals mesh vertical).length =>
    ParentBlocks.ParentBlock occurrence vertical forward ((SourceIntervals.axisIntervals mesh vertical)[i.val]'i.isLt))

/-- One occurrence-span comparison locates every interval on the requested shared mesh. Parent search and source-piece
selection are cached together. -/
def ParentBlock.buildBank
    {prepared : ExteriorProgram.AllSurfacePreparation regular domains differential} {previous : RegularMeshes.CommonCuts
      domains}
    (selected : SourceCuts prepared previous) (member : occurrence ∈ prepared.occurrences)
    {coarseDepth : Nat} {fixed : (sheet : Fin 2) → RegularMeshes.Preflights domains sheet} {meshTarget :
      InverseRootPolynomial.Coordinate}
    (request : TwoSheetBilinearRequest.TwoSheetRequest
      (fun sheet => RegularMeshes.build domains selected.cuts sheet coarseDepth) fixed meshTarget)
    (sheet : Fin 2) (position : Fin base.faces.regulars.length)
    (vertical forward : Bool)
    (lower : SourceBlockParameters.signedAxis vertical forward occurrence.start ≤
      (FragmentFamilies.signedMeshSpan ((request.entries.get sheet).meshes.entries.get position) vertical
        forward).lower)
    (upper : (FragmentFamilies.signedMeshSpan ((request.entries.get sheet).meshes.entries.get position) vertical
      forward).upper ≤
      SourceBlockParameters.signedAxis vertical forward occurrence.finish) :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBank.ParentBlockBank occurrence ((request.entries.get
      sheet).meshes.entries.get position) vertical forward :=
  DependentVector.ofFn (fun i =>
    let mesh := (request.entries.get sheet).meshes.entries.get position
    let physical := (SourceIntervals.axisIntervals mesh vertical)[i.val]'i.isLt
    have present : physical ∈ SourceIntervals.axisIntervals mesh vertical := List.getElem_mem i.isLt
    have bounds := FragmentFamilies.blockMidpoint_mesh_bounds mesh vertical forward present
    ParentBlock.build selected member request sheet position vertical forward physical present
      (lower.trans bounds.1.le) (bounds.2.trans_le upper))

/-- The actual occurrence supplies its own face, sheet, orientation and span. No per-interval parent assignment or
endpoint alignment is supplied by a caller. -/
def ParentBlock.forOccurrence
    {prepared : ExteriorProgram.AllSurfacePreparation regular domains differential} {previous : RegularMeshes.CommonCuts
      domains}
    (selected : SourceCuts prepared previous) (member : occurrence ∈ prepared.occurrences)
    {coarseDepth : Nat} {fixed : (sheet : Fin 2) → RegularMeshes.Preflights domains sheet} {meshTarget :
      InverseRootPolynomial.Coordinate}
    (request : TwoSheetBilinearRequest.TwoSheetRequest
      (fun sheet => RegularMeshes.build domains selected.cuts sheet coarseDepth) fixed meshTarget) :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBank.ParentBlockBank occurrence
      ((request.entries.get occurrence.sideOccurrence.sheet).meshes.entries.get occurrence.sideOccurrence.position)
      (SurfaceOccurrence.sourceVertical occurrence) (SurfaceOccurrence.sourceForward occurrence) :=
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBank.ParentBlock.buildBank selected member request
    occurrence.sideOccurrence.sheet occurrence.sideOccurrence.position
    (SurfaceOccurrence.sourceVertical occurrence) (SurfaceOccurrence.sourceForward occurrence)
      (SurfaceOccurrence.source_span_endpoints occurrence).1.le
    (SurfaceOccurrence.source_span_endpoints occurrence).2.symm.le

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBank
