module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.List.Flatten

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Riemann.Integration.PreparedParentSplitting
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Paths.RectangularSegmentRefinement
import Purelib.Riemann.Paths.RectangularSegmentSplitting
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest
public import Purelib.Geometry.Rectangle.SourceIntervals
import Init.Data.List.Basic
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
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
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Paths.PreparedPathParentCaches
meta import Mathlib.Tactic.Linter.Lint

open Purelib

open Purelib.Curves.Hyperelliptic

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes

open Purelib.Data.List

open Purelib.Geometry.Rectangle

open Purelib.Geometry.Rectangle.Partition

open Purelib.Riemann.Integration

open Purelib.Riemann.Integration.PreparedParentSplitting

open Purelib.Riemann.Paths

public section

/-! The shared cut bank retains every endpoint of the original exterior
preparation. Existing cuts, including observation points, are preserved. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
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
open Purelib.Riemann.Normalization
open Purelib.Riemann.Integration.PreparedParentSplitting (ParentSplits)
open Purelib.Riemann.Paths.RectangularSegmentSplitting (SegmentSplit)
variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Purelib.Riemann.Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Purelib.Riemann.Meshes.LiftedPuncturedGrid base} {differential :
    Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}

set_option genInjectivity false in
/-- The shared cut bank extended by every actual endpoint of the original exterior source preparation.

Membership certificates retain both all previous cuts and the complete original source-point bank. -/
structure SourceCuts (prepared : ExteriorProgram.AllSurfacePreparation regular domains differential) (previous :
  RegularMeshes.CommonCuts domains) where
  /-- The cached flattening of actual mesh points from the original retained exterior occurrences. -/ sourcePoints :
    List InverseRootPolynomial.Gaussian
  /-- The source-point cache is exactly the original occurrence mesh-point flattening. -/ sourcePoints_eq : sourcePoints
    = prepared.occurrences.flatMap (fun occurrence => occurrence.compared.entered.mesh.points)
  /-- The retained common cut bank containing previous and actual source points. -/ cuts : RegularMeshes.CommonCuts
    domains
  /-- Every previous retained cut point survives in the enlarged common bank. -/ previous_included : ∀ point ∈
    previous.points, point ∈ cuts.points
  /-- Every actual cached original source point belongs to the enlarged common bank. -/ source_included : ∀ point ∈
    sourcePoints, point ∈ cuts.points

constructive_injectivity SourceCuts

namespace SourceCuts
variable {prepared :
  SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation
  regular domains differential} {previous :
  Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.CommonCuts domains}

/-- Only concatenate cached point banks. Parent preparation, splitting, root ownership and numerical values are not
recomputed. -/
@[expose] def build (prepared : ExteriorProgram.AllSurfacePreparation regular domains differential) (previous :
  RegularMeshes.CommonCuts domains) : SourceCuts prepared
  previous :=
  let sourcePoints := prepared.occurrences.flatMap (fun occurrence => occurrence.compared.entered.mesh.points)
  let cuts : RegularMeshes.CommonCuts domains :=
    ⟨previous.points ++ sourcePoints, fun position sheet point member =>
      List.mem_append_left _ (previous.includes position sheet point member)⟩
  ⟨sourcePoints, rfl, cuts, fun _ member => List.mem_append_left _ member,
    fun _ member => List.mem_append_right _ member⟩

/-- Every original previous cut point remains present in the selected shared bank. -/
theorem previous_points (selected : SourceCuts prepared
  previous) {point : InverseRootPolynomial.Gaussian}
    (member : point ∈ previous.points) : point ∈ selected.cuts.points := by
  exact selected.previous_included point member

/-- Every actual retained exterior occurrence mesh point belongs to the selected shared bank. -/
theorem occurrence_points (selected : SourceCuts prepared
  previous)
    {occurrence : ExteriorProgram.SurfaceOccurrence regular domains differential} (member : occurrence ∈
      prepared.occurrences)
    {point : InverseRootPolynomial.Gaussian} (present : point ∈ occurrence.compared.entered.mesh.points) : point ∈
      selected.cuts.points := by
  apply selected.source_included
  rw [selected.sourcePoints_eq]
  exact Flatten.mem_flatMap.mpr ⟨occurrence, member, present⟩

/-- Every endpoint in an original retained parent split belongs to the selected shared bank. -/
theorem split_points (selected : SourceCuts prepared
  previous)
    {occurrence : ExteriorProgram.SurfaceOccurrence regular domains differential} (member : occurrence ∈
      prepared.occurrences)
    {parent : PreparedSubdivisionModelCore.CenteredEdge curve differential}
    {split : RectangularSegmentSplitting.SegmentSplit occurrence.compared.entered.domain.cuts (parent.edge.point 0)
      (parent.edge.point 1)}
    (retained : ParentSplits.Member split occurrence.compared.entered.mesh.splits)
    {point : InverseRootPolynomial.Gaussian} (present : point ∈ split.points) : point ∈ selected.cuts.points := by
  apply selected.occurrence_points member
  rw [occurrence.compared.entered.mesh.points_eq]
  exact List.mem_append_left _ (ParentSplits.point_mem retained present)

/-- The same finite bank is present on every face and both sheets. -/
theorem mesh_split_points (selected : SourceCuts prepared
  previous) (sheet : Fin 2) (depth : Nat)
    (position : Fin base.faces.regulars.length)
    {occurrence : ExteriorProgram.SurfaceOccurrence regular domains differential} (member : occurrence ∈
      prepared.occurrences)
    {parent : PreparedSubdivisionModelCore.CenteredEdge curve differential}
    {split : RectangularSegmentSplitting.SegmentSplit occurrence.compared.entered.domain.cuts (parent.edge.point 0)
      (parent.edge.point 1)}
    (retained : ParentSplits.Member split occurrence.compared.entered.mesh.splits)
    {point : InverseRootPolynomial.Gaussian} (present : point ∈ split.points) :
    point ∈ ((RegularMeshes.build domains selected.cuts sheet depth).entries.get position).points := by
  rw [RegularMeshes.build_points]
  exact selected.split_points member retained present

/-- Every original retained source-split endpoint belongs to the requested actual mesh on every face and sheet. -/
theorem requested_split_points (selected : SourceCuts
  prepared previous) {coarseDepth : Nat}
    {fixed : (sheet : Fin 2) → RegularMeshes.Preflights domains sheet} {target : InverseRootPolynomial.Coordinate}
    (request : TwoSheetBilinearRequest.TwoSheetRequest (fun sheet => RegularMeshes.build domains selected.cuts sheet
      coarseDepth) fixed target)
    (sheet : Fin 2) (position : Fin base.faces.regulars.length)
    {occurrence : ExteriorProgram.SurfaceOccurrence regular domains differential} (member : occurrence ∈
      prepared.occurrences)
    {parent : PreparedSubdivisionModelCore.CenteredEdge curve differential}
    {split : RectangularSegmentSplitting.SegmentSplit occurrence.compared.entered.domain.cuts (parent.edge.point 0)
      (parent.edge.point 1)}
    (retained : ParentSplits.Member split occurrence.compared.entered.mesh.splits)
    {point : InverseRootPolynomial.Gaussian} (present : point ∈ split.points) :
    point ∈ ((request.entries.get sheet).meshes.entries.get position).points := by
  rw [(request.entries.get sheet).mesh_eq, ((request.entries.get sheet).entries.get position).mesh_eq]
  exact selected.mesh_split_points sheet coarseDepth position member retained present

/-- Source-piece selection on the actual shared mesh no longer asks the caller to prove that fragment endpoints survived
common-cut construction. -/
@[expose] def locateInterval (selected : SourceCuts
  prepared previous) {coarseDepth : Nat}
    {fixed : (sheet : Fin 2) → RegularMeshes.Preflights domains sheet} {target : InverseRootPolynomial.Coordinate}
    (request : TwoSheetBilinearRequest.TwoSheetRequest (fun sheet => RegularMeshes.build domains selected.cuts sheet
      coarseDepth) fixed target)
    (sheet : Fin 2) (position : Fin base.faces.regulars.length)
    {occurrence : ExteriorProgram.SurfaceOccurrence regular domains differential} (member : occurrence ∈
      prepared.occurrences)
    {parent : PreparedSubdivisionModelCore.CenteredEdge curve differential}
    (split : RectangularSegmentSplitting.SegmentSplit occurrence.compared.entered.domain.cuts (parent.edge.point 0)
      (parent.edge.point 1))
    (retained : ParentSplits.Member split occurrence.compared.entered.mesh.splits)
    (vertical : Bool) (physical : PreparedAxisPartitions.Interval)
    (present : physical ∈ SourceIntervals.axisIntervals ((request.entries.get sheet).meshes.entries.get position)
      vertical)
    (range : PreparedAxisPartitions.Interval) (within : 0 ≤ range.lower ∧ range.upper ≤ 1)
    (correspondence : SourceIntervals.AxisCorrespondence vertical
      (parent.edge.point 0) (parent.edge.point 1) range physical) : RectangularSegmentRefinement.Subinterval split range
        :=
  SourceIntervals.locateSourceInterval ((request.entries.get sheet).meshes.entries.get position) split
    (fun _ present => selected.requested_split_points request sheet position member retained present)
    vertical physical present range within correspondence

end SourceCuts

namespace SourceCuts

set_option genInjectivity false in
/-- Retain the automatically constructed reciprocal data and the original exterior source preparation alongside the cut
bank that contains its points. -/
structure SourcePreparation (domains : DomainBanks.FaceDomainBank lifted.frames base.faces.regulars)
    (differential : Differentials.Basic.Differential genus) where
  /-- The cached original exterior reciprocal collar. -/ collar : ReciprocalExteriorCollar.Data curve
  /-- The cached inner reciprocal data on that exact retained collar. -/ cap : ReciprocalInnerInverse.Data curve collar
  /-- The cached regular reciprocal bounds on the original cap. -/ regular : RegularBounds.Data cap
  /-- The complete retained original exterior source preparation on these domains. -/ prepared :
    ExteriorProgram.AllSurfacePreparation regular domains differential
  /-- The original shared common cuts before adding exterior source points. -/ previous : RegularMeshes.CommonCuts
    domains
  /-- The retained enlarged cut bank containing these exact original exterior source points. -/ selected :
    SourceCuts prepared previous

constructive_injectivity SourcePreparation

end SourceCuts

namespace SourceCuts.SourcePreparation

/-- Cache the original reciprocal geometry and complete exterior source preparation, then extend the original common
cuts with its retained mesh points. -/
@[expose] def build (domains : DomainBanks.FaceDomainBank lifted.frames base.faces.regulars)
    (differential : Differentials.Basic.Differential genus) :
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceCuts.SourcePreparation domains differential :=
  let collar := ReciprocalExteriorCollar.Data.build curve
  let cap := ReciprocalInnerInverse.Data.build curve collar 0
  let regular := RegularBounds.Data.build cap
  let prepared := AllSurfacePreparation.build regular domains differential
  let previous := CommonCuts.build domains
  ⟨collar, cap, regular, prepared, previous,
    SourceCuts.build prepared previous⟩

end SourceCuts.SourcePreparation

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior
