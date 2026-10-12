module
import Purelib.Data.List.Membership
import Purelib.Data.List.Flatten
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.List.Map

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleSourceChords
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.FacePerimeters
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SideOccurrenceReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TriangleSourceUniqueness
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Topology.Mesh.TriangleSourceUniqueness
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SideRemainders
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BranchHoleSourceComparison
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalSideArea
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalizedNumerics
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TriangleCornerSources
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Vector.Dependent
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.GridLiftedBoundaryLoops
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Polygon.Stokes
import Purelib.Tactic.Ring

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid

public section

/-! Exterior cap preparations for different differentials retain the same
ordered triangle sources. This identifies source readings, not independently
prepared primitive paths or their internal areas. -/
section
open
  ExteriorProgram.AllSurfacePreparation

open Purelib.Curves
open Purelib.Data
open Purelib.Data.Rat
open Purelib.Riemann
open Purelib

open Purelib.Data.List
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram

open Purelib.Riemann.Normalization

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {differential other : Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid
namespace ExteriorProgram
namespace AllSurfacePreparation

/-- The ordered triangle-corner source edges of the retained original exterior occurrences. -/
@[expose] def sources (prepared :
  ExteriorProgram.AllSurfacePreparation
    regular domains differential) : List (Topology.Surface.Sewing.SewnPrimitiveContacts.SourceEdge
      lifted.mesh.triangles.length) :=
  prepared.occurrences.map (fun occurrence => occurrence.placement.location.sourceEdge)

end AllSurfacePreparation
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid
namespace ExteriorProgram
namespace AllSurfacePreparation

open
  ExteriorProgram.AllSurfacePreparation
  in
/-- Projecting the retained source edges gives exactly the flattened original exterior boundary list. -/
theorem sources_project (prepared :
  ExteriorProgram.AllSurfacePreparation
    regular domains differential) :
    prepared.sources.map (fun source => source.project lifted.mesh.triangulation.faces) =
      lifted.exteriorBoundaries.flatten := by
  rw [sources, Map.map_map]
  exact (Data.List.Map.map_congr_left (fun occurrence _ => occurrence.placement.location.sourceEdge_project)).trans
    prepared.indexed_eq

end AllSurfacePreparation
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid
namespace ExteriorProgram
namespace AllSurfacePreparation

open
  ExteriorProgram.AllSurfacePreparation
  in
/-- Every retained source projecting to the original physical exterior boundary has positive orientation. -/
private theorem exterior_positive (sources : List (Topology.Surface.Sewing.SewnPrimitiveContacts.SourceEdge
  lifted.mesh.triangles.length))
    (projected : sources.map (fun source => source.project lifted.mesh.triangulation.faces) =
      lifted.exteriorBoundaries.flatten) :
    ∀ source ∈ sources, Purelib.Topology.Mesh.TriangleSourceUniqueness.SourceEdge.Positive source
      lifted.mesh.triangulation.faces := by
  intro source member
  apply Hyperelliptic.Meshes.PuncturedGrid.BranchHoleSourceComparison.physicalSource_positive lifted source
  change _ ∈ (lifted.exteriorBoundaries ++ _).flatten
  rw [Flatten.flatten_append]
  exact Membership.mem_append.mpr (Or.inl (projected ▸ Data.List.Map.mem_map_of_mem member))

/-- Physical source uniqueness preserves order, repetitions, sheets and
triangle corners, even when the other list came from another differential. -/
theorem sources_eq (prepared :
  ExteriorProgram.AllSurfacePreparation
    regular domains differential)
    (retained : List (Topology.Surface.Sewing.SewnPrimitiveContacts.SourceEdge lifted.mesh.triangles.length))
    (projected : retained.map (fun source => source.project lifted.mesh.triangulation.faces) =
      lifted.exteriorBoundaries.flatten) :
    prepared.sources = retained :=
  Topology.Mesh.TriangleSourceUniqueness.SourceEdge.list_eq_of_project_eq lifted.mesh.orientedEdges_unique
    (Hyperelliptic.Meshes.PuncturedGrid.TriangleSourceUniqueness.LiftedMesh.corners_injective lifted.mesh) _ _

      (exterior_positive
      _ prepared.sources_project)
      (exterior_positive
      _ projected)
    (prepared.sources_project.trans projected.symm)

/-- Exterior preparations for two differentials have the same ordered triangle-source list.

Physical source uniqueness preserves all repetitions, sheets and corners; it does not identify the separately retained
primitive paths. -/
theorem differential_sources_eq (prepared :
  ExteriorProgram.AllSurfacePreparation
    regular domains differential)
    (next :
      ExteriorProgram.AllSurfacePreparation
      regular domains other) : prepared.sources = next.sources :=
  prepared.sources_eq next.sources next.sources_project

/-- The actual requested cap entries, including a request for a different
standard differential, read precisely the retained fine-side source list. -/
theorem request_sources_eq (prepared :
  ExteriorProgram.AllSurfacePreparation
    regular domains differential)
    {next :
      ExteriorProgram.AllSurfacePreparation
      regular domains other} {target areaTarget : Fraction.Rational} {floor : Nat}
    (requested : Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.Request
      next target areaTarget floor) :
    prepared.sources = requested.entries.map (fun entry => entry.occurrence.placement.location.sourceEdge) := by
  apply prepared.sources_eq
  rw [Map.map_map]
  exact (Data.List.Map.map_congr_left (fun entry _ => entry.occurrence.placement.location.sourceEdge_project)).trans
    requested.indexed_eq

end AllSurfacePreparation
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram

variable {cuts : Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.CommonCuts domains} {coarseDepth :
  Nat} {fixed : (sheet : Fin 2) → Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Preflights
  domains sheet}
  {meshTarget : Fraction.Rational} {i j : Fin genus} {stage : Nat} {cache :
    Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics domains stage}
  {meshRequest : Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest.TwoSheetRequest (fun sheet =>
    Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.build domains cuts sheet coarseDepth) fixed
    meshTarget}

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid
namespace ExteriorProgram
namespace AllSurfacePreparation

open
  ExteriorProgram.AllSurfacePreparation
  in
/-- Read the bilinear source chords on the actual cap request's entries.
Only the source list is transported; all fine-side internal areas remain. -/
theorem fineRemainder_request_chords (prepared :
  ExteriorProgram.AllSurfacePreparation
    regular domains differential)
    {next :
      ExteriorProgram.AllSurfacePreparation
      regular domains other} {target areaTarget : Fraction.Rational} {floor : Nat}
    (requested : Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.Request
      next target areaTarget floor)
    (perimeters : Matched.FacePerimeters (request := meshRequest)
      cache.normalize i j)
    (left : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings (cache.get i) lifted.mesh)
      (right : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings (cache.get j) lifted.mesh)
      :
    prepared.fineRemainder perimeters left right + Data.Gaussian.Norm.Sum.Basic.gaussianSum (requested.entries.map
      (fun entry => Hyperelliptic.Meshes.PuncturedGrid.HoleSourceChords.BranchCellBank.TriangleReadings.sourceChord left
        right entry.occurrence.placement.location.sourceEdge)) =
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (prepared.occurrences.map (fun occurrence =>
        Hyperelliptic.Meshes.PuncturedGrid.SideOccurrenceReadings.LiftedPuncturedGrid.occurrenceFineArea perimeters
        occurrence.sideOccurrence)) := by
  have chords := congrArg (fun entries => Data.Gaussian.Norm.Sum.Basic.gaussianSum (entries.map
    (Hyperelliptic.Meshes.PuncturedGrid.HoleSourceChords.BranchCellBank.TriangleReadings.sourceChord left right)))
    (prepared.request_sources_eq requested)
  dsimp only [sources] at chords
  simp only [Map.map_map, Function.comp_def, -eq_self, -iff_self] at chords
  rw [← chords]
  dsimp only
    [fineRemainder]
  generalize prepared.occurrences = occurrences
  induction occurrences with
  | nil => exact add_zero _
  | cons head tail ih =>
      change
        (SurfaceOccurrence.fineRemainder
        head perimeters left right + _) +
        (Hyperelliptic.Meshes.PuncturedGrid.HoleSourceChords.BranchCellBank.TriangleReadings.sourceChord left right
          head.placement.location.sourceEdge + _) =
          Hyperelliptic.Meshes.PuncturedGrid.SideOccurrenceReadings.LiftedPuncturedGrid.occurrenceFineArea perimeters
          head.sideOccurrence + _
      change ((Hyperelliptic.Meshes.PuncturedGrid.SideOccurrenceReadings.LiftedPuncturedGrid.occurrenceFineArea
        perimeters head.sideOccurrence -
        Hyperelliptic.Meshes.PuncturedGrid.HoleSourceChords.BranchCellBank.TriangleReadings.sourceChord left right
          head.placement.location.sourceEdge) + _) + _ = _
      calc
        _ = Hyperelliptic.Meshes.PuncturedGrid.SideOccurrenceReadings.LiftedPuncturedGrid.occurrenceFineArea perimeters
          head.sideOccurrence +
            (Data.Gaussian.Norm.Sum.Basic.gaussianSum (tail.map (fun occurrence => occurrence.fineRemainder perimeters
              left right)) +
             Data.Gaussian.Norm.Sum.Basic.gaussianSum (tail.map (fun occurrence =>
               Hyperelliptic.Meshes.PuncturedGrid.HoleSourceChords.BranchCellBank.TriangleReadings.sourceChord left
               right occurrence.placement.location.sourceEdge))) := by ring1
        _ = _ := congrArg
          (Hyperelliptic.Meshes.PuncturedGrid.SideOccurrenceReadings.LiftedPuncturedGrid.occurrenceFineArea perimeters
          head.sideOccurrence + ·) ih

end AllSurfacePreparation
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram

end
