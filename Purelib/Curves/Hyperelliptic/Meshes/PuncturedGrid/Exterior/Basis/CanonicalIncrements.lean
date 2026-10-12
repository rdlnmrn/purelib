module
import Purelib.Data.List.Membership
import Purelib.Data.List.Flatten
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.List.Map
import Purelib.Topology.Polygon.Stokes

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.CornerTotals
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Integration.Path.ConjugatePathReadback
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedBoundaryLoops
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceIncrementReadback
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalPhysicalBoundary
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SideRemainders
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceGeometry
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentSideSources
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Vector.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Surface.Cut.PrimitiveJumps
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts

open Purelib.Algebra

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.CornerTotals

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceIncrementReadback

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid

open Purelib.Data.List

open Purelib.Integration.Path

open Purelib.Riemann.Meshes

open Purelib.Topology.Polygon.Stokes

open Purelib.Topology.Surface.Sewing

public section

/-! Exact canonical edge values on the retained physical exterior occurrences. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid
namespace ExteriorProgram

open Purelib

open Purelib.Data.Rat
open Purelib.Riemann.Meshes.GridLiftedDualSteps (GridSide)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
  (SurfaceOccurrence)
open Purelib.Riemann.Normalization
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.CornerTotals.SharedPerimeter (cachedIncrement)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.EndpointReadback.SharedPerimeter (cornerValue)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Riemann.Integration.PreparedEdgeRecasting (recastCenteredEdge)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
  (AllSurfacePreparation)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes (Numerics)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues (edgeValuation)
variable {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Riemann.Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Riemann.Meshes.LiftedPuncturedGrid base} {differential other :
    Curves.Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
  {occurrence :
    SurfaceOccurrence
    regular domains differential}

open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr)
open Purelib.Topology.Polygon.Stokes (PrimitivePoint)
open Purelib.Integration.Path.ConjugatePathReadback (conjugateDiagonal)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.CornerTotals.SharedPerimeter (cachedIncrement)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceIncrementReadback.SharedPerimeter
  (weighted_occurrence_source)

namespace SurfaceOccurrence
/-- Project the exact side source selected by the original occurrence placement. -/
theorem side_source_project (occurrence : ExteriorProgram.SurfaceOccurrence regular domains differential) :
    occurrence.sideOccurrence.source.project lifted.mesh.triangulation.faces = occurrence.placement.indexed :=
  (congrArg (fun source => source.project lifted.mesh.triangulation.faces) occurrence.side_source).trans
    occurrence.placement.location.sourceEdge_project
end SurfaceOccurrence

namespace AllSurfacePreparation
variable (whole :
  ExteriorProgram.AllSurfacePreparation
  regular domains differential)
  (occurrence :
    SurfaceOccurrence
    regular domains differential) (member : occurrence ∈ whole.occurrences)

include member

/-- Each retained occurrence projects into the original exterior tours. -/
theorem occurrence_exterior_member : occurrence.placement.indexed ∈ lifted.exteriorBoundaries.flatten := by
  have mapped : occurrence.placement.indexed ∈ whole.occurrences.map (fun item => item.placement.indexed) :=
    Map.mem_map_of_mem member
  rw [whole.indexed_eq] at mapped
  exact mapped

/-- Exterior occurrences are physical-boundary occurrences, with multiplicity retained. -/
theorem occurrence_physical_member :
    occurrence.sideOccurrence.source.project lifted.mesh.triangulation.faces ∈ lifted.boundaryLoops.flatten := by
  rw [occurrence.side_source_project, LiftedPuncturedGrid.boundaryLoops, Data.List.Flatten.flatten_append]
  exact Data.List.Membership.mem_append.mpr (Or.inl (whole.occurrence_exterior_member occurrence member))

/-- No chart-change estimate is needed on the unique physical-boundary source. -/
theorem occurrence_canonical_increment
    (values : Fin lifted.mesh.triangles.length → PrimitiveSewing.PrimitiveValues 3) :
    occurrence.sideOccurrence.source.increment values =
      CanonicalEdgeValues.edgeValuation lifted.mesh values occurrence.placement.indexed := by
  have equal := CanonicalPhysicalBoundary.canonical_physical_source occurrence.sideOccurrence.source
    (whole.occurrence_physical_member occurrence member) values
  rw [occurrence.side_source_project] at equal
  exact equal.symm

variable {stage : Nat} (cache : Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics
  domains stage)
  (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus)
  (readings : (row : Fin genus) → Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings
    (cache.get row) lifted.mesh)

/-- Signed corner displacements equal the same weighted canonical cochain used by Newton. -/
theorem occurrence_cached_canonical :
    (let total := SharedPerimeter.cachedIncrement (lifted := lifted) cache coefficients
      occurrence.sideOccurrence.position occurrence.sideOccurrence.sheet occurrence.sideOccurrence.side
    if occurrence.sourceForward then total else PrimitivePoint.zero.sub total) =
      ConjugatePathReadback.conjugateDiagonal (FiniteSum.Fin.sumFin fun row => coefficients row *
        CanonicalEdgeValues.edgeValuation lifted.mesh (readings row).values occurrence.placement.indexed) := by
  apply (SharedPerimeter.weighted_occurrence_source cache coefficients readings occurrence).symm.trans
  apply congrArg ConjugatePathReadback.conjugateDiagonal
  apply FiniteSum.Fin.sumFin_congr
  intro row
  exact congrArg (coefficients row * ·) (whole.occurrence_canonical_increment occurrence member (readings row).values)

end AllSurfacePreparation
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
