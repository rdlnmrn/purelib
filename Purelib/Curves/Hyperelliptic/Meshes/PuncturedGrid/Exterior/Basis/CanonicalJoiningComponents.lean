module
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.List.Flatten
import Purelib.Data.List.Map

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.CornerTotals
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Integration.Path.ConjugatePathReadback
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Topology.Polygon.Stokes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.CanonicalJoiningWord
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SideRemainders
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceGeometry
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentSideSources
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Vector.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.GridLiftedBoundaryLoops
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Surface.Cut.PrimitiveJumps
import Purelib.Topology.Surface.Sewing.PrimitiveSewing

open Purelib.Algebra

open Purelib.Curves

open Purelib.Data

open Purelib.Integration

open Purelib.Riemann

public section

/-! Assemble canonical joining polygons on the exact parity-selected exterior components. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid
namespace ExteriorProgram

open Purelib

open Purelib.Data.Rat

open Purelib.Riemann.Normalization

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
    regular domains differential}

namespace AllSurfacePreparation

/-- A component retains its original occurrence membership in the complete surface. -/
theorem component_occurrence_member (whole :
  ExteriorProgram.AllSurfacePreparation
  regular domains differential)
    (component :
      SurfaceComponent
      regular domains differential) (member : component ∈ whole.components)
    (outer : Fin component.prepared.occurrences.length) :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt component.prepared.occurrences outer ∈
      whole.occurrences := by
  rw [whole.occurrences_eq]
  exact Data.List.Flatten.mem_flatMap.mpr ⟨component, member, List.getElem_mem outer.isLt⟩

/-- The canonical preparation has exactly the exterior tours, without intercomponent bridges. -/
theorem built_component_words :

      ((build
      (lifted := lifted) regular domains differential).components.map
      (fun component => component.program.indexed)) = lifted.exteriorBoundaries := by
  change ((Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms.exteriorPrograms lifted differential).map
    (SurfaceComponent.build
    regular domains)).map
    (fun component => component.program.indexed) = _
  rw [Data.List.Map.map_map]
  exact Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms.exteriorPrograms_indexed lifted differential

/-- Map polygon area separately over the actual closed exterior components. -/
theorem built_component_areas (value : Topology.Polygon.Stokes.OrientedEdge lifted.vertices.count →
  Topology.Polygon.Stokes.PrimitivePoint) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum
      ((build
      regular domains differential).components.map
      (fun component => Path.PairedIncrementArea.area (component.program.indexed.map value))) =
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (lifted.exteriorBoundaries.map (fun word => Path.PairedIncrementArea.area
        (word.map value))) := by
  rw [←
    built_component_words
    (regular := regular) (domains := domains) (differential := differential), Data.List.Map.map_map]
  rfl

variable {stage : Nat} (cache : Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics domains
  stage)
  (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus)
  (readings : (row : Fin genus) → Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings
    (cache.get row) lifted.mesh)

/-- Each component word uses its own retained occurrence list and the common Newton cache. -/
theorem component_cached_word (whole :
  ExteriorProgram.AllSurfacePreparation
  regular domains differential)
    (component :
      SurfaceComponent
      regular domains differential) (member : component ∈ whole.components) :
    (List.ofFn fun outer =>
      let occurrence := Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt
        component.prepared.occurrences outer
      let total := Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.CornerTotals.SharedPerimeter.cachedIncrement
        (lifted := lifted) cache coefficients
        occurrence.sideOccurrence.position occurrence.sideOccurrence.sheet occurrence.sideOccurrence.side
      if occurrence.sourceForward then total else Topology.Polygon.Stokes.PrimitivePoint.zero.sub total) =
      component.program.indexed.map (fun edge => Path.ConjugatePathReadback.conjugateDiagonal (FiniteSum.Fin.sumFin fun
        row => coefficients row *
        Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation lifted.mesh (readings row).values edge)) :=
  component.prepared.cached_increment_word whole (whole.component_occurrence_member component member) cache coefficients
    readings

/-- The full cached joining sum is precisely the Newton exterior polygon sum in both degree shapes. -/
theorem built_cached_joining_areas :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum
      ((build
      (lifted := lifted) regular domains differential).components.map
      (fun component => Path.PairedIncrementArea.area (List.ofFn fun outer =>
        let occurrence := Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt
          component.prepared.occurrences outer
        let total := Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.CornerTotals.SharedPerimeter.cachedIncrement
          (lifted := lifted) cache coefficients
          occurrence.sideOccurrence.position occurrence.sideOccurrence.sheet occurrence.sideOccurrence.side
        if occurrence.sourceForward then total else Topology.Polygon.Stokes.PrimitivePoint.zero.sub total))) =
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (lifted.exteriorBoundaries.map (fun word => Path.PairedIncrementArea.area
        (word.map
        (fun edge => Path.ConjugatePathReadback.conjugateDiagonal (FiniteSum.Fin.sumFin fun row => coefficients row *
          Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation lifted.mesh (readings row).values
            edge))))) := by
  apply Eq.trans _
    (built_component_areas
    (regular := regular) (domains := domains) (differential := differential) _)
  apply congrArg Data.Gaussian.Norm.Sum.Basic.gaussianSum
  apply Data.List.Map.map_congr_left
  intro component member
  exact congrArg Path.PairedIncrementArea.area

      (component_cached_word
      cache coefficients readings
      (build
      regular domains differential) component member)

end AllSurfacePreparation
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
