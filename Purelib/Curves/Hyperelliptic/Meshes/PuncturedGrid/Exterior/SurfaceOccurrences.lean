module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.List.Map
import Purelib.Data.List.Flatten
import Purelib.Data.Gaussian.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Polynomial.Geometry.ClearPath

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PeriodSegmentBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFaceSegments
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ReciprocalCapPreparation
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Paths.PreparedClearPathModels
import Purelib.Riemann.Paths.PreparedExteriorPathGeometry
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Topology.SquareRootContinuationChain
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourFaces
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ReciprocalAreaComparison
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.GridLiftedBoundaryLoops
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Paths.PreparedBoundarySegments
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Paths.PreparedPathTrace
import Purelib.Riemann.Periods.PreparedGridPeriodPrograms
import Purelib.Riemann.RootContinuation.PreparedGridRootClosure
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Polygon.Stokes

public section

/-!
# Actual exterior occurrences in the shared surface and cap banks

The original parity-selected period walk supplies every face assignment and
covered segment. All local comparisons retain its incoming owners and cached
parents. The ordered occurrence list has exactly the original lifted indices;
its concatenated parents are the original period's initial parents.
-/

section

open Purelib.Approximation
open Purelib.Curves
open Purelib.Data
open Purelib.Polynomial
open Purelib.Riemann

open Purelib.Data.List

open Purelib.Riemann.Normalization

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {differential : Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap}
  {domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid
namespace ExteriorProgram

/-- Select the original shared owner by its retained sheet, without another
owner classification or a replacement period preparation. -/
@[expose] def faceGeometry (program : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms.ExteriorProgram lifted
  differential) :
    Hyperelliptic.Meshes.PuncturedGrid.Standard.TourFaces.FramedPuncturedGrid.OwnerWalkFaces lifted.mesh
      program.period.closed.walk (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms.exteriorOwner lifted
      program.sheet) :=
  Hyperelliptic.Meshes.PuncturedGrid.Standard.TourFaces.FramedPuncturedGrid.OwnerWalkFaces.ofSheet lifted.mesh
    program.period.closed.walk
    ⟨base.bank.frame.xLower, base.bank.frame.yLower⟩ program.sheet ⟨Gaussian.Equivalence.NamedEquivalent.refl _⟩

set_option genInjectivity false in
/-- One actual prepared exterior segment with shared-face and cap ownership. -/
structure SurfaceOccurrence (regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap)
    (domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars)
      (differential : Hyperelliptic.Differentials.Basic.Differential genus) where
  /-- The original segment's initial coordinate. -/ start : Gaussian.Basic.Canonical
  /-- The original segment's terminal coordinate. -/ finish : Gaussian.Basic.Canonical
  /-- The actual clear segment between those retained coordinates. -/ segment : Geometry.ClearPath.ClearSegment
    curve.polynomial (Hyperelliptic.Branches.Cuts.Ambient curve) start finish
  /-- The original incoming root owner. -/ owner : Topology.SquareRootContinuationChain.Owner (curve.polynomial.eval
    start)
  /-- The covered segment on that exact original owner. -/ piece : Paths.PreparedPathDecomposition.CoveredSegment
    segment owner
  /-- The actual face placement of the original segment. -/ placement : Meshes.GridLiftedMesh.LiftedMesh.SegmentFace
    lifted.mesh segment
  /-- The original shared-face comparison. -/ compared :
    Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison placement piece differential 0
  /-- The comparison uses the exact original domain at its retained route. -/ aligned : compared.domains =
    domains.atRoute placement.location
  /-- The cap preparation on that same retained comparison. -/ cap :
    Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.CapPreparation regular compared

constructive_injectivity SurfaceOccurrence

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid
namespace ExteriorProgram
namespace SurfaceOccurrence

variable {start finish : Gaussian.Basic.Canonical} {path : Polynomial.Geometry.ClearPath curve.polynomial
  (Hyperelliptic.Branches.Cuts.Ambient curve) start finish}
  {owner : Topology.SquareRootContinuationChain.Owner (curve.polynomial.eval start)} {prepared :
    Paths.PreparedClearPathModels.PreparedPath path owner} {pieces :
    Paths.PreparedPathDecomposition.PreparedPath.CoveredSegments prepared}

/-- Traverse the original assigned segment spine and retain each exact face comparison and cap preparation. -/
@[expose] def build : ∀ {start finish : Gaussian.Basic.Canonical} {path : Polynomial.Geometry.ClearPath curve.polynomial
  (Hyperelliptic.Branches.Cuts.Ambient curve) start finish}
    {owner : Topology.SquareRootContinuationChain.Owner (curve.polynomial.eval start)} {prepared :
      Paths.PreparedClearPathModels.PreparedPath path owner} {pieces :
      Paths.PreparedPathDecomposition.PreparedPath.CoveredSegments prepared},
    ∀ (assigned : Hyperelliptic.Meshes.PuncturedGrid.PreparedFaceSegments.AssignedSegments lifted.mesh pieces) (compared
      : Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.AssignedSegments.Comparisons differential 0
      assigned),
    Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.AssignedSegments.Comparisons.UsesDomains domains
      differential 0 assigned compared → Paths.PreparedExteriorPathGeometry.ClearPath.OnBoxSides
      (Hyperelliptic.Branches.Cuts.Ambient curve) path →
      List
        (ExteriorProgram.SurfaceOccurrence
        regular domains differential)
  | _, _, _, _, _, _, .nil _ _, _, _, _ => []
  | _, _, _, _, _, _, .cons placement remaining, compared, aligned, sides =>
      ⟨_, _, _, _, _, placement, compared.1, aligned.1,
        Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.CapPreparation.build regular
        compared.1 sides.1⟩ ::

          build
          remaining compared.2 aligned.2 sides.2

/-- The retained occurrence placements have exactly the original assignment's lifted indices. -/
theorem build_indexed : ∀ {start finish : Gaussian.Basic.Canonical} {path : Polynomial.Geometry.ClearPath
  curve.polynomial (Hyperelliptic.Branches.Cuts.Ambient curve) start finish}
    {owner : Topology.SquareRootContinuationChain.Owner (curve.polynomial.eval start)} {prepared :
      Paths.PreparedClearPathModels.PreparedPath path owner} {pieces :
      Paths.PreparedPathDecomposition.PreparedPath.CoveredSegments prepared},
    ∀ (assigned : Hyperelliptic.Meshes.PuncturedGrid.PreparedFaceSegments.AssignedSegments lifted.mesh pieces) (compared
      : Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.AssignedSegments.Comparisons differential 0
      assigned)
    (aligned : Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.AssignedSegments.Comparisons.UsesDomains
      domains differential 0 assigned compared) (sides : Paths.PreparedExteriorPathGeometry.ClearPath.OnBoxSides
      (Hyperelliptic.Branches.Cuts.Ambient curve) path),

      (build
      (regular := regular) assigned compared aligned sides).map (fun item => item.placement.indexed) = assigned.indexed
  | _, _, _, _, _, _, .nil _ _, _, _, _ => rfl
  | _, _, _, _, _, _, .cons _ remaining, compared, aligned, sides =>
      congrArg (List.cons _)
        (build_indexed
        remaining compared.2 aligned.2 sides.2)

/-- Flattening the occurrence parents gives exactly the original comparison parents. -/
theorem build_parents : ∀ {start finish : Gaussian.Basic.Canonical} {path : Polynomial.Geometry.ClearPath
  curve.polynomial (Hyperelliptic.Branches.Cuts.Ambient curve) start finish}
    {owner : Topology.SquareRootContinuationChain.Owner (curve.polynomial.eval start)} {prepared :
      Paths.PreparedClearPathModels.PreparedPath path owner} {pieces :
      Paths.PreparedPathDecomposition.PreparedPath.CoveredSegments prepared},
    ∀ (assigned : Hyperelliptic.Meshes.PuncturedGrid.PreparedFaceSegments.AssignedSegments lifted.mesh pieces) (compared
      : Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.AssignedSegments.Comparisons differential 0
      assigned)
    (aligned : Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.AssignedSegments.Comparisons.UsesDomains
      domains differential 0 assigned compared) (sides : Paths.PreparedExteriorPathGeometry.ClearPath.OnBoxSides
      (Hyperelliptic.Branches.Cuts.Ambient curve) path),

      ((build
      (regular := regular) assigned compared aligned sides).map (fun item =>
      item.compared.entered.cache.parents)).flatten =
      Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.AssignedSegments.Comparisons.parents differential
        0 assigned compared
  | _, _, _, _, _, _, .nil _ _, _, _, _ => rfl
  | _, _, _, _, _, _, .cons _ remaining, compared, aligned, sides =>
      congrArg (List.append _)
        (build_parents
        remaining compared.2 aligned.2 sides.2)

end SurfaceOccurrence
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid
namespace ExteriorProgram

set_option genInjectivity false in
/-- The surface and cap comparisons share every segment of this original
period, including repeated laps and all face/sheet handoffs. -/
structure SurfacePreparation (regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap)
    (domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars)
      (program : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms.ExteriorProgram lifted differential) where
  /-- The actual original period segment bank. -/ segments :
    Hyperelliptic.Meshes.PuncturedGrid.PeriodSegmentBanks.SegmentBank program.period
  /-- The retained original face assignments. -/ assigned :
    Hyperelliptic.Meshes.PuncturedGrid.PreparedFaceSegments.AssignedSegments lifted.mesh segments.pieces
  /-- The assignments have exactly the original program indices. -/ indexed_eq : assigned.indexed = program.indexed
  /-- The actual original segment comparisons. -/ compared :
    Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.AssignedSegments.Comparisons differential 0
    assigned
  /-- All comparisons use the retained shared face domains. -/ shared :
    Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.AssignedSegments.Comparisons.UsesDomains domains
    differential 0 assigned compared
  /-- The ordered original segment occurrences with their cap owners. -/ occurrences : List
    (SurfaceOccurrence
    regular domains differential)
  /-- The occurrence indices equal the original period's indices. -/ occurrences_eq : occurrences.map (fun item =>
    item.placement.indexed) = program.indexed
  /-- The flattened occurrence parents equal the original period cache. -/ parents_eq : (occurrences.map (fun item =>
    item.compared.entered.cache.parents)).flatten = program.cache.parents

constructive_injectivity SurfacePreparation

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid
namespace ExteriorProgram
namespace SurfacePreparation

/-- Reuse the original supplied segment bank to retain its shared-face assignments, cap occurrences and exact parent
readback. -/
@[expose] def ofSegments (regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap) (domains :
  Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars)
    (program : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms.ExteriorProgram lifted differential) (segments
      : Hyperelliptic.Meshes.PuncturedGrid.PeriodSegmentBanks.SegmentBank program.period) :

      ExteriorProgram.SurfacePreparation
      regular domains program := by
  let geometry :=
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.faceGeometry
    program
  let assigned := geometry.assign segments.pieces
  let caches := segments.parentCaches differential
  let compared := geometry.comparisons segments.pieces domains differential 0 caches
  have shared := geometry.comparisons_shared segments.pieces domains differential 0 caches
  have sides : Paths.PreparedExteriorPathGeometry.ClearPath.OnBoxSides
      (Hyperelliptic.Branches.Cuts.Ambient curve) program.period.closed.walk.path := by
    rw [program.walk_eq]
    exact Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms.exteriorWalk_sides base
  let occurrences :=
    SurfaceOccurrence.build
    (regular := regular) assigned compared shared sides
  have indexedEq : assigned.indexed = program.indexed :=
    (geometry.assign_indexed segments.pieces).trans geometry.indexed_eq
  have parentsEq : (occurrences.map (fun item => item.compared.entered.cache.parents)).flatten = program.cache.parents
    :=

      (SurfaceOccurrence.build_parents
      assigned compared shared sides).trans
      ((geometry.comparisons_parents segments.pieces domains differential 0 caches).trans
        ((segments.parentCaches_parents differential).trans program.recast_cache))
  exact ⟨segments, assigned, indexedEq, compared, shared, occurrences,

      (SurfaceOccurrence.build_indexed
      assigned compared shared sides).trans indexedEq, parentsEq⟩

/-- Prepare the original period's segment bank once and retain its exact surface and cap occurrences. -/
@[expose] def build (regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap) (domains :
  Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars)
    (program : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms.ExteriorProgram lifted differential) :
      ExteriorProgram.SurfacePreparation
      regular domains program :=

    ofSegments
    regular domains program (Hyperelliptic.Meshes.PuncturedGrid.PeriodSegmentBanks.SegmentBank.build program.period)

end SurfacePreparation
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid
namespace ExteriorProgram

set_option genInjectivity false in
/-- Retain each component together with its original root-closed program. -/
structure SurfaceComponent (regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap)
    (domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars)
      (differential : Hyperelliptic.Differentials.Basic.Differential genus) where
  /-- The original root-closed exterior program. -/ program :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms.ExteriorProgram lifted differential
  /-- The actual surface preparation of that exact program. -/ prepared :
    SurfacePreparation
    regular domains program

constructive_injectivity SurfaceComponent

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid
namespace ExteriorProgram
namespace SurfaceComponent

/-- Retain an original exterior period together with its actual shared surface preparation. -/
@[expose] def build (regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap) (domains :
  Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars)
    (program : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms.ExteriorProgram lifted differential) :
      ExteriorProgram.SurfaceComponent
      regular domains differential :=
  ⟨program,
    SurfacePreparation.build
    regular domains program⟩

/-- Flattening the actual component occurrences preserves the original component programs' index order. -/
theorem occurrences_indexed (components : List
  (Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceComponent
  regular domains differential)) :
    ((components.flatMap (fun component => component.prepared.occurrences)).map (fun item => item.placement.indexed)) =
      (components.map (fun component => component.program.indexed)).flatten := by
  induction components with
  | nil => rfl
  | cons head tail ih =>
      simp only [Flatten.flatMap_cons, Map.map_append, List.map_cons, List.flatten_cons, head.prepared.occurrences_eq,
        ih, -eq_self, -iff_self]
      rfl

end SurfaceComponent
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid
namespace ExteriorProgram

set_option genInjectivity false in
/-- All exterior components, in the exact physical-boundary occurrence order. -/
structure AllSurfacePreparation (regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap)
    (domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars)
      (differential : Hyperelliptic.Differentials.Basic.Differential genus) where
  /-- The original exterior components in retained boundary order. -/ components : List
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceComponent
    regular domains differential)
  /-- The cached concatenation of their actual surface occurrences. -/ occurrences : List
    (SurfaceOccurrence
    regular domains differential)
  /-- The cached list is exactly the original component occurrence concatenation. -/ occurrences_eq : occurrences =
    components.flatMap (fun component => component.prepared.occurrences)
  /-- The occurrence indices equal the literal flattened original exterior boundaries. -/ indexed_eq : occurrences.map
    (fun item => item.placement.indexed) = lifted.exteriorBoundaries.flatten

constructive_injectivity AllSurfacePreparation

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid
namespace ExteriorProgram
namespace AllSurfacePreparation

/-- Prepare each original parity-selected exterior program in physical-boundary order and cache the exact concatenated
occurrences. -/
@[expose] def build (regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap)
    (domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars)
      (differential : Hyperelliptic.Differentials.Basic.Differential genus) :

      ExteriorProgram.AllSurfacePreparation
      regular domains differential :=
  let programs := Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms.exteriorPrograms lifted differential
  let components := programs.map
    (SurfaceComponent.build
    regular domains)
  let occurrences := components.flatMap (fun component => component.prepared.occurrences)
  ⟨components, occurrences, rfl,
    (SurfaceComponent.occurrences_indexed
    components).trans (by
    rw [Map.map_map]
    exact congrArg List.flatten (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms.exteriorPrograms_indexed
      lifted differential))⟩

end AllSurfacePreparation
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram

end
