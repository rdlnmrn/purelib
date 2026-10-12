module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Corners
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleAdjacentFaces
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleLiftedSides
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleRootedCorrection
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.FacePerimeters
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalizedPrimitives
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PhysicalSideChords
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TriangleCornerSources
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedDualSteps
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalizedCornerMagnitude
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Mesh.IndexedQuadrilaterals
import Purelib.Topology.Mesh.QuadrilateralDual
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts
import Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleAreaRemainder
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalizedNumerics
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SideNeighborConsistency
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Vector.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Geometry.Rectangle.Partition.RectangularEdgeUniqueness
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Branches.RectangularSheetGauge
import Purelib.Riemann.Integration.RectangularRefinementSigns
import Purelib.Riemann.Integration.RectangularStitchedPerimeter
import Purelib.Riemann.Meshes.GridLiftedFaceLocations
import Purelib.Riemann.Meshes.GridLiftedFaces
import Purelib.Riemann.Meshes.RectangularFaceModels
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Riemann.Readings.RectangularObservationAssembly
import Purelib.Riemann.Readings.RectangularPointReadings
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Tactic.Ring

open Purelib

open Purelib.Algebra

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Corners

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleAdjacentFaces

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleLiftedSides.FramedPuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalizedCornerMagnitude.RegularMeshes

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PhysicalSideChords.RegularMeshes

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings

open Purelib.Riemann.Meshes

open Purelib.Riemann.Meshes.GridLiftedDualSteps

open Purelib.Topology.Mesh.IndexedQuadrilaterals

open Purelib.Topology.Mesh.QuadrilateralDual

open Purelib.Topology.Polygon

open Purelib.Topology.Surface.Sewing

@[expose] public section

/-! Actual inward hole-side sources read the same centered endpoint chords
that occur in the fine physical perimeter remainder. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleSourceChords.BranchCellBank

open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces)
open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedMesh)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes (RegularMeshes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes (Numerics)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open Purelib.Riemann.Meshes.GridLiftedDualSteps (GridSide)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Topology.Polygon.Stokes (edgeArea)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts (SourceEdge)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : Purelib.Curves.Hyperelliptic.Branches.BranchCellBank curve branches
    higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {vertices :
    Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank bank.grid} {edges :
    Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank frames}
  {faces : Purelib.Riemann.Meshes.PuncturedGridFaces.PuncturedFaces bank} {mesh :
    Purelib.Riemann.Meshes.GridLiftedMesh.LiftedMesh vertices edges faces}
  {domains : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames faces.regulars}
    {stage : Nat} {cache : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics
    domains stage}
  {i j : Fin genus} {position : Fin faces.regulars.length} {sheet : Fin 2}

namespace LiftedMesh.LocatedFace

/-- The original oriented triangle source for a side of the retained located face. -/
def sideSource (_located : mesh.LocatedFace position sheet) (side : GridLiftedDualSteps.GridSide) :
  SewnPrimitiveContacts.SourceEdge mesh.triangles.length :=
  ⟨mesh.triangleIndex position sheet (QuadOccurrence.upperSide side.kind),
    FaceCorners.firstCorner side.kind, FaceCorners.lastCorner side.kind⟩

/-- The retained side source projects to that actual lifted face edge. -/
theorem sideSource_project (located : mesh.LocatedFace position sheet) (side : GridLiftedDualSteps.GridSide) :
    (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleSourceChords.BranchCellBank.LiftedMesh.LocatedFace.sideSource
      located side).project mesh.triangulation.faces = located.lifted.quad.edge side.kind := by
  unfold Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleSourceChords.BranchCellBank.LiftedMesh.LocatedFace.sideSource
    SewnPrimitiveContacts.SourceEdge.project
  rw [mesh.triangleIndex_face, FaceCorners.source_edge,
    (mesh.locateFace position sheet).lifted.quad_eq located.lifted]

end LiftedMesh.LocatedFace

namespace TriangleReadings

/-- A source chord is centered at its own triangle's first corner, which is also the shared face anchor for both
triangles of a rectangle. -/
def sourceChord (left : TrianglePrimitiveReadings.TriangleReadings (cache.get i) mesh) (right :
  TrianglePrimitiveReadings.TriangleReadings (cache.get j) mesh)
    (source : SewnPrimitiveContacts.SourceEdge mesh.triangles.length) : Data.Gaussian.Basic.Canonical :=
  Stokes.edgeArea
    ⟨left.values source.source source.first - left.values source.source 0,
      right.values source.source source.first - right.values source.source 0⟩
    ⟨left.values source.source source.last - left.values source.source 0,
      right.values source.source source.last - right.values source.source 0⟩

/-- The actual source chord equals the normalized side chord with its original top/left orientation sign.

Every source keeps its original triangle and bounded corner indices. The
four side orientations select the displayed sign directly, preserving the
cached normalized readings and actual perimeter remainder. -/
theorem sourceChord_side (left : TrianglePrimitiveReadings.TriangleReadings (cache.get i) mesh)
    (right : TrianglePrimitiveReadings.TriangleReadings (cache.get j) mesh)
    (located : mesh.LocatedFace position sheet) (side : GridLiftedDualSteps.GridSide) :
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleSourceChords.BranchCellBank.TriangleReadings.sourceChord left
      right
      (LiftedMesh.LocatedFace.sideSource
      located side) =
      if side = .top ∨ side = .left then -Numerics.sideChord cache.normalize i j position sheet side
      else Numerics.sideChord cache.normalize i j position sheet side := by
  unfold Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleSourceChords.BranchCellBank.TriangleReadings.sourceChord
    Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleSourceChords.BranchCellBank.LiftedMesh.LocatedFace.sideSource
  rw [left.values_eq, right.values_eq]
  cases side
  all_goals
    first
    | rw [if_pos (show GridSide.top = .top ∨ GridSide.top = .left from Or.inl rfl)]
    | rw [if_pos (show GridSide.left = .top ∨ GridSide.left = .left from Or.inr rfl)]
    | rw [if_neg (show ¬ (GridSide.bottom = .top ∨ GridSide.bottom = .left) from by
        intro impossible; rcases impossible with impossible | impossible <;> nomatch impossible)]
    | rw [if_neg (show ¬ (GridSide.right = .top ∨ GridSide.right = .left) from by
        intro impossible; rcases impossible with impossible | impossible <;> nomatch impossible)]
  all_goals
    simp only [Numerics.sideChord, Numerics.cornerPair, -eq_self, -iff_self]
    rw [cache.normalize_atDomain, cache.normalize_atDomain]
    simp only [FaceCorners.triangleValues, DomainPrimitives.normalize_corner, Numerics.atDomain,
      Stokes.edgeArea, Data.Vector.Basic.vectorOfFn_apply, -eq_self, -iff_self]
    dsimp [GridSide.kind, QuadOccurrence.upperSide, FaceCorners.firstCorner,
      FaceCorners.lastCorner, FaceCorners.triangle, FaceCorners.quad,
      IndexedQuadrilateral.firstTriangle,
      IndexedQuadrilateral.secondTriangle,
      SewnPrimitiveFaces.corner]
  all_goals ring1

end TriangleReadings
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleSourceChords.BranchCellBank

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleSourceChords.LiftedPuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes (RegularMeshes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes (CommonCuts Preflights
  Numerics)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest (TwoSheetRequest)
open Purelib.Riemann.Meshes.GridLiftedDualSteps (GridSide)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleRootedCorrection (HoleSideLifts)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleAreaRemainder (holeAreaRemainder sideAreaRemainder)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleAdjacentFaces.FramedPuncturedGrid (HoleAdjacentFace)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleLiftedSides.FramedPuncturedGrid.HoleAdjacentFace (LiftedSide)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr sumFin_sub)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Purelib.Riemann.Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Purelib.Riemann.Meshes.LiftedPuncturedGrid base} {domains :
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
  {cuts : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.CommonCuts domains}
    {coarseDepth : Nat} {fixed : (sheet : Fin 2) →
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Preflights domains sheet}
  {target : Purelib.Data.Rat.Fraction.Rational} {i j : Fin genus} {stage : Nat} {cache :
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics domains stage}
  {request : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest.TwoSheetRequest (fun sheet =>
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.build domains cuts sheet
    coarseDepth) fixed target}
  {hole : Fin base.faces.holes.length}
  {adjacent : HoleAdjacentFaces
    base (base.faces.holes[hole.val]'hole.isLt)}

/-- Each selected adjacent-face source is the original inward hole edge, including its root-sheet transport. -/
theorem holeSideSource_project {side : GridLiftedDualSteps.GridSide} {sheet : Fin 2}
    {adjacent : FramedPuncturedGrid.HoleAdjacentFace base (base.faces.holes[hole.val]'hole.isLt) side}
    (selected : HoleAdjacentFace.LiftedSide adjacent lifted sheet) :
    (Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleSourceChords.BranchCellBank.LiftedMesh.LocatedFace.sideSource
      selected.selected.located side.opposite).project lifted.mesh.triangulation.faces =
      lifted.edges.indexedEdge lifted.vertices ((base.faces.holes[hole.val]'hole.isLt).side side).reverse sheet :=
  (Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleSourceChords.BranchCellBank.LiftedMesh.LocatedFace.sideSource_project
    selected.selected.located side.opposite).trans selected.edge_eq

/-- All eight inward-oriented source chords, retaining the actual face sheet selected by each original hole side. -/
def holeSourceChords (left : TrianglePrimitiveReadings.TriangleReadings (cache.get i) lifted.mesh)
    (right : TrianglePrimitiveReadings.TriangleReadings (cache.get j) lifted.mesh) (sides :
      HoleRootedCorrection.HoleSideLifts lifted adjacent) : Data.Gaussian.Basic.Canonical :=
  FiniteSum.Fin.sumFin (fun sheet =>
    Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleSourceChords.BranchCellBank.TriangleReadings.sourceChord left right
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleSourceChords.BranchCellBank.LiftedMesh.LocatedFace.sideSource
      (sides.left.get sheet).selected.located .right) +
    Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleSourceChords.BranchCellBank.TriangleReadings.sourceChord left right
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleSourceChords.BranchCellBank.LiftedMesh.LocatedFace.sideSource
      (sides.top.get sheet).selected.located .bottom) +
    Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleSourceChords.BranchCellBank.TriangleReadings.sourceChord left right
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleSourceChords.BranchCellBank.LiftedMesh.LocatedFace.sideSource
      (sides.right.get sheet).selected.located .left) +
    Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleSourceChords.BranchCellBank.TriangleReadings.sourceChord left right
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleSourceChords.BranchCellBank.LiftedMesh.LocatedFace.sideSource
      (sides.bottom.get sheet).selected.located .top))

/-- The fine hole remainder subtracts the actual original source chords; all fine side excursions remain in the
displayed perimeter term.

Every source keeps its original triangle and bounded corner indices. The
four side orientations select the displayed sign directly, preserving the
cached normalized readings and actual perimeter remainder. -/
theorem holeAreaRemainder_eq_sourceChords
    (perimeters : Matched.FacePerimeters (request := request) cache.normalize i j)
    (left : TrianglePrimitiveReadings.TriangleReadings (cache.get i) lifted.mesh)
    (right : TrianglePrimitiveReadings.TriangleReadings (cache.get j) lifted.mesh) (sides :
      HoleRootedCorrection.HoleSideLifts lifted adjacent) :
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleAreaRemainder.holeAreaRemainder perimeters sides =
      FiniteSum.Fin.sumFin (fun sheet =>
        ((perimeters.perimeters.get adjacent.left.position).get (sides.left.get sheet).selected.sheet).right -
        ((perimeters.perimeters.get adjacent.right.position).get (sides.right.get sheet).selected.sheet).left -
        (((perimeters.perimeters.get adjacent.bottom.position).get (sides.bottom.get sheet).selected.sheet).top -
          ((perimeters.perimeters.get adjacent.top.position).get (sides.top.get sheet).selected.sheet).bottom)) -
      Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleSourceChords.LiftedPuncturedGrid.holeSourceChords left right
        sides := by
  unfold HoleAreaRemainder.holeAreaRemainder HoleSourceChords.LiftedPuncturedGrid.holeSourceChords
  rw [← FiniteSum.Fin.sumFin_sub]
  apply FiniteSum.Fin.sumFin_congr
  intro sheet
  simp only [HoleAreaRemainder.sideAreaRemainder,
    Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleSourceChords.BranchCellBank.TriangleReadings.sourceChord_side left
    right, -eq_self, -iff_self]
  have bottomRejected : ¬ (GridSide.bottom = .top ∨ GridSide.bottom = .left) := by
    intro impossible; rcases impossible with impossible | impossible <;> nomatch impossible
  have rightRejected : ¬ (GridSide.right = .top ∨ GridSide.right = .left) := by
    intro impossible; rcases impossible with impossible | impossible <;> nomatch impossible
  rw [if_pos (show GridSide.top = .top ∨ GridSide.top = .left from Or.inl rfl),
    if_pos (show GridSide.left = .top ∨ GridSide.left = .left from Or.inr rfl),
    if_neg bottomRejected, if_neg rightRejected]
  ring1

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleSourceChords.LiftedPuncturedGrid
