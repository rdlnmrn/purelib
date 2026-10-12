module
import Purelib.Data.List.Membership
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.List.Map
import Purelib.Topology.Surface.Sewing.SimpleBoundaryCycles

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BranchHoleSourceComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleAdjacentFaces
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleAreaRemainder
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleRootedCorrection
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.FacePerimeters
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TriangleSourceUniqueness
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedDualSteps
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Topology.Mesh.TriangleSourceUniqueness
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleSourceChords
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleBoundaryReadback
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BranchHoleCutWords
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleLiftedSides
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalizedNumerics
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SideNeighborConsistency
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Vector.Dependent
import Purelib.Geometry.Rectangle.Partition.RectangularEdgeUniqueness
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.FromStates
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Integration.RectangularStitchedPerimeter
import Purelib.Riemann.Meshes.GridLiftedBoundaryLoops
import Purelib.Riemann.Meshes.GridLiftedFaceLocations
import Purelib.Riemann.Meshes.GridLiftedFaces
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Readings.RectangularObservationAssembly
import Purelib.Riemann.RootContinuation.RootPathTransport
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootEdges
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Topology.Surface.Sewing.SewnPrimitivePaths
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega

open Purelib

open Purelib.Algebra

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleSourceChords

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleSourceChords.BranchCellBank

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleSourceChords.BranchCellBank.LiftedMesh

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TriangleSourceUniqueness

open Purelib.Data.List

open Purelib.Riemann.Meshes

open Purelib.Topology.Mesh.TriangleSourceUniqueness

open Purelib.Topology.Surface.Sewing

public section

/-! Root-ordered source occurrences of the physical hole. The area sum
retains both sheets even when each side transport swaps their order. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleSourceWords
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleRootedCorrection (HoleSideLifts)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Riemann.Meshes.GridLiftedDualSteps (GridSide)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes (RegularMeshes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes (CommonCuts Preflights
  Numerics)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest (TwoSheetRequest)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts (SourceEdge)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BranchHoleCutWords (PhysicalCutWord)
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Algebra.FiniteSum.Fin (sumFin)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {hole : Fin base.faces.holes.length}
  {adjacent : HoleAdjacentFaces
    base (base.faces.holes[hole.val]'hole.isLt)}

/-- The original inward source occurrences of one physical hole lap in transported root-sheet order. -/
@[expose] def lapSources (sides : HoleRootedCorrection.HoleSideLifts lifted adjacent) (sheet : Fin 2) : List
  (SewnPrimitiveContacts.SourceEdge lifted.mesh.triangles.length) :=
  let source := (base.faces.holes[hole.val]'hole.isLt)
  let afterLeft := (lifted.edges.edge (source.side .left).reverse).forward.target sheet
  let afterTop := (lifted.edges.edge (source.side .top).reverse).forward.target afterLeft
  let afterRight := (lifted.edges.edge (source.side .right).reverse).forward.target afterTop
  [LocatedFace.sideSource (sides.left.get sheet).selected.located .right,
    LocatedFace.sideSource (sides.top.get afterLeft).selected.located .bottom,
    LocatedFace.sideSource (sides.right.get afterTop).selected.located .left,
    LocatedFace.sideSource (sides.bottom.get afterRight).selected.located .top]

/-- The retained source lap projects to the actual inward lifted hole lap. -/
theorem lapSources_project (sides : HoleRootedCorrection.HoleSideLifts lifted adjacent) (sheet : Fin 2) :
    (lapSources sides sheet).map (fun source => source.project
      lifted.mesh.triangulation.faces) =
      HoleBoundaryReadback.lap sides sheet := by
  simp only [lapSources, HoleBoundaryReadback.lap,
    List.map_cons, List.map_nil, LocatedFace.sideSource_project]
  rfl

/-- Both original inward source laps, starting on sheet zero and then sheet one. -/
@[expose] def boundarySources (sides : HoleRootedCorrection.HoleSideLifts lifted adjacent) : List
  (SewnPrimitiveContacts.SourceEdge lifted.mesh.triangles.length) :=
  lapSources sides 0 ++
    lapSources sides 1

/-- The complete retained source list projects to the original lifted physical hole boundary. -/
theorem boundarySources_project (sides : HoleRootedCorrection.HoleSideLifts lifted adjacent) :
    (boundarySources sides).map (fun source => source.project
      lifted.mesh.triangulation.faces) =
      (base.faces.holes[hole.val]'hole.isLt).liftedBoundary lifted.vertices lifted.edges := by
  rw [boundarySources, Map.map_append,
    lapSources_project sides,
    lapSources_project sides]
  exact HoleBoundaryReadback.boundaryEdges_eq sides

/-- Every source projecting to the original physical hole boundary has its retained positive triangle orientation. -/
private theorem sources_positive (sources : List (SewnPrimitiveContacts.SourceEdge lifted.mesh.triangles.length))
    (projected : sources.map (fun source => source.project lifted.mesh.triangulation.faces) =
      base.faces.holes[hole.val].liftedBoundary lifted.vertices lifted.edges) :
    ∀ source ∈ sources, SourceEdge.Positive source lifted.mesh.triangulation.faces := by
  intro source member
  apply BranchHoleSourceComparison.physicalSource_positive lifted source
  exact SimpleBoundaryCycles.mem_flatten.mpr
    ⟨base.faces.holes[hole.val].liftedBoundary lifted.vertices lifted.edges,
      Membership.mem_append.mpr (Or.inr (Map.mem_map_of_mem (List.getElem_mem hole.isLt))),
      projected ▸ Map.mem_map_of_mem member⟩

/-- The original physical boundary has a unique positive triangle source at every occurrence. This applies to already
retained annular source lists. -/
theorem boundarySources_eq (sides : HoleRootedCorrection.HoleSideLifts lifted adjacent)
    (sources : List (SewnPrimitiveContacts.SourceEdge lifted.mesh.triangles.length))
    (projected : sources.map (fun source => source.project lifted.mesh.triangulation.faces) =
      (base.faces.holes[hole.val]'hole.isLt).liftedBoundary lifted.vertices lifted.edges) :
    boundarySources sides = sources :=
  SourceEdge.list_eq_of_project_eq lifted.mesh.orientedEdges_unique
    (LiftedMesh.corners_injective lifted.mesh) _ _
    (sources_positive _
      (boundarySources_project sides))
      (sources_positive _ projected)
    ((boundarySources_project sides).trans projected.symm)

/-- Root transport only permutes the two sheets; the sum reads each of the four actual adjacent sides twice, with its
original source orientation. -/
theorem boundarySources_sum (sides : HoleRootedCorrection.HoleSideLifts lifted adjacent)
    (value : SewnPrimitiveContacts.SourceEdge lifted.mesh.triangles.length → Data.Gaussian.Basic.Canonical) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum
      ((boundarySources sides).map value) =
      FiniteSum.Fin.sumFin (fun sheet =>
        value (LocatedFace.sideSource (sides.left.get sheet).selected.located .right) +
        value (LocatedFace.sideSource (sides.top.get sheet).selected.located .bottom) +
        value (LocatedFace.sideSource (sides.right.get sheet).selected.located .left) +
        value (LocatedFace.sideSource (sides.bottom.get sheet).selected.located .top)) := by
  let source := (base.faces.holes[hole.val]'hole.isLt)
  let target := fun side => (lifted.edges.edge (source.side side).reverse).forward.target
  have injective (side : GridLiftedDualSteps.GridSide) : Function.Injective (target side) :=
    ((lifted.edges.edge (source.side side).reverse).bijection
      (BranchCellBank.referenceAt base.bank.toBranchCellBank _ (source.side side).reverse.vertices.1).toLoop
      (BranchCellBank.referenceAt base.bank.toBranchCellBank _ (source.side
        side).reverse.vertices.2).toLoop).forward_injective
  have top := Data.Gaussian.Norm.Sum.Basic.sum_two_reindex (target .left) (injective .left)
    (fun sheet => value (LocatedFace.sideSource (sides.top.get sheet).selected.located .bottom))
  have right := Data.Gaussian.Norm.Sum.Basic.sum_two_reindex (fun sheet => target .top (target .left sheet))
    ((injective .top).comp (injective .left))
    (fun sheet => value (LocatedFace.sideSource (sides.right.get sheet).selected.located .left))
  have bottom := Data.Gaussian.Norm.Sum.Basic.sum_two_reindex (fun sheet => target .right (target .top (target
    .left sheet)))
    ((injective .right).comp ((injective .top).comp (injective .left)))
    (fun sheet => value (LocatedFace.sideSource (sides.bottom.get sheet).selected.located .top))
  have combined := congrArg₂ (fun a b : Data.Gaussian.Basic.Canonical => a + b) top
    (congrArg₂ (fun a b : Data.Gaussian.Basic.Canonical => a + b) right bottom)
  have addLeft := congrArg (fun remaining =>
    (value (LocatedFace.sideSource (sides.left.get 0).selected.located .right) +
      value (LocatedFace.sideSource (sides.left.get 1).selected.located .right)) + remaining) combined
  dsimp only [target, source] at addLeft
  simp only [boundarySources,
    lapSources, List.cons_append, List.nil_append,
    List.map_cons, List.map_nil,
    Data.Gaussian.Norm.Sum.Basic.gaussianSum, FiniteSum.Fin.sumFin_succ]
  simp only [FiniteSum.Fin.sumFin, List.ofFn_zero, List.foldl_nil]
  change _ =
    (value (LocatedFace.sideSource (sides.left.get 0).selected.located .right) +
      value (LocatedFace.sideSource (sides.top.get 0).selected.located .bottom) +
      value (LocatedFace.sideSource (sides.right.get 0).selected.located .left) +
      value (LocatedFace.sideSource (sides.bottom.get 0).selected.located .top)) +
    ((value (LocatedFace.sideSource (sides.left.get 1).selected.located .right) +
      value (LocatedFace.sideSource (sides.top.get 1).selected.located .bottom) +
      value (LocatedFace.sideSource (sides.right.get 1).selected.located .left) +
      value (LocatedFace.sideSource (sides.bottom.get 1).selected.located .top)) + 0)
  refine Eq.trans ?_ (Eq.trans addLeft ?_)
  · ring1
  · ring1

variable {domains : FaceDomainBank lifted.frames
  base.faces.regulars} {stage : Nat}
  {cache : Numerics domains stage}
    {i j : Fin genus}

/-- Summing the actual boundary source chords gives the retained two-sheet hole chord readback. -/
theorem boundarySources_chords (sides : HoleRootedCorrection.HoleSideLifts lifted adjacent)
    (left : TrianglePrimitiveReadings.TriangleReadings (cache.get i) lifted.mesh) (right :
      TrianglePrimitiveReadings.TriangleReadings (cache.get j) lifted.mesh) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum
      ((boundarySources sides).map
      (TriangleReadings.sourceChord left right)) = LiftedPuncturedGrid.holeSourceChords left right sides :=
  boundarySources_sum sides (TriangleReadings.sourceChord left
    right)

/-- The physical cut word and the root-ordered side list retain exactly the same source occurrences; no independently
sampled values are substituted. -/
theorem physical_sources_chords (sides : HoleRootedCorrection.HoleSideLifts lifted adjacent)
    (physical : BranchHoleCutWords.PhysicalCutWord lifted ((base.faces.holes[hole.val]'hole.isLt).liftedBoundary
      lifted.vertices lifted.edges))
    (left : TrianglePrimitiveReadings.TriangleReadings (cache.get i) lifted.mesh) (right :
      TrianglePrimitiveReadings.TriangleReadings (cache.get j) lifted.mesh) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (physical.sources.sources.map (TriangleReadings.sourceChord left
      right)) = LiftedPuncturedGrid.holeSourceChords left right sides := by
  rw [← boundarySources_eq sides physical.sources.sources
    physical.sources_project]
  exact boundarySources_chords sides left right

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest.TwoSheetRequest
variable {cuts : CommonCuts domains}
  {coarseDepth : Nat} {fixed : (sheet : Fin 2) →
  Preflights domains sheet}
  {target : Purelib.Data.Rat.Fraction.Rational}
  {request : TwoSheetRequest (fun sheet =>
    RegularMeshes.build domains cuts sheet
    coarseDepth) fixed target}

/-- The fine physical hole remainder is compared with the exact source list carried by the cut word, including the
retained annular inner word. -/
theorem remainder_add_physical_source_chords (sides : HoleRootedCorrection.HoleSideLifts lifted adjacent)
    (physical : BranchHoleCutWords.PhysicalCutWord lifted ((base.faces.holes[hole.val]'hole.isLt).liftedBoundary
      lifted.vertices lifted.edges))
    (perimeters : Matched.FacePerimeters (request := request) cache.normalize i j)
    (left : TrianglePrimitiveReadings.TriangleReadings (cache.get i) lifted.mesh) (right :
      TrianglePrimitiveReadings.TriangleReadings (cache.get j) lifted.mesh) :
    HoleAreaRemainder.holeAreaRemainder perimeters sides + Data.Gaussian.Norm.Sum.Basic.gaussianSum
      (physical.sources.sources.map (TriangleReadings.sourceChord left right)) =
      FiniteSum.Fin.sumFin (fun sheet =>
        ((perimeters.perimeters.get adjacent.left.position).get (sides.left.get sheet).selected.sheet).right -
        ((perimeters.perimeters.get adjacent.right.position).get (sides.right.get sheet).selected.sheet).left -
        (((perimeters.perimeters.get adjacent.bottom.position).get (sides.bottom.get sheet).selected.sheet).top -
          ((perimeters.perimeters.get adjacent.top.position).get (sides.top.get sheet).selected.sheet).bottom)) := by
  rw [physical_sources_chords sides physical left right,
    LiftedPuncturedGrid.holeAreaRemainder_eq_sourceChords perimeters left right sides]
  ring1

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleSourceWords
