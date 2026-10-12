module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.LiftedSides
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularSideNeighbors
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Polygon.Stokes
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SideNeighborConsistency
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.NeighborUniqueness
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Data.Gaussian.Field
import Purelib.Data.Vector.Dependent
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Meshes.GridLiftedDualSteps
import Purelib.Riemann.Meshes.GridLiftedFaceLocations
import Purelib.Tactic.QuotientFreeOmega

open Purelib

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingBank

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.NeighborUniqueness

open Purelib.Riemann.Meshes.GridLiftedDualSteps

open Purelib.Riemann.Meshes.PuncturedGridFaces

open Purelib.Topology.Polygon

@[expose] public section

/-! The complete side classification agrees with the retained lifted crossings. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NeighborCrossingAgreement

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices (VertexBank)
open Purelib.RootIsolation.SquareRoot.Grid (RootEdgeBank)
open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedMesh)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes (RegularMeshes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes (CommonCuts Preflights)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest (TwoSheetRequest)
open Purelib.Riemann.Meshes.GridLiftedDualSteps (GridSide)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.LiftedSides (HorizontalCrossing VerticalCrossing)
open _root_.Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched (CrossingBank)
open _root_.Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingBank (HorizontalOutcome
  VerticalOutcome)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Riemann.Readings.RectangularMatchedObservationSides.ObservationMesh (MatchedHorizontalSide
  MatchedVerticalSide)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches
    higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {vertices :
    VertexBank bank.grid} {edges :
    RootEdgeBank frames}
  {faces : PuncturedFaces bank} {domains :
    FaceDomainBank frames faces.regulars}
  {cuts : CommonCuts domains}
    {coarseDepth : Nat} {fixed : (sheet : Fin 2) →
    Preflights domains sheet}
    {target : Rational}
  {mesh : LiftedMesh vertices edges faces}
  {firstPosition : Fin faces.regulars.length} {firstSheet : Fin 2}

variable {request : TwoSheetRequest (fun sheet
  => RegularMeshes.build domains cuts sheet
  coarseDepth) fixed target}

namespace HorizontalCrossing
variable {first : mesh.LocatedFace firstPosition firstSheet} {nextPosition : Fin faces.regulars.length}
  {firstUpper lastUpper : Bool}

/-- The actual retained horizontal crossing satisfies the original physical top-side adjacency equalities. -/
theorem physical_match (joined : LiftedSides.HorizontalCrossing request first nextPosition firstUpper lastUpper) :
    GridSide.Matches .top faces.regulars[firstPosition.val].cell.box faces.regulars[nextPosition.val].cell.box := by
  have lower := HorizontalCrossing.next_anchor joined
  have upper := congrArg (fun edge : Stokes.OrientedEdge vertices.count =>
    vertices.coordinate edge.finish) joined.reversed
  change vertices.coordinate joined.crossing.next.located.lifted.quad.second =
    vertices.coordinate first.lifted.quad.third at upper
  rw [joined.crossing.next.located.lifted.coordinates.2.1, first.lifted.coordinates.2.2.1] at upper
  exact ⟨(congrArg (fun point : Data.Gaussian.Basic.Canonical => point.re) lower).symm,
    (congrArg (fun point : Data.Gaussian.Basic.Canonical => point.re) upper).symm,
    (congrArg (fun point : Data.Gaussian.Basic.Canonical => point.im) lower).symm⟩

end HorizontalCrossing

namespace HorizontalOutcome
variable {first : mesh.LocatedFace firstPosition firstSheet} {nextPosition : Fin faces.regulars.length}

/-- The original top-side neighbor classification selects a regular face exactly when its retained horizontal outcome
contains a crossing. -/
theorem regular_iff_matched (outcome : CrossingBank.HorizontalOutcome request first nextPosition)
    (neighbor : PuncturedFaces.SideNeighbor faces faces.regulars[firstPosition.val] .top) :
    neighbor.RegularAt nextPosition ↔ ∃ joined, outcome = .matched joined := by
  constructor
  · intro regular
    have matching := neighbor.matches_of_regular nextPosition regular
    exact HorizontalOutcome.complete request outcome matching.1 matching.2.1 matching.2.2
  · rintro ⟨joined, rfl⟩
    exact neighbor.regular_of_matches nextPosition
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.NeighborCrossingAgreement.HorizontalCrossing.physical_match joined)

end HorizontalOutcome

namespace VerticalCrossing
variable {first : mesh.LocatedFace firstPosition firstSheet} {nextPosition : Fin faces.regulars.length}
  {firstUpper lastUpper : Bool}

/-- The actual retained vertical crossing satisfies the original physical right-side adjacency equalities. -/
theorem physical_match (joined : LiftedSides.VerticalCrossing request first nextPosition firstUpper lastUpper) :
    GridSide.Matches .right faces.regulars[firstPosition.val].cell.box faces.regulars[nextPosition.val].cell.box := by
  have lower := VerticalCrossing.next_anchor joined
  have upper := congrArg (fun edge : Stokes.OrientedEdge vertices.count =>
    vertices.coordinate edge.start) joined.reversed
  change vertices.coordinate joined.crossing.next.located.lifted.quad.fourth =
    vertices.coordinate first.lifted.quad.third at upper
  rw [joined.crossing.next.located.lifted.coordinates.2.2.2, first.lifted.coordinates.2.2.1] at upper
  exact ⟨(congrArg (fun point : Data.Gaussian.Basic.Canonical => point.im) lower).symm,
    (congrArg (fun point : Data.Gaussian.Basic.Canonical => point.im) upper).symm,
    (congrArg (fun point : Data.Gaussian.Basic.Canonical => point.re) lower).symm⟩

end VerticalCrossing

namespace VerticalOutcome
variable {first : mesh.LocatedFace firstPosition firstSheet} {nextPosition : Fin faces.regulars.length}

/-- The original right-side neighbor classification selects a regular face exactly when its retained vertical outcome
contains a crossing. -/
theorem regular_iff_matched (outcome : CrossingBank.VerticalOutcome request first nextPosition)
    (neighbor : PuncturedFaces.SideNeighbor faces faces.regulars[firstPosition.val] .right) :
    neighbor.RegularAt nextPosition ↔ ∃ joined, outcome = .matched joined := by
  constructor
  · intro regular
    have matching := neighbor.matches_of_regular nextPosition regular
    exact VerticalOutcome.complete request outcome matching.1 matching.2.1 matching.2.2
  · rintro ⟨joined, rfl⟩
    exact neighbor.regular_of_matches nextPosition
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.NeighborCrossingAgreement.VerticalCrossing.physical_match joined)

end VerticalOutcome

/-- The complete original top-neighbor bank and retained horizontal crossing bank classify the same destination face. -/
theorem CrossingBank.horizontal_neighbor_iff (retained : Matched.CrossingBank request mesh)
    (neighbors : PuncturedFaces.NeighborBank faces)
    (firstPosition nextPosition : Fin faces.regulars.length) (sheet : Fin 2) :
    (neighbors.entries.get firstPosition).top.RegularAt nextPosition ↔
      ∃ joined, ((retained.horizontal.get firstPosition).get sheet).get nextPosition = .matched joined :=
  Curves.Hyperelliptic.Meshes.PuncturedGrid.NeighborCrossingAgreement.HorizontalOutcome.regular_iff_matched _ _

/-- The destination's original bottom-neighbor classification agrees with the same retained horizontal crossing in
reverse. -/
theorem CrossingBank.horizontal_reverse_neighbor_iff (retained : Matched.CrossingBank request mesh)
    (neighbors : PuncturedFaces.NeighborBank faces)
    (firstPosition nextPosition : Fin faces.regulars.length) (sheet : Fin 2) :
    (neighbors.entries.get nextPosition).bottom.RegularAt firstPosition ↔
      ∃ joined, ((retained.horizontal.get firstPosition).get sheet).get nextPosition = .matched joined := by
  constructor
  · intro regular
    apply (Curves.Hyperelliptic.Meshes.PuncturedGrid.NeighborCrossingAgreement.CrossingBank.horizontal_neighbor_iff
      retained neighbors firstPosition nextPosition sheet).mp
    exact (neighbors.entries.get firstPosition).top.regular_of_matches nextPosition
      ((neighbors.entries.get nextPosition).bottom.matches_of_regular firstPosition regular).reverse
  · intro matched
    have regular :=
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.NeighborCrossingAgreement.CrossingBank.horizontal_neighbor_iff
      retained neighbors firstPosition nextPosition sheet).mpr matched
    exact (neighbors.entries.get nextPosition).bottom.regular_of_matches firstPosition
      ((neighbors.entries.get firstPosition).top.matches_of_regular nextPosition regular).reverse

/-- The complete original right-neighbor bank and retained vertical crossing bank classify the same destination face. -/
theorem CrossingBank.vertical_neighbor_iff (retained : Matched.CrossingBank request mesh)
    (neighbors : PuncturedFaces.NeighborBank faces)
    (firstPosition nextPosition : Fin faces.regulars.length) (sheet : Fin 2) :
    (neighbors.entries.get firstPosition).right.RegularAt nextPosition ↔
      ∃ joined, ((retained.vertical.get firstPosition).get sheet).get nextPosition = .matched joined :=
  Curves.Hyperelliptic.Meshes.PuncturedGrid.NeighborCrossingAgreement.VerticalOutcome.regular_iff_matched _ _

/-- The destination's original left-neighbor classification agrees with the same retained vertical crossing in reverse.
-/
theorem CrossingBank.vertical_reverse_neighbor_iff (retained : Matched.CrossingBank request mesh)
    (neighbors : PuncturedFaces.NeighborBank faces)
    (firstPosition nextPosition : Fin faces.regulars.length) (sheet : Fin 2) :
    (neighbors.entries.get nextPosition).left.RegularAt firstPosition ↔
      ∃ joined, ((retained.vertical.get firstPosition).get sheet).get nextPosition = .matched joined := by
  constructor
  · intro regular
    apply (Curves.Hyperelliptic.Meshes.PuncturedGrid.NeighborCrossingAgreement.CrossingBank.vertical_neighbor_iff
      retained neighbors firstPosition nextPosition sheet).mp
    exact (neighbors.entries.get firstPosition).right.regular_of_matches nextPosition
      ((neighbors.entries.get nextPosition).left.matches_of_regular firstPosition regular).reverse
  · intro matched
    have regular :=
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.NeighborCrossingAgreement.CrossingBank.vertical_neighbor_iff
      retained neighbors firstPosition nextPosition sheet).mpr matched
    exact (neighbors.entries.get nextPosition).left.regular_of_matches firstPosition
      ((neighbors.entries.get firstPosition).right.matches_of_regular nextPosition regular).reverse

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NeighborCrossingAgreement

