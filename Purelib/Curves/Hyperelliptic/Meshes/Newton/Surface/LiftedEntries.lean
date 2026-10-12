module
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries
import Purelib.Riemann.Meshes.GridLiftedDualSteps
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Integration.Observation.PreparedFaceTracePrefixes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Data.Gaussian.Field
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Geometry.Rectangle.Partition.RectangularEdgeUniqueness
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Meshes.GridLiftedFaceLocations
import Purelib.Riemann.Meshes.GridLiftedFaces
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Topology.Mesh.IndexedQuadrilaterals
import Purelib.Topology.Polygon.Stokes
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshFaceEntries

open Purelib

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries

open Purelib.Riemann.Meshes.GridLiftedMesh

@[expose] public section

/-! Complete-surface contacts start on the actual shared lifted corner owner.
The destination sheet comes from the retained root transport, without a
caller sheet agreement or a new root classification. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.LiftedEntries

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank (FaceModels)
open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedMesh)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : Purelib.Curves.Hyperelliptic.Branches.BranchCellBank curve
    branches higher}
  {preparation : Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonPreparation original} {target
    radius : Purelib.Data.Rat.Fraction.Rational}
  {grid : Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonGrid preparation target radius}
    {frames : RootIsolation.SquareRoot.Grid.RootFrames grid.shrunk.prepared.grid}
  {domains : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames
    grid.faces.regulars}
  {vertices : Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank grid.shrunk.prepared.grid} {edges :
    Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank frames}
  {mesh : Purelib.Riemann.Meshes.GridLiftedMesh.LiftedMesh vertices edges grid.faces}
  {first last : Fin grid.faces.regulars.length} {sheet : Fin 2}

namespace HorizontalContact

variable (source : mesh.LocatedFace first sheet)

/-- Locate the neighboring face on the sheet selected by the retained side transport. -/
def next : mesh.AtSide last .bottom (source.lifted.sideFinishSheet .top) :=
  mesh.locateAtSide last .bottom (source.lifted.sideFinishSheet .top)

/-- Read the entry at the retained upper-left source corner. -/
def firstEntry : FaceModels.Entry (domains.get first).models
    (vertices.coordinate source.lifted.quad.fourth) (vertices.owner frames source.lifted.quad.fourth) :=
  ⟨sheet, (source.lifted.edge_endpoints_reached (domains.get first).models .top).2⟩

/-- Read the adjacent upper face's entry on that same retained upper-left corner owner. -/
def lastEntry
    (lower : (grid.faces.regulars[first.val]'first.isLt).cell.box.xLower =
      (grid.faces.regulars[last.val]'last.isLt).cell.box.xLower)
    (upper : (grid.faces.regulars[first.val]'first.isLt).cell.box.xUpper =
      (grid.faces.regulars[last.val]'last.isLt).cell.box.xUpper)
    (joined : (grid.faces.regulars[first.val]'first.isLt).cell.box.yUpper =
      (grid.faces.regulars[last.val]'last.isLt).cell.box.yLower) :
    FaceModels.Entry (domains.get last).models (vertices.coordinate source.lifted.quad.fourth)
      (vertices.owner frames source.lifted.quad.fourth) := by
  let destination := Curves.Hyperelliptic.Meshes.Newton.Surface.LiftedEntries.HorizontalContact.next (last := last)
    source
  refine ⟨destination.sheet, ?_⟩
  have reached := (destination.located.lifted.edge_endpoints_reached (domains.get last).models .bottom).1
  have reversed := LiftedMesh.opposite_sides source .top .bottom destination
    (Data.Gaussian.Basic.ext lower.symm joined.symm)
    (Data.Gaussian.Basic.ext upper.symm joined.symm)
  change destination.located.lifted.quad.edge .bottom = (source.lifted.quad.edge .top).reverse at reversed
  rw [reversed] at reached
  exact reached

end HorizontalContact

namespace VerticalContact

variable (source : mesh.LocatedFace first sheet)

/-- Locate the neighboring face on the sheet selected by the retained side transport. -/
def next : mesh.AtSide last .left (source.lifted.sideFinishSheet .right) :=
  mesh.locateAtSide last .left (source.lifted.sideFinishSheet .right)

/-- Read the entry at the retained lower-right source corner. -/
def firstEntry : FaceModels.Entry (domains.get first).models
    (vertices.coordinate source.lifted.quad.second) (vertices.owner frames source.lifted.quad.second) :=
  ⟨sheet, (source.lifted.edge_endpoints_reached (domains.get first).models .right).1⟩

/-- Read the adjacent right face's entry on that same retained lower-right corner owner. -/
def lastEntry
    (lower : (grid.faces.regulars[first.val]'first.isLt).cell.box.yLower =
      (grid.faces.regulars[last.val]'last.isLt).cell.box.yLower)
    (upper : (grid.faces.regulars[first.val]'first.isLt).cell.box.yUpper =
      (grid.faces.regulars[last.val]'last.isLt).cell.box.yUpper)
    (joined : (grid.faces.regulars[first.val]'first.isLt).cell.box.xUpper =
      (grid.faces.regulars[last.val]'last.isLt).cell.box.xLower) :
    FaceModels.Entry (domains.get last).models (vertices.coordinate source.lifted.quad.second)
      (vertices.owner frames source.lifted.quad.second) := by
  let destination := Curves.Hyperelliptic.Meshes.Newton.Surface.LiftedEntries.VerticalContact.next (last := last) source
  refine ⟨destination.sheet, ?_⟩
  have reached := (destination.located.lifted.edge_endpoints_reached (domains.get last).models .left).2
  have reversed := LiftedMesh.opposite_sides source .right .left destination
    (Data.Gaussian.Basic.ext joined.symm upper.symm)
    (Data.Gaussian.Basic.ext joined.symm lower.symm)
  change destination.located.lifted.quad.edge .left = (source.lifted.quad.edge .right).reverse at reversed
  rw [reversed] at reached
  exact reached

end VerticalContact
end Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.LiftedEntries
