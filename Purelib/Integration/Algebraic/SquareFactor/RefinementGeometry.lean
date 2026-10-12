module
import Purelib.Data.List.Flatten
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction

import Purelib.Curves.Hyperelliptic.Differentials.SquareFactor
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Algebraic.SquareFactor.ChildCells
import Purelib.Integration.Algebraic.SquareFactor.ChildMeshes
import Purelib.Integration.Algebraic.SquareFactor.OwnedCells
import Purelib.Integration.Algebraic.SquareFactor.PathContinuation
import Purelib.Integration.Algebraic.SquareFactor.PathInput
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
public import Purelib.Integration.Algebraic.SquareFactor.UniformRefinement
import Purelib.Integration.Algebraic.SquareFactor.Accuracy
import Purelib.Data.Rat.Fraction.Arithmetic

public section

/-!
# Exact whole-path geometry of synchronized refinements

The retained parameter edges, including their order and both endpoints,
are the full dyadic mesh at the sum of the old and additional depths.  This
is stronger than equal cell counts, widths, or total displacements alone.
-/

namespace Purelib.Integration.Algebraic.SquareFactor.RefinementGeometry

open Purelib.Riemann
open Purelib.Riemann.Branches Purelib.Integration.Algebraic.SquareFactor.UniformRefinement

open Purelib.Curves.Hyperelliptic.Differentials.SquareFactor
open Purelib.Integration.Algebraic.SquareFactor.PathInput
open Purelib.Integration.Algebraic.SquareFactor.PathContinuation
open Purelib.Integration.Algebraic.SquareFactor.OwnedCells
open Purelib.Integration.Algebraic.SquareFactor.ChildCells
open Purelib.Integration.Algebraic.SquareFactor.ChildMeshes

open Purelib.Data.Rat in
/-- The rational carrier for retained refinement geometry. -/
abbrev Coordinate := Fraction.Rational
/-- The original certified subdivision endpoint carrier. -/
abbrev Endpoint := Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision.Endpoint
/-- The original subdivision parameter-edge carrier. -/
abbrev ParameterEdge := Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision.ParameterEdge

variable {polynomial : Purelib.Curves.Hyperelliptic.Differentials.SquareFactor.GaussianPolynomial} {request :
  Purelib.Curves.Hyperelliptic.Differentials.SquareFactor.Request}
  {prepared : Purelib.Curves.Hyperelliptic.Differentials.SquareFactor.Prepared polynomial request} {segment :
    Purelib.Integration.Algebraic.SquareFactor.PathInput.Segment}
  {data : Purelib.Integration.Algebraic.SquareFactor.PathInput.Data prepared segment} {safe : data.Safe}

section
open Purelib.Integration.Algebraic.SquareFactor
/-- Read the exact original endpoint pair from a retained compiled cell. -/
@[expose] def parameterEdge (cell : OwnedCells.Cell safe) : ParameterEdge := ⟨cell.edge.left, cell.edge.step.endpoint⟩

/-- Certified endpoints with equal parameters are equal. -/
private theorem endpoint_ext {left right : RefinementGeometry.Endpoint} (equal : left.parameter = right.parameter) :
  left = right := by
  cases left
  cases right
  cases equal
  rfl

end

section
open Purelib.Integration.Algebraic.SquareFactor
open Purelib.Riemann.Branches
/-- Mapping the initial child fraction gives the exact original parent starting endpoint. -/
theorem endpointAt_first (parent : OwnedCells.Cell safe) : ChildCells.endpointAt parent PathContinuation.first =
  parent.edge.left :=
  RefinementGeometry.endpoint_ext (PreparedSheetContinuation.parameterAt_zero parent.edge.left parent.edge.step)

/-- Mapping the final child fraction gives the exact original parent step endpoint. -/
theorem endpointAt_last (parent : OwnedCells.Cell safe) : ChildCells.endpointAt parent PathContinuation.last =
  parent.edge.step.endpoint :=
  RefinementGeometry.endpoint_ext (PreparedSheetContinuation.parameterAt_one parent.edge.left parent.edge.step)

/-- The retained child block reads the exact dyadic subdivision of its original parent edge. -/
theorem block_parameterEdges {parent : OwnedCells.Cell safe} {diameter : RefinementGeometry.Coordinate} {depth : Nat}
    (block : ChildMeshes.Block parent diameter depth) :
    block.cells.map RefinementGeometry.parameterEdge = ClearSheetContinuation.Subdivision.dyadicEdges
      depth parent.edge.left parent.edge.step.endpoint := by
  rw [block.cells_eq]
  change block.mesh.cells.map (fun cell => (⟨cell.edge.left, cell.edge.step.endpoint⟩ :
    RefinementGeometry.ParameterEdge)) = _
  rw [block.mesh.parameterEdges, RefinementGeometry.endpointAt_first, RefinementGeometry.endpointAt_last]

end

open Purelib.Integration.Algebraic.SquareFactor
open Purelib.Riemann.Branches
/-- An expansion reads the ordered flattening of its original parent edges.

Each retained child block contributes the exact dyadic subdivision of its
parent. Concatenation preserves the original parent and child ordering. -/
theorem Expansion.parameterEdges {diameter : RefinementGeometry.Coordinate} {depth : Nat} {parents : List
  (OwnedCells.Cell safe)}
    (expansion : UniformRefinement.Expansion diameter depth parents) :
    expansion.cells.map RefinementGeometry.parameterEdge = parents.flatMap (fun parent =>
      ClearSheetContinuation.Subdivision.dyadicEdges depth parent.edge.left parent.edge.step.endpoint) := by
  induction expansion with
  | nil => rfl
  | @cons parent parents head tail ih =>
      rw [UniformRefinement.Expansion.cells, Purelib.Data.List.Map.map_append, Purelib.Data.List.Flatten.flatMap_cons,
        RefinementGeometry.block_parameterEdges]
      rw [ih]

/-- A uniform refinement of the original dyadic path has the exact dyadic geometry at the sum of its depths. -/
theorem Synchronized.geometry {parents : List (OwnedCells.Cell safe)} {diameter : RefinementGeometry.Coordinate}
  {minimumDepth : Nat}
    (result : UniformRefinement.Synchronized parents diameter minimumDepth) (parentDepth : Nat)
    (parentGeometry : parents.map RefinementGeometry.parameterEdge = ClearSheetContinuation.Subdivision.dyadicEdges
      parentDepth PathContinuation.first PathContinuation.last) :
    result.expansion.cells.map RefinementGeometry.parameterEdge =
      ClearSheetContinuation.Subdivision.dyadicEdges (parentDepth + result.depth) PathContinuation.first last := by
  rw [RefinementGeometry.Expansion.parameterEdges result.expansion,
    ClearSheetContinuation.Subdivision.dyadicEdges_add]
  unfold ClearSheetContinuation.Subdivision.refineDyadicEdges
  rw [← parentGeometry, Purelib.Data.List.Flatten.flatMap_map]
  rfl

/-- A uniform refinement of the original dyadic path has the exact dyadic geometry at the sum of its depths. -/
theorem Refined.geometry {parents : List (OwnedCells.Cell safe)} {target : RefinementGeometry.Coordinate} {parentDepth :
  Nat}
    (result : UniformRefinement.Refined parentDepth parents target)
    (parentGeometry : parents.map RefinementGeometry.parameterEdge = ClearSheetContinuation.Subdivision.dyadicEdges
      parentDepth PathContinuation.first PathContinuation.last) :
    result.cells.map RefinementGeometry.parameterEdge =
      ClearSheetContinuation.Subdivision.dyadicEdges (parentDepth + result.synchronized.depth) PathContinuation.first
        last := by
  rw [result.cells_eq]
  exact RefinementGeometry.Synchronized.geometry result.synchronized parentDepth parentGeometry

end Purelib.Integration.Algebraic.SquareFactor.RefinementGeometry
