module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Integration.Program.Gaussian.Cached.Basic
import Purelib.Algebra.Field.ExplicitField
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.ComparisonAllowance
public import Purelib.Integration.Polynomial.Gaussian.Path.ConstantComparison

import Purelib.Curves.Hyperelliptic.Differentials.SquareFactor
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Algebraic.SquareFactor.CellModels
import Purelib.Integration.Algebraic.SquareFactor.OwnedCells
import Purelib.Integration.Algebraic.SquareFactor.PathContinuation
import Purelib.Integration.Algebraic.SquareFactor.PathInput
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.PreparedSheetContinuation
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
public import Purelib.Integration.Algebraic.SquareFactor.ChildCells
import Purelib.Integration.Algebraic.SquareFactor.MeshBounds
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Integration.Polynomial.Gaussian.Path.Allowance
import Purelib.Polynomial.Dense.Gaussian.Squarefree.SquareFactor.Basic
import Purelib.Polynomial.Dense.Gaussian.Path.Bounds.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Polynomial.Ascending.Gaussian.Basic
import Purelib.Data.Gaussian.Components.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Mathlib.Order.Basic
import Purelib.Tactic.Ring
import Purelib.Data.List.Append
import Purelib.Data.List.Map
import Purelib.Data.List.Membership
import Purelib.Tactic.QuotientFreeOmega

open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius_antitone)

public section

/-!
# Complete direct dyadic child blocks

Each leaf is prepared from its parent's retained point-query owner.  The
finite mesh constructor derives acceptance at a computed sufficient depth,
and its tree retains exact coverage before centres are requested.  The
compiled block caches those centres and derives its constant-partition
comparison certificate rather than accepting one as an input.
-/

namespace Purelib.Integration.Algebraic.SquareFactor.ChildMeshes

open Purelib.Data.List
open Purelib.Data.Gaussian.Norm.Basic (normSq_eq_canonical)

open Purelib.Riemann
open Purelib.Riemann.Branches

open Purelib.Curves.Hyperelliptic.Differentials.SquareFactor
open Purelib.Integration.Algebraic.SquareFactor.PathInput
open Purelib.Integration.Algebraic.SquareFactor.PathContinuation
open Purelib.Integration.Algebraic.SquareFactor.OwnedCells
open Purelib.Integration.Algebraic.SquareFactor.ChildCells
open Purelib.Data.Gaussian.Basic.Canonical

open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)

open Purelib.Data.Rat in
/-- The rational carrier for retained child-mesh requests. -/
abbrev Coordinate := Fraction.Rational
/-- The original certified subdivision endpoint carrier. -/
abbrev Endpoint := ClearSheetContinuation.Subdivision.Endpoint

variable {polynomial : GaussianPolynomial} {request :
  Request}
  {prepared : Prepared polynomial request} {segment :
    Segment}
  {data : Data prepared segment} {safe : data.Safe}

open Purelib.Integration.Algebraic.SquareFactor in
/-- Construct the certified midpoint of the two retained unit-interval endpoints. -/
@[expose] def midpoint (left right : Endpoint) : Endpoint :=
  ⟨ClearSheetContinuation.midpoint left.parameter right.parameter,
    ClearSheetContinuation.midpoint_inside left.inside right.inside⟩

open Purelib.Integration.Algebraic.SquareFactor.ChildMeshes in
open Purelib.Data.Rat in
open Purelib.Integration.Algebraic.SquareFactor in
/-- Mapping a child midpoint through the parent edge equals the midpoint of its mapped parameters. -/
theorem endpointAt_midpoint (parent : Cell safe) (left right : Endpoint) :
    (ChildCells.endpointAt parent (midpoint left right)).parameter =
      ClearSheetContinuation.midpoint (ChildCells.endpointAt parent left).parameter (ChildCells.endpointAt parent
        right).parameter := by
  change parent.edge.parameter (ClearSheetContinuation.midpoint left.parameter right.parameter) =
    ClearSheetContinuation.midpoint (parent.edge.parameter left.parameter) (parent.edge.parameter right.parameter)
  rw [parent.edge.parameter_eq, parent.edge.parameter_eq, parent.edge.parameter_eq]
  unfold CellModels.Span.parameter ClearSheetContinuation.midpoint
  apply Fraction.Field.mul_right_cancel_of_ne (show (2 : Coordinate) ≠ 0 by decide)
  rw [Fraction.Field.div_mul_cancel_of_ne _ 2 (by decide)]
  calc
    (parent.edge.span.interval.lower + parent.edge.span.width * ((left.parameter + right.parameter) / 2)) * 2 =
        parent.edge.span.interval.lower * 2 + parent.edge.span.width *
          (((left.parameter + right.parameter) / 2) * 2) := by ring1
    _ = _ := by
      rw [Fraction.Field.div_mul_cancel_of_ne _ 2 (by decide)]
      ring1

open Purelib.Integration.Algebraic.SquareFactor in
/-- Certified endpoints with equal parameters are equal. -/
private theorem endpoint_ext {left right : Endpoint} (equal : left.parameter = right.parameter) : left =
  right := by
  cases left
  cases right
  cases equal
  rfl

open Purelib.Integration.Algebraic.SquareFactor.ChildMeshes in
open Purelib.Integration.Algebraic.SquareFactor in
/-- The parent-edge map preserves the exact certified midpoint endpoint. -/
theorem endpointAt_midpoint_eq (parent : Cell safe) (left right : Endpoint) :
    ChildCells.endpointAt parent (midpoint left right) = midpoint (ChildCells.endpointAt parent left)
      (ChildCells.endpointAt parent right) :=
  endpoint_ext (endpointAt_midpoint parent left right)

open Purelib.Algebra in
open Purelib.Approximation.Rational in
open Purelib.Data.Rat in
open Purelib.Integration.Algebraic.SquareFactor in
/-- Dividing the initial scale by four advances the quarter-radius depth by one. -/
private theorem quarterRadius_div_four (scale : Coordinate) (depth : Nat) :
    Geometric.Basic.quarterRadius (scale / 4) depth =
      Geometric.Basic.quarterRadius scale (depth + 1) := by
  have scaleDiv : scale / 4 = scale * (1 / 4 : Coordinate) := by
    rw [Field.ExplicitField.div_eq_mul_inv, Field.ExplicitField.div_eq_mul_inv,
      Fraction.Field.one_mul]
  rw [Geometric.Basic.quarterRadius_eq_mul_pow,
    Geometric.Basic.quarterRadius_eq_mul_pow, scaleDiv, pow_succ]
  ring1

set_option genInjectivity false in
open Purelib.Integration.Algebraic.SquareFactor.ChildMeshes Purelib.Integration.Algebraic.SquareFactor.PathContinuation
  in
open Purelib.Integration.Algebraic.SquareFactor in
/-- A dyadic tree of certified child leaves tied to one original parent, diameter, depth and endpoint pair.

Each split retains its two ordered midpoint submeshes, preserving the original leaf preparations and root owners. -/
inductive Mesh (parent : Cell safe) (diameter : Coordinate) : Nat → Endpoint →
  Endpoint → Type
  /-- A retained certified child leaf gives a depth-zero mesh on its original interval. -/ | leaf {left right :
    Endpoint} (value : Leaf parent left right diameter) :
    ChildMeshes.Mesh parent diameter 0 left right
  /-- The retained midpoint halves form the next-depth mesh in their original order. -/ | split {depth : Nat} {left
    right : Endpoint}
      (first : ChildMeshes.Mesh parent diameter depth left (midpoint left
        right))
      (second : ChildMeshes.Mesh parent diameter depth (midpoint left right)
        right) :
      ChildMeshes.Mesh parent diameter (depth + 1) left right

constructive_injectivity Mesh

open Purelib.Integration.Algebraic.SquareFactor.ChildMeshes Purelib.Integration.Algebraic.SquareFactor.PathContinuation
  in
open Purelib.Integration.Algebraic.SquareFactor in
/-- Attempt the exact dyadic child mesh by checking retained leaf preparations from left to right.

Failure of any local leaf check returns no mesh at this depth; it does not rule out a finer subdivision. -/
@[expose] def tryBuild (parent : Cell safe) (diameter : Coordinate) (positive : 0 < diameter) :
    (depth : Nat) → (left right : Endpoint) → left.parameter ≤ right.parameter →
      Option (Mesh parent diameter depth left right)
  | 0, left, right, ordered =>
      (ChildCells.tryLeaf parent left right ordered diameter positive).map Mesh.leaf
  | depth + 1, left, right, ordered => do
      let first ← tryBuild parent diameter positive depth left (midpoint left right)
        (ClearSheetContinuation.left_le_midpoint ordered)
      let second ← tryBuild parent diameter positive depth (midpoint left right) right
        (ClearSheetContinuation.midpoint_le_right ordered)
      pure (.split first second)

section
open Purelib.Integration.Algebraic.SquareFactor.ChildMeshes
open Purelib.Approximation.Rational
open Purelib.Data.Rat
open Purelib.Integration.Algebraic.SquareFactor
/-- Construct a child mesh from a quarter-radius movement bound below the uniform prepared clearance.

Each split transports the original bound to its midpoint halves, keeping the same parent and diameter request at every
leaf. -/
@[expose] def build (parent : Cell safe) (diameter : Coordinate) (positive : 0 < diameter) :
    (depth : Nat) → (left right : Endpoint) → (ordered : left.parameter ≤ right.parameter) →
    Geometric.Basic.quarterRadius (ClearSheetContinuation.variationBound (PathContinuation.clearSegment safe)
      (ChildCells.endpointAt parent left).parameter (ChildCells.endpointAt parent right).parameter) depth <
        PreparedSheetContinuation.uniformPreparedClearanceFloor (PathContinuation.clearSegment safe) diameter →
    Mesh parent diameter depth left right
  | 0, left, right, ordered, small =>
      .leaf (ChildCells.prepareLeaf parent left right ordered diameter positive (by
        simpa only [Geometric.Basic.quarterRadius_eq_mul_pow, pow_zero,
          Fraction.Field.mul_one_direct] using small))
  | depth + 1, left, right, ordered, small =>
      .split
        (ChildMeshes.build parent diameter positive depth left (midpoint left
          right)
          (ClearSheetContinuation.left_le_midpoint ordered) (by
            rw [endpointAt_midpoint, ClearSheetContinuation.variationBound_left_midpoint,
              quarterRadius_div_four]
            exact small))
        (ChildMeshes.build parent diameter positive depth (midpoint left
          right) right
          (ClearSheetContinuation.midpoint_le_right ordered) (by
            rw [endpointAt_midpoint, ClearSheetContinuation.variationBound_midpoint_right,
              quarterRadius_div_four]
            exact small))

/-- The uniform movement certificate makes the mesh checker return the exact constructed dyadic mesh. -/
theorem tryBuild_eq_some_build (parent : Cell safe) (diameter : Coordinate) (positive : 0 <
  diameter)
    (depth : Nat) (left right : Endpoint) (ordered : left.parameter ≤ right.parameter)
    (small : Geometric.Basic.quarterRadius (ClearSheetContinuation.variationBound (PathContinuation.clearSegment safe)
      (ChildCells.endpointAt parent left).parameter (ChildCells.endpointAt parent right).parameter) depth <
        PreparedSheetContinuation.uniformPreparedClearanceFloor (PathContinuation.clearSegment safe) diameter) :
    tryBuild parent diameter positive depth left right ordered =
      some (build parent diameter positive depth left right ordered small) := by
  induction depth generalizing left right with
  | zero =>
      have bound : ClearSheetContinuation.variationBound (PathContinuation.clearSegment safe)
          (ChildCells.endpointAt parent left).parameter (ChildCells.endpointAt parent right).parameter <
            PreparedSheetContinuation.uniformPreparedClearanceFloor (PathContinuation.clearSegment safe) diameter := by
        simpa only [Geometric.Basic.quarterRadius_eq_mul_pow, pow_zero,
          Fraction.Field.mul_one_direct] using small
      rw [tryBuild, ChildCells.tryLeaf_eq_some_prepareLeaf parent left right ordered diameter positive bound]
      rfl
  | succ depth ih =>
      have firstSmall : Geometric.Basic.quarterRadius
          (ClearSheetContinuation.variationBound (PathContinuation.clearSegment safe)
            (ChildCells.endpointAt parent left).parameter (ChildCells.endpointAt parent (midpoint left
              right)).parameter) depth <
              PreparedSheetContinuation.uniformPreparedClearanceFloor (PathContinuation.clearSegment safe) diameter :=
                by
        rw [endpointAt_midpoint, ClearSheetContinuation.variationBound_left_midpoint,
          quarterRadius_div_four]
        exact small
      have secondSmall : Geometric.Basic.quarterRadius
          (ClearSheetContinuation.variationBound (PathContinuation.clearSegment safe)
            (ChildCells.endpointAt parent (midpoint left right)).parameter (ChildCells.endpointAt parent
              right).parameter) depth <
              PreparedSheetContinuation.uniformPreparedClearanceFloor (PathContinuation.clearSegment safe) diameter :=
                by
        rw [endpointAt_midpoint, ClearSheetContinuation.variationBound_midpoint_right,
          quarterRadius_div_four]
        exact small
      rw [tryBuild, ih left (midpoint left right) (ClearSheetContinuation.left_le_midpoint ordered) firstSmall]
      rw [ih (midpoint left right) right (ClearSheetContinuation.midpoint_le_right ordered) secondSmall]
      rfl

end

open Purelib.Integration.Algebraic.SquareFactor.PathContinuation in
open Purelib.Approximation.Rational in
open Purelib.Integration.Algebraic.SquareFactor in
/-- Construct the exact full-parent child mesh at any depth meeting the original sufficient dyadic depth. -/
@[expose] def generateAtDepth (parent : Cell safe) (diameter : Coordinate) (positive : 0 <
  diameter) (depth : Nat)
    (enough : PreparedSheetContinuation.Subdivision.sufficientDyadicDepth (PathContinuation.clearSegment safe)
      parent.edge.left parent.edge.step.endpoint diameter ≤ depth) :
    Mesh parent diameter depth first last :=
  build parent diameter positive _ first PathContinuation.last (by decide) (by
    have sufficient := PreparedSheetContinuation.Subdivision.sufficientDyadicDepth_variation_lt
      (PathContinuation.clearSegment safe) parent.edge.left parent.edge.step.endpoint positive
    have small := (quarterRadius_antitone
      (ClearSheetContinuation.variationBound_nonneg (PathContinuation.clearSegment safe)
        parent.edge.left.parameter parent.edge.step.endpoint.parameter) enough).trans_lt
      sufficient
    simpa only [ChildCells.endpointAt, first, PathContinuation.last, Edge.parameter,
      PreparedSheetContinuation.parameterAt_zero,
      PreparedSheetContinuation.parameterAt_one] using small)

namespace Mesh

variable {parent : Cell safe} {diameter :
  Coordinate} {level : Nat} {left right :
  Endpoint}

section
open Purelib.Integration.Algebraic.SquareFactor.PathContinuation
open Purelib.Integration.Algebraic.SquareFactor
/-- Read the retained leaf cells in left-to-right order from the original dyadic mesh. -/
@[expose] def cells : {level : Nat} → {left right : Endpoint} → Mesh parent diameter level left
  right → List (Cell safe)
  | _, _, _, .leaf value => [value.cell]
  | _, _, _, .split first second => Mesh.cells first ++
    Mesh.cells second

/-- Read the exact original prepared leaf edges in order without constructing their root witnesses or cell models. -/
@[expose] def edges : {level : Nat} → {left right : Endpoint} →
    Mesh parent diameter level left right → List (Edge safe)
  | _, _, _, .leaf value => [value.edge]
  | _, _, _, .split first second => first.edges ++ second.edges

/-- Compiling the retained leaf-edge list gives exactly the original mesh's ordered cell readback. -/
theorem compileEdges_edges (mesh : Mesh parent diameter level left right) :
    OwnedCells.compileEdges mesh.edges = mesh.cells := by
  induction mesh with
  | leaf value => exact congrArg (fun cell => [cell]) value.cell_eq_compileEdge.symm
  | split first second firstEq secondEq =>
      rewrite [edges, OwnedCells.compileEdges_append, firstEq, secondEq]
      rfl

/-- The retained dyadic mesh has exactly two to the power of its depth cells.

A split retains both equal-depth halves in order, so their lengths add to the next dyadic power. -/
theorem cellCount (mesh : Mesh parent diameter level left right) : mesh.cells.length = 2 ^ level := by
  induction mesh with
  | leaf _ => rfl
  | split first second ihFirst ihSecond =>
      rw [Mesh.cells, Append.length_append, ihFirst, ihSecond, pow_succ]
      omega

end

open Purelib.Integration.Algebraic.SquareFactor.PathContinuation in
open Purelib.Data.Gaussian in
open Purelib.Integration.Algebraic.SquareFactor in
open Purelib.Integration.Polynomial.Gaussian.Path in
/-- Every retained child center meets its comparison allowance against the original parent center.

Each leaf retains its original parent-center comparison allowance; a split transports the bound through membership in
its two ordered halves. -/
theorem errors_le (mesh : Mesh parent diameter level left right) :
    ∀ cell ∈ mesh.cells, Norm.Basic.normSq (cell.model.center - parent.model.center) ≤
      PathModel.parentChildAllowance parent.model.cell cell.model.cell := by
  induction mesh with
  | leaf value =>
      intro cell member
      have equal := Membership.mem_singleton.mp member
      cases equal
      exact value.error_le
  | split first second ihFirst ihSecond =>
      intro cell member
      rcases Membership.mem_append.mp member with member | member
      · exact ihFirst cell member
      · exact ihSecond cell member

section
open Purelib.Integration.Algebraic.SquareFactor.PathContinuation
open Purelib.Integration.Algebraic.SquareFactor
/-- The retained child cells read the exact dyadic parameter edges between the original mapped endpoints.

The leaf endpoints and retained midpoint splits read the same ordered dyadic edges after mapping through the original
parent. -/
theorem parameterEdges (mesh : Mesh parent diameter level left right) :
    mesh.cells.map (fun cell =>
      (⟨cell.edge.left, cell.edge.step.endpoint⟩ : ClearSheetContinuation.Subdivision.ParameterEdge)) =
      ClearSheetContinuation.Subdivision.dyadicEdges level (ChildCells.endpointAt parent left) (ChildCells.endpointAt
        parent right) := by
  induction mesh with
  | leaf _ => rfl
  | split first second ihFirst ihSecond =>
      simp only [Mesh.cells, Map.map_append, ClearSheetContinuation.Subdivision.dyadicEdges]
      rw [ihFirst, ihSecond]
      rw [endpointAt_midpoint_eq]
      rfl

/-- Every retained child cell keeps the original mesh's root-diameter request.

Every leaf keeps the same original diameter index, and membership selects a leaf from one of the retained midpoint
halves. -/
theorem diameters (mesh : Mesh parent diameter level left right) :
    ∀ cell ∈ mesh.cells, cell.edge.step.rootDiameter = diameter := by
  induction mesh with
  | leaf value =>
      intro cell member
      have equal := Membership.mem_singleton.mp member
      cases equal
      rfl
  | split first second ihFirst ihSecond =>
      intro cell member
      rcases Membership.mem_append.mp member with member | member
      · exact ihFirst cell member
      · exact ihSecond cell member

end

open Purelib.Integration.Algebraic.SquareFactor.PathContinuation in
open Purelib.Data.Gaussian in
open Purelib.Integration.Polynomial.Gaussian.Cell in
open Purelib.Integration.Polynomial.Gaussian.Path in
/-- Appending retained cell lists adds their exact displacement sums. -/
private theorem displacementSum_append (first second : List Basic.CellModel) :
    PathModel.displacementSum (first ++ second) =
      PathModel.displacementSum first + PathModel.displacementSum second := by
  induction first with
  | nil => exact (Basic.zero_add _).symm
  | cons head tail ih =>
      simp only [List.cons_append, PathModel.displacementSum_cons]
      rw [ih, Basic.add_assoc]

open Purelib.Integration.Algebraic.SquareFactor.PathContinuation in
open Purelib.Data.Gaussian in
open Purelib.Integration.Algebraic.SquareFactor in
open Purelib.Integration.Polynomial.Gaussian.Path in
/-- The retained child displacement sum is the difference between the original mapped physical endpoints.

The ordered mesh halves meet at the retained midpoint, so their displacement sums telescope to the original outer
endpoints. -/
theorem displacement (mesh : Mesh parent diameter level left right) :
    PathModel.displacementSum (mesh.cells.map (fun cell => cell.model.cell)) =
      segment.point (ChildCells.endpointAt parent right).parameter - segment.point (ChildCells.endpointAt parent
        left).parameter := by
  induction mesh with
  | leaf value =>
      change value.cell.model.cell.displacement + 0 = _
      exact Basic.add_zero _
  | split first second ihFirst ihSecond =>
      rw [Mesh.cells, Map.map_append, displacementSum_append, ihFirst, ihSecond]
      apply Basic.ext <;>
        simp only [Basic.add_re, Basic.add_im, Basic.sub_re, Basic.sub_im] <;> ring1

end Mesh

open Purelib.Data.Gaussian in
open Purelib.Integration.Algebraic.SquareFactor in
open Purelib.Integration.Polynomial.Gaussian.Path in
/-- Build the ordered constant comparison from the retained children and their individual parent-center error bounds.

Each original child keeps its cached center and certified parent allowance. Structural recursion retains the children
and their error list in the same order. -/
@[expose] def comparisons (parent : Cell safe) : (children : List (Cell safe)) →
    (∀ child ∈ children, Norm.Basic.normSq (child.model.center - parent.model.center) ≤
      PathModel.parentChildAllowance parent.model.cell child.model.cell) →
    PathModel.ConstantComparison parent.model.center
      (children.map (fun child => PathModel.comparisonCell parent.model.cell child.model.cell))
      (children.map (fun child => child.model.center - parent.model.center))
  | [], _ => .nil
  | child :: children, bounds =>
      .cons child.model.center (child.model.center - parent.model.center) rfl rfl
        (by
          have scalar := bounds child (List.mem_cons_self ..)
          rw [normSq_eq_canonical] at scalar
          exact scalar)
        (ChildMeshes.comparisons parent children (fun cell member => bounds
          cell (List.mem_cons_of_mem _ member)))

open Purelib.Integration.Polynomial.Gaussian.Cell in
open Purelib.Integration.Polynomial.Gaussian.Path in
/-- Replacing child allowances by comparison allowances preserves their exact displacement sum. -/
private theorem comparison_displacement (parent : Basic.CellModel) (children : List Basic.CellModel) :
    PathModel.displacementSum (children.map (PathModel.comparisonCell parent)) =
      PathModel.displacementSum children := by
  induction children with
  | nil => rfl
  | cons child children ih =>
      simp only [List.map_cons, PathModel.displacementSum_cons]
      rw [ih]
      rfl

set_option genInjectivity false in
open Purelib.Integration.Algebraic.SquareFactor.PathContinuation in
open Purelib.Integration.Algebraic.SquareFactor in
/-- The original full-parent dyadic mesh with its cached ordered child cell list. -/
structure Block (parent : Cell safe) (diameter : Coordinate) (depth : Nat) where
  /-- The exact full-parent dyadic mesh at the retained diameter and depth. -/ mesh : Mesh parent diameter
    depth first PathContinuation.last
  /-- The cached ordered list of original mesh cells. -/ cells : List (Cell safe)
  /-- The cached list equals the exact original mesh's cell readback. -/ cells_eq : cells = mesh.cells

constructive_injectivity Block

open Purelib.Integration.Algebraic.SquareFactor.PathContinuation in
open Purelib.Integration.Algebraic.SquareFactor in
/-- Retain a supplied original mesh and its already compiled ordered cell cache with the exact readback identity. -/
@[expose] def Block.ofCells {parent : Cell safe} {diameter : Coordinate} {depth : Nat}
    (mesh : Mesh parent diameter depth first PathContinuation.last)
    (cells : List (Cell safe)) (cellsEq : cells = mesh.cells) : Block parent diameter depth :=
  ⟨mesh, cells, cellsEq⟩

open Purelib.Integration.Algebraic.SquareFactor.PathContinuation in
open Purelib.Integration.Algebraic.SquareFactor in
/-- Cache the exact original mesh's ordered cells with their defining equation. -/
@[expose] def compile {parent : Cell safe} {diameter : Coordinate} {depth : Nat}
    (mesh : Mesh parent diameter depth first PathContinuation.last) : Block parent diameter
      depth :=
  Block.ofCells mesh mesh.cells rfl

open Purelib.Integration.Algebraic.SquareFactor.PathContinuation in
open Purelib.Integration.Algebraic.SquareFactor in
/-- The original mesh and cell-cache identity preserve exactly the original compiled child block. -/
theorem Block.ofCells_eq_compile {parent : Cell safe} {diameter : Coordinate} {depth : Nat}
    (mesh : Mesh parent diameter depth first PathContinuation.last)
    (cells : List (Cell safe)) (cellsEq : cells = mesh.cells) :
    Block.ofCells mesh cells cellsEq = compile mesh := by
  cases cellsEq
  rfl

namespace Block

variable {parent : Cell safe} {diameter :
  Coordinate} {depth : Nat}
  (block : Block parent diameter depth)

/-- Read the path model from the exact retained child cell models. -/
@[expose] def pathModel : PathModel := ⟨block.cells.map (fun cell => cell.model.cell)⟩

open Purelib.Integration.Algebraic.SquareFactor.PathContinuation in
open Purelib.Data.Gaussian in
open Purelib.Integration.Algebraic.SquareFactor in
open Purelib.Integration.Polynomial.Gaussian.Path in
/-- Certify the retained child comparison path against its original constant parent.

The certificate retains the ordered center-error list and the exact displacement agreement from the original mesh. -/
@[expose] def partition : PathModel.ConstantPartitionCertificate parent.model.cell
    (PathModel.comparisonBlock parent.model.cell block.pathModel) where
  reference := parent.model.center
  parent_polynomial_eq := rfl
  errors := block.cells.map (fun child => child.model.center - parent.model.center)
  comparison := by
    have bound : ∀ child ∈ block.cells, Norm.Basic.normSq (child.model.center - parent.model.center) ≤
        PathModel.parentChildAllowance parent.model.cell child.model.cell := by
      rw [block.cells_eq]
      exact block.mesh.errors_le
    have certificate := comparisons parent block.cells bound
    unfold PathModel.comparisonBlock pathModel
    rw [Map.map_map]
    dsimp only [Function.comp_def]
    exact certificate
  displacement_eq := by
    rw [PathModel.comparisonBlock, comparison_displacement]
    change PathModel.displacementSum (block.cells.map (fun cell => cell.model.cell)) = _
    rw [block.cells_eq, block.mesh.displacement]
    simp only [ChildCells.endpointAt, first, PathContinuation.last, Edge.parameter,
      PreparedSheetContinuation.parameterAt_zero,
      PreparedSheetContinuation.parameterAt_one]
    rfl

open Purelib.Data.Gaussian in
open Purelib.Integration.Polynomial.Gaussian.Path in
/-- The retained child-minus-parent integral sample meets the aggregate allowance of their exact comparison block. -/
theorem integral_difference_le : Norm.Basic.normSq (block.pathModel.integralSample -
  parent.model.cell.integralSample) ≤
    (PathModel.comparisonBlock parent.model.cell block.pathModel).aggregateAllowance := by
  have bound := ConstantComparison.PathModel.ConstantPartitionCertificate.integral_difference_le block.partition
  rw [← normSq_eq_canonical] at bound
  rw [PathModel.comparisonBlock_integralSample] at bound
  exact bound

end Block

end Purelib.Integration.Algebraic.SquareFactor.ChildMeshes
