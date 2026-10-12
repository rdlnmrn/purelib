module
import Purelib.Data.List.Membership
import Purelib.Data.List.Append
import Purelib.Data.List.Map
import Purelib.Data.Nat.Order
import Purelib.Data.Nat.Multiplication

meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Integration.Program.Gaussian.Cached.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.ComparisonAllowance
public import Purelib.Integration.Polynomial.Gaussian.Path.CompatibleRefinement

import Purelib.Curves.Hyperelliptic.Differentials.SquareFactor
import Purelib.Data.Rat.Fraction.Compatibility
public import Purelib.Integration.Algebraic.SquareFactor.ChildMeshes
import Purelib.Integration.Algebraic.SquareFactor.CoefficientBounds
import Purelib.Integration.Algebraic.SquareFactor.MeshBounds
import Purelib.Integration.Algebraic.SquareFactor.OwnedCells
import Purelib.Integration.Algebraic.SquareFactor.PathContinuation
import Purelib.Integration.Algebraic.SquareFactor.PathInput
import Purelib.Riemann.Branches.PreparedSheetContinuation
import Purelib.Integration.Algebraic.SquareFactor.ChildBounds
public import Purelib.Integration.Algebraic.SquareFactor.Accuracy
public import Purelib.Data.Task.Parallel
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Integration.Algebraic.SquareFactor.CellModels
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Polynomial.Dense.Gaussian.Squarefree.SquareFactor.Basic
import Purelib.Polynomial.Dense.Gaussian.Path.Bounds.Basic
import Purelib.Data.Gaussian.Components.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Mathlib.Order.Basic
import Mathlib.Data.Nat.Basic
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega

public section

/-!
# Synchronized refinement of a complete retained path

A checked finite search gives all parent cells the same additional depth,
bounded by a proved sufficient maximum.  Each block retains its inherited
root occurrence, while the uniform leaf count and squared width are preserved
across the whole path.  Only the accepted whole bank computes cell centres.
-/

namespace Purelib.Integration.Algebraic.SquareFactor.UniformRefinement

open Purelib.Riemann
open Purelib.Integration.Algebraic.SquareFactor
open Purelib.Riemann.Branches

open Purelib.Curves.Hyperelliptic.Differentials.SquareFactor
open Purelib.Integration.Algebraic.SquareFactor.PathInput
open Purelib.Integration.Algebraic.SquareFactor.PathContinuation
open Purelib.Integration.Algebraic.SquareFactor.OwnedCells
open Purelib.Integration.Algebraic.SquareFactor.CoefficientBounds
open Purelib.Integration.Algebraic.SquareFactor.ChildMeshes

open Purelib.Data.Gaussian.Basic.Canonical

open Purelib.Data.Rat in
/-- The rational carrier for synchronized refinement requests. -/
abbrev Coordinate := Fraction.Rational

variable {polynomial : Purelib.Curves.Hyperelliptic.Differentials.SquareFactor.GaussianPolynomial} {request :
  Purelib.Curves.Hyperelliptic.Differentials.SquareFactor.Request}
  {prepared : Purelib.Curves.Hyperelliptic.Differentials.SquareFactor.Prepared polynomial request} {segment :
    Purelib.Integration.Algebraic.SquareFactor.PathInput.Segment}
  {data : Purelib.Integration.Algebraic.SquareFactor.PathInput.Data prepared segment} {safe : data.Safe}

/-- The maximum of the requested minimum and every original parent's sufficient child-mesh depth. -/
@[expose] def maximumAdditionalDepth (diameter : UniformRefinement.Coordinate) (minimumDepth : Nat) : List
  (OwnedCells.Cell safe) → Nat
  | [] => minimumDepth
  | parent :: parents => max
      (PreparedSheetContinuation.Subdivision.sufficientDyadicDepth (PathContinuation.clearSegment safe)
        parent.edge.left parent.edge.step.endpoint diameter)
      (Purelib.Integration.Algebraic.SquareFactor.UniformRefinement.maximumAdditionalDepth diameter minimumDepth
        parents)

/-- The common sufficient maximum meets the original minimum-depth request. -/
theorem minimum_le_maximumAdditionalDepth (diameter : UniformRefinement.Coordinate) (minimumDepth : Nat)
    (parents : List (OwnedCells.Cell safe)) :
    minimumDepth ≤ UniformRefinement.maximumAdditionalDepth diameter minimumDepth parents := by
  induction parents with
  | nil => exact Nat.le_refl _
  | cons parent parents ih => exact ih.trans (Purelib.Data.Nat.Order.le_max_right _ _)

/-- Every retained parent's sufficient depth lies below the common maximum. -/
theorem sufficient_le_maximumAdditionalDepth (diameter : UniformRefinement.Coordinate) (minimumDepth : Nat)
    (parents : List (OwnedCells.Cell safe)) :
    ∀ parent ∈ parents,
      PreparedSheetContinuation.Subdivision.sufficientDyadicDepth (PathContinuation.clearSegment safe)
        parent.edge.left parent.edge.step.endpoint diameter ≤
          UniformRefinement.maximumAdditionalDepth diameter minimumDepth parents := by
  induction parents with
  | nil => intro parent member; nomatch member
  | cons parent parents ih =>
      intro cell member
      rcases Purelib.Data.List.Membership.mem_cons.mp member with equal | member
      · cases equal; exact Purelib.Data.Nat.Order.le_max_left _ _
      · exact (ih cell member).trans (Purelib.Data.Nat.Order.le_max_right _ _)

set_option genInjectivity false in
/-- An ordered bank of compiled child blocks at one common diameter and depth, indexed by the exact parent cells.

Each retained block keeps its original parent identity and cached mesh cells. -/
inductive Expansion (diameter : UniformRefinement.Coordinate) (depth : Nat) : List (OwnedCells.Cell safe) → Type
  /-- The empty original parent list has an empty retained bank. -/ | nil :
    Purelib.Integration.Algebraic.SquareFactor.UniformRefinement.Expansion diameter depth []
  /-- Prepend the exact original parent's retained compiled child block to the remaining expansion. -/ | cons {parent :
    OwnedCells.Cell safe} {parents : List (OwnedCells.Cell safe)}
      (head : ChildMeshes.Block parent diameter depth) (tail :
        Purelib.Integration.Algebraic.SquareFactor.UniformRefinement.Expansion diameter depth parents) :
      Purelib.Integration.Algebraic.SquareFactor.UniformRefinement.Expansion diameter depth (parent :: parents)

constructive_injectivity Expansion

namespace Expansion

variable {diameter : Purelib.Integration.Algebraic.SquareFactor.UniformRefinement.Coordinate} {depth : Nat}

/-- Flatten the exact retained child block cells in original parent order. -/
@[expose] def cells : {parents : List (OwnedCells.Cell safe)} → UniformRefinement.Expansion diameter depth parents →
  List (OwnedCells.Cell safe)
  | _, .nil => []
  | _, .cons head tail => head.cells ++ Purelib.Integration.Algebraic.SquareFactor.UniformRefinement.Expansion.cells
    tail

open Purelib.Integration.Polynomial.Gaussian.Cell in
/-- Flatten the retained child block model cells in original parent order. -/
@[expose] def models : {parents : List (OwnedCells.Cell safe)} → UniformRefinement.Expansion diameter depth parents →
  List Basic.CellModel
  | _, .nil => []
  | _, .cons head tail => head.pathModel.cells ++
    Purelib.Integration.Algebraic.SquareFactor.UniformRefinement.Expansion.models tail

/-- The retained model list is exactly the model readback of the retained compiled cells. -/
theorem models_eq {parents : List (OwnedCells.Cell safe)} (expansion : UniformRefinement.Expansion diameter depth
  parents) :
    expansion.models = expansion.cells.map (fun cell => cell.model.cell) := by
  induction expansion with
  | nil => rfl
  | cons head tail ih =>
      rw [UniformRefinement.Expansion.models, UniformRefinement.Expansion.cells, Purelib.Data.List.Map.map_append, ih]
      rfl

open Purelib.Integration.Polynomial.Gaussian.Path in
/-- Read the compatible constant refinement from the original retained block certificates. -/
@[expose] def refinement : {parents : List (OwnedCells.Cell safe)} → (expansion : UniformRefinement.Expansion diameter
  depth parents) →
    Basic.PathModel.CompatibleConstantPathRefinement (parents.map (fun cell => cell.model.cell)) expansion.models
  | _, .nil => .nil
  | _, .cons head tail => .cons head.partition
    (Purelib.Integration.Algebraic.SquareFactor.UniformRefinement.Expansion.refinement tail)

/-- The retained expansion has the original parent count times two to the common additional depth cells. -/
theorem count {parents : List (OwnedCells.Cell safe)} (expansion : UniformRefinement.Expansion diameter depth parents) :
    expansion.cells.length = parents.length * 2 ^ depth := by
  induction expansion with
  | nil => exact (Nat.zero_mul _).symm
  | @cons parent parents head tail ih =>
      rw [UniformRefinement.Expansion.cells, Purelib.Data.List.Append.length_append,
        ChildBounds.Block.cellCount head,
        ih, List.length_cons]
      rw [Purelib.Data.Nat.Multiplication.right_distrib, Nat.one_mul, Nat.add_comm]

open Purelib.Integration.Algebraic.SquareFactor.PathContinuation in
open Purelib.Approximation.Rational in
/-- Nested quarter radii add their exact depths. -/
private theorem quarterRadius_nested (scale : UniformRefinement.Coordinate) (first second : Nat) :
    Geometric.Basic.quarterRadius (Geometric.Basic.quarterRadius scale first) second =
      Geometric.Basic.quarterRadius scale (first + second) := by
  rw [Geometric.Basic.quarterRadius_eq_mul_pow, Geometric.Basic.quarterRadius_eq_mul_pow,
    Geometric.Basic.quarterRadius_eq_mul_pow, pow_add]
  ring1

open Purelib.Approximation.Rational in
/-- Uniform original parent widths give child widths at the sum of the retained depths. -/
theorem widths {parents : List (OwnedCells.Cell safe)} (expansion : UniformRefinement.Expansion diameter depth parents)
    (parentDepth : Nat)
    (parentWidths : ∀ parent ∈ parents,
      parent.edge.span.width ^ 2 = Geometric.Basic.quarterRadius 1 parentDepth) :
    ∀ child ∈ expansion.cells, child.edge.span.width ^ 2 =
      Geometric.Basic.quarterRadius 1 (parentDepth + depth) := by
  induction expansion with
  | nil => intro child member; nomatch member
  | @cons parent parents head tail ih =>
      intro child member
      rcases Purelib.Data.List.Membership.mem_append.mp member with member | member
      · rw [ChildBounds.Block.width_sq head child member,
          parentWidths parent (List.mem_cons_self ..)]
        rw [UniformRefinement.Expansion.quarterRadius_nested]
      · exact ih (fun cell member => parentWidths cell (List.mem_cons_of_mem _ member))
          child member

/-- Every retained expanded child keeps the original common diameter request. -/
theorem diameters {parents : List (OwnedCells.Cell safe)} (expansion : UniformRefinement.Expansion diameter depth
  parents) :
    ∀ child ∈ expansion.cells, child.edge.step.rootDiameter = diameter := by
  induction expansion with
  | nil => intro child member; nomatch member
  | cons head tail ih =>
      intro child member
      rcases Purelib.Data.List.Membership.mem_append.mp member with member | member
      · exact ChildBounds.Block.diameter_eq head child member
      · exact ih child member

open Purelib.Approximation.Rational in
/-- Uniform original parent widths give the explicit parameter-and-root local allowance for every retained child. -/
theorem local_allowance_le {parents : List (OwnedCells.Cell safe)} (expansion : UniformRefinement.Expansion diameter
  depth parents)
    (parentDepth : Nat)
    (parentWidths : ∀ parent ∈ parents,
      parent.edge.span.width ^ 2 = Geometric.Basic.quarterRadius 1 parentDepth) :
    ∀ child ∈ expansion.cells, child.model.cell.localAllowance ≤
      CoefficientBounds.parameterSlope data * Geometric.Basic.quarterRadius 1 (parentDepth + depth) +
        CoefficientBounds.rootSlope data * diameter := by
  intro child member
  have bound := MeshBounds.cell_allowance_le child
  rw [expansion.widths parentDepth parentWidths child member, expansion.diameters child member] at bound
  exact bound

open Purelib.Data.Gaussian in
open Purelib.Data.List in
open Purelib.Data.Rat in
open Purelib.Integration.Polynomial.Gaussian.Path in
/-- Retained parent and child bounds control every exact comparison model's displacement and local allowance. -/
theorem comparison_bounds {parents : List (OwnedCells.Cell safe)} (expansion : UniformRefinement.Expansion diameter
  depth parents)
    (movement parentAllowance childAllowance : UniformRefinement.Coordinate)
    (parentBounds : ∀ parent ∈ parents, parent.model.cell.localAllowance ≤ parentAllowance)
    (childBounds : ∀ child ∈ expansion.cells,
      Data.Gaussian.Norm.Basic.normSq child.model.cell.displacement ≤ movement ∧ child.model.cell.localAllowance ≤
        childAllowance) :
    ∀ model ∈ (CompatibleRefinement.PathModel.CompatibleConstantPathRefinement.comparisonCells expansion.refinement),
      Data.Gaussian.Norm.Basic.normSq model.displacement ≤ movement ∧ model.localAllowance ≤ 2 * (parentAllowance +
        childAllowance) := by
  induction expansion with
  | nil => intro model member; nomatch member
  | @cons parent parents head tail ih =>
      intro model member
      rcases Purelib.Data.List.Membership.mem_append.mp member with member | member
      · change model ∈ head.pathModel.cells.map (Basic.PathModel.comparisonCell parent.model.cell) at member
        rcases Map.mem_map.mp member with ⟨childModel, childMember, rfl⟩
        change childModel ∈ head.cells.map (fun child => child.model.cell) at childMember
        rcases Map.mem_map.mp childMember with ⟨child, cellMember, rfl⟩
        have childBound := childBounds child ((Purelib.Data.List.Membership.mem_append.mpr (Or.inl cellMember)))
        refine ⟨childBound.1, ?_⟩
        exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          (add_le_add (parentBounds parent (List.mem_cons_self ..)) childBound.2) (by decide)
      · exact ih (fun cell member => parentBounds cell (List.mem_cons_of_mem _ member))
          (fun child member => childBounds child ((Purelib.Data.List.Membership.mem_append.mpr (Or.inr member)))) model
            member

end Expansion

open Purelib.Integration.Algebraic.SquareFactor.PathContinuation in
set_option genInjectivity false in
/-- An ordered bank of original child meshes sharing one diameter and depth and indexed by their exact parents. -/
inductive MeshBank (diameter : UniformRefinement.Coordinate) (depth : Nat) : List (OwnedCells.Cell safe) → Type
  /-- The empty original parent list has an empty retained bank. -/ | nil :
    Purelib.Integration.Algebraic.SquareFactor.UniformRefinement.MeshBank diameter depth []
  /-- Prepend the exact original parent's retained child mesh to the remaining mesh bank. -/ | cons {parent :
    OwnedCells.Cell safe} {parents : List (OwnedCells.Cell safe)}
      (head : ChildMeshes.Mesh parent diameter depth first last) (tail :
        Purelib.Integration.Algebraic.SquareFactor.UniformRefinement.MeshBank diameter depth parents) :
      Purelib.Integration.Algebraic.SquareFactor.UniformRefinement.MeshBank diameter depth (parent :: parents)

constructive_injectivity MeshBank

/-- Compile the retained mesh bank in order, caching each original mesh's cell list.

The original parent order determines each retained compiled child block.
Structural recursion reuses the supplied remaining bank without choosing new meshes. -/
@[expose] def MeshBank.sequentialCompile {diameter : UniformRefinement.Coordinate} {depth : Nat} :
    {parents : List (OwnedCells.Cell safe)} → UniformRefinement.MeshBank diameter depth parents →
      UniformRefinement.Expansion diameter depth parents
  | _, .nil => .nil
  | _, .cons head tail => .cons (ChildMeshes.compile head) tail.sequentialCompile

section
open Purelib.Integration.Algebraic.SquareFactor.PathContinuation
open Purelib.Data
/-- Compile the original mesh bank in groups of four parallel tasks while retaining the exact original parent order. -/
@[expose] def MeshBank.compile {diameter : UniformRefinement.Coordinate} {depth : Nat} :
    {parents : List (OwnedCells.Cell safe)} → UniformRefinement.MeshBank diameter depth parents →
      UniformRefinement.Expansion diameter depth parents
  | _, .nil => .nil
  | _, .cons head .nil => .cons (ChildMeshes.compile head) .nil
  | _, .cons head (.cons second .nil) =>
      .cons (ChildMeshes.compile head) (.cons (ChildMeshes.compile second) .nil)
  | _, .cons head (.cons second (.cons third .nil)) =>
      .cons (ChildMeshes.compile head)
        (.cons (ChildMeshes.compile second) (.cons (ChildMeshes.compile third) .nil))
  | _, .cons first (.cons second (.cons third (.cons fourth tail))) =>
      let results := Task.Parallel.four
        (fun _ => ChildMeshes.compile first)
        (fun _ => ChildMeshes.compile second)
        (fun _ => ChildMeshes.compile third)
        (fun _ => ChildMeshes.compile fourth)
      .cons results.1 (.cons results.2.1 (.cons results.2.2.1 (.cons results.2.2.2 tail.compile)))

/-- Parallel mesh-bank compilation equals the exact sequential compilation. -/
theorem MeshBank.compile_eq_sequential {diameter : UniformRefinement.Coordinate} {depth : Nat} :
    {parents : List (OwnedCells.Cell safe)} → (bank : UniformRefinement.MeshBank diameter depth parents) →
      bank.compile = bank.sequentialCompile
  | _, .cons first (.cons second (.cons third (.cons fourth tail))) => by
      simp only [compile, Task.Parallel.four_eq, sequentialCompile, compile_eq_sequential tail, -eq_self, -iff_self]
      rfl
  | _, .nil => rfl
  | _, .cons _ .nil => rfl
  | _, .cons _ (.cons _ .nil) => rfl
  | _, .cons _ (.cons _ (.cons _ .nil)) => rfl

end

open Purelib.Integration.Algebraic.SquareFactor.PathContinuation
  Purelib.Integration.Algebraic.SquareFactor.UniformRefinement in
/-- Attempt child meshes sequentially for the original parents at the common diameter and depth.

Each original parent is attempted once in order at the supplied diameter and
depth. A failed attempt ends the traversal with the same original failure result. -/
@[expose] def sequentialMeshes (diameter : UniformRefinement.Coordinate) (positive : 0 < diameter) (depth : Nat) :
    (parents : List (OwnedCells.Cell safe)) → Option (UniformRefinement.MeshBank diameter depth parents)
  | [] => some .nil
  | parent :: parents => do
      let head ← ChildMeshes.tryBuild parent diameter positive depth first last (by decide)
      let tail ← sequentialMeshes diameter positive depth parents
      pure (.cons head tail)

open Purelib.Integration.Algebraic.SquareFactor.PathContinuation
  Purelib.Integration.Algebraic.SquareFactor.UniformRefinement in
open Purelib.Data in
set_option backward.match.sparseCases false in
/-- Attempt child meshes in groups of four parallel tasks, preserving the original parent order and exact failure
outcome. -/
@[expose] def tryMeshes (diameter : UniformRefinement.Coordinate) (positive : 0 < diameter) (depth : Nat) :
    (parents : List (OwnedCells.Cell safe)) → Option (UniformRefinement.MeshBank diameter depth parents)
  | one :: two :: three :: four :: parents =>
      let results := Task.Parallel.four
        (fun _ => ChildMeshes.tryBuild one diameter positive depth first last (by decide))
        (fun _ => ChildMeshes.tryBuild two diameter positive depth first last (by decide))
        (fun _ => ChildMeshes.tryBuild three diameter positive depth first last (by decide))
        (fun _ => ChildMeshes.tryBuild four diameter positive depth first last (by decide))
      match results with
      | (some firstMesh, some secondMesh, some thirdMesh, some fourthMesh) =>
          match Purelib.Integration.Algebraic.SquareFactor.UniformRefinement.tryMeshes diameter positive depth parents
            with
          | none => none
          | some tail => some (.cons firstMesh (.cons secondMesh (.cons thirdMesh (.cons fourthMesh tail))))
      | _ => none
  | parents => sequentialMeshes diameter positive depth parents

open Purelib.Integration.Algebraic.SquareFactor.PathContinuation
  Purelib.Integration.Algebraic.SquareFactor.UniformRefinement in
open Purelib.Data in
/-- Parallel child-mesh attempts equal the exact sequential attempts, including failure results. -/
theorem tryMeshes_eq_sequential (diameter : UniformRefinement.Coordinate) (positive : 0 < diameter) (depth : Nat) :
    ∀ parents : List (OwnedCells.Cell safe),
      UniformRefinement.tryMeshes diameter positive depth parents = sequentialMeshes diameter positive depth parents
  | one :: two :: three :: four :: parents => by
      simp only [UniformRefinement.tryMeshes, Task.Parallel.four_eq, sequentialMeshes]
      rw [Purelib.Integration.Algebraic.SquareFactor.UniformRefinement.tryMeshes_eq_sequential diameter positive depth
        parents]
      generalize ChildMeshes.tryBuild one diameter positive depth first last (by decide) = a
      generalize ChildMeshes.tryBuild two diameter positive depth first last (by decide) = b
      generalize ChildMeshes.tryBuild three diameter positive depth first last (by decide) = c
      generalize ChildMeshes.tryBuild four diameter positive depth first last (by decide) = d
      cases a <;> cases b <;> cases c <;> cases d <;>
        cases sequentialMeshes diameter positive depth parents <;> rfl
  | [] => rfl
  | [_] => rfl
  | [_, _] => rfl
  | [_, _, _] => rfl

/-- Construct the original mesh bank from a sufficient-depth certificate for every retained parent. -/
@[expose] def buildMeshes (diameter : UniformRefinement.Coordinate) (positive : 0 < diameter) (depth : Nat) :
    (parents : List (OwnedCells.Cell safe)) →
    (∀ parent ∈ parents, PreparedSheetContinuation.Subdivision.sufficientDyadicDepth
      (PathContinuation.clearSegment safe) parent.edge.left parent.edge.step.endpoint diameter ≤ depth) →
    UniformRefinement.MeshBank diameter depth parents
  | [], _ => .nil
  | parent :: parents, enough =>
      .cons (ChildMeshes.generateAtDepth parent diameter positive depth (enough parent (List.mem_cons_self ..)))
        (Purelib.Integration.Algebraic.SquareFactor.UniformRefinement.buildMeshes diameter positive depth parents
          (fun cell member => enough cell (List.mem_cons_of_mem _ member)))

set_option genInjectivity false in
/-- A retained common-depth mesh bank between the requested minimum and the derived sufficient maximum. -/
structure SelectedMeshes (parents : List (OwnedCells.Cell safe)) (diameter : UniformRefinement.Coordinate) (minimumDepth
  : Nat) where
  /-- The actual common selected additional mesh depth. -/ depth : Nat
  /-- The selected common depth meets the original minimum request. -/ minimum_le_depth : minimumDepth ≤ depth
  /-- The selected common depth is bounded by the original sufficient maximum. -/ depth_le_maximum : depth ≤
    UniformRefinement.maximumAdditionalDepth diameter minimumDepth parents
  /-- The original mesh bank at the exact retained common depth. -/ meshes : UniformRefinement.MeshBank diameter depth
    parents

constructive_injectivity SelectedMeshes

/-- Search successive common depths for the original parent mesh bank, stopping at the certified sufficient maximum.

Accepted attempts retain their exact meshes; the final sufficient depth constructs the certified meshes directly. -/
@[expose] def searchMeshes (parents : List (OwnedCells.Cell safe)) (diameter : UniformRefinement.Coordinate) (positive :
  0 < diameter)
    (minimumDepth depth : Nat) : (remaining : Nat) → minimumDepth ≤ depth →
      UniformRefinement.maximumAdditionalDepth diameter minimumDepth parents = depth + remaining →
      UniformRefinement.SelectedMeshes parents diameter minimumDepth
  | 0, minimum, upper =>
      { depth
        minimum_le_depth := minimum
        depth_le_maximum := by omega
        meshes := UniformRefinement.buildMeshes diameter positive depth parents (by
          intro parent member
          have bound := UniformRefinement.sufficient_le_maximumAdditionalDepth diameter minimumDepth parents parent
            member
          omega) }
  | remaining + 1, minimum, upper =>
      match UniformRefinement.tryMeshes diameter positive depth parents with
      | some meshes =>
          { depth
            minimum_le_depth := minimum
            depth_le_maximum := by omega
            meshes }
      | none => Purelib.Integration.Algebraic.SquareFactor.UniformRefinement.searchMeshes parents diameter positive
        minimumDepth (depth + 1)
          remaining (by omega) (by omega)

/-- Select a common mesh depth from the original minimum through the retained sufficient maximum. -/
@[expose] def selectMeshes (parents : List (OwnedCells.Cell safe)) (diameter : UniformRefinement.Coordinate) (positive :
  0 < diameter)
    (minimumDepth : Nat) : UniformRefinement.SelectedMeshes parents diameter minimumDepth :=
  UniformRefinement.searchMeshes parents diameter positive minimumDepth minimumDepth
    (UniformRefinement.maximumAdditionalDepth diameter minimumDepth parents - minimumDepth) le_rfl (by
      have bound := UniformRefinement.minimum_le_maximumAdditionalDepth diameter minimumDepth parents
      omega)

set_option genInjectivity false in
/-- Compiled child blocks sharing one selected depth with the original minimum and maximum bounds. -/
structure Synchronized (parents : List (OwnedCells.Cell safe)) (diameter : UniformRefinement.Coordinate) (minimumDepth :
  Nat) where
  /-- The actual common selected additional mesh depth. -/ depth : Nat
  /-- The selected common depth meets the original minimum request. -/ minimum_le_depth : minimumDepth ≤ depth
  /-- The selected common depth is bounded by the original sufficient maximum. -/ depth_le_maximum : depth ≤
    UniformRefinement.maximumAdditionalDepth diameter minimumDepth parents
  /-- The retained compiled child blocks indexed by the exact original parents and depth. -/ expansion :
    UniformRefinement.Expansion diameter depth parents

constructive_injectivity Synchronized

/-- Select the original mesh bank once and compile its retained meshes at their common depth. -/
@[expose] def synchronize (parents : List (OwnedCells.Cell safe)) (diameter : UniformRefinement.Coordinate) (positive :
  0 < diameter)
    (minimumDepth : Nat) : UniformRefinement.Synchronized parents diameter minimumDepth :=
  let selected := UniformRefinement.selectMeshes parents diameter positive minimumDepth
  ⟨selected.depth, selected.minimum_le_depth, selected.depth_le_maximum, selected.meshes.compile⟩

namespace Synchronized

variable {parents : List (Purelib.Integration.Algebraic.SquareFactor.OwnedCells.Cell safe)} {diameter :
  Purelib.Integration.Algebraic.SquareFactor.UniformRefinement.Coordinate} {minimumDepth : Nat}
  (result : Purelib.Integration.Algebraic.SquareFactor.UniformRefinement.Synchronized parents diameter minimumDepth)

/-- The retained expansion has the original parent count times two to the common additional depth cells. -/
theorem count : result.expansion.cells.length = parents.length * 2 ^ result.depth :=
  result.expansion.count

open Purelib.Approximation.Rational in
/-- Uniform original parent widths give child widths at the sum of the retained depths. -/
theorem widths (parentDepth : Nat)
    (parentWidths : ∀ parent ∈ parents,
      parent.edge.span.width ^ 2 = Geometric.Basic.quarterRadius 1 parentDepth) :
    ∀ child ∈ result.expansion.cells, child.edge.span.width ^ 2 =
      Geometric.Basic.quarterRadius 1 (parentDepth + result.depth) :=
  result.expansion.widths parentDepth parentWidths

end Synchronized

open Purelib.Approximation.Rational in
open Purelib.Integration.Polynomial.Gaussian.Path in
set_option genInjectivity false in
/-- A target-indexed refinement retaining the resolution, synchronized expansion, cached cells, model and explicit
allowance.

The cache equations tie all readbacks to the same original parent expansion, with its certified uniform parent widths.
-/
structure Refined (parentDepth : Nat) (parents : List (OwnedCells.Cell safe)) (target : UniformRefinement.Coordinate)
  where
  /-- Every original parent has the certified squared width at the retained parent depth. -/ parentWidths : ∀ parent ∈
    parents,
    parent.edge.span.width ^ 2 = Geometric.Basic.quarterRadius 1 parentDepth
  /-- The exact target resolution using unit weight and the original path data. -/ resolution : Accuracy.Resolution data
    1 target
  /-- The retained common-depth expansion for the exact resolved diameter and additional minimum. -/ synchronized :
    UniformRefinement.Synchronized parents resolution.rootDiameter (resolution.minimumDepth - parentDepth)
  /-- The cached ordered compiled child cells. -/ cells : List (OwnedCells.Cell safe)
  /-- The cached child cells equal the exact retained expansion's cell readback. -/ cells_eq : cells =
    synchronized.expansion.cells
  /-- The cached child path model. -/ model : Basic.PathModel
  /-- The cached model cells equal the exact retained expansion's model readback. -/ model_eq : model.cells =
    synchronized.expansion.models
  /-- The cached explicit local allowance for the retained refinement. -/ allowance : UniformRefinement.Coordinate
  /-- The cached allowance is the exact sum of retained parameter and root contributions. -/ allowance_eq : allowance =
    CoefficientBounds.parameterSlope data * Geometric.Basic.quarterRadius 1 (parentDepth + synchronized.depth) +
    CoefficientBounds.rootSlope data * resolution.rootDiameter

constructive_injectivity Refined

open Purelib.Approximation.Rational in
/-- Resolve the target, synchronize the original parent meshes and cache their exact cells, model and allowance.

The additional minimum depth accounts for the original parent depth; all cached readbacks retain their defining
equations. -/
@[expose] def refine (parentDepth : Nat) (parents : List (OwnedCells.Cell safe))
    (parentWidths : ∀ parent ∈ parents,
      parent.edge.span.width ^ 2 = Geometric.Basic.quarterRadius 1 parentDepth)
    (target : UniformRefinement.Coordinate) (positive : 0 < target) : UniformRefinement.Refined parentDepth parents
      target :=
  let resolution := Accuracy.resolve safe 1 (by decide) target positive
  let synchronized := UniformRefinement.synchronize parents resolution.rootDiameter resolution.rootDiameterPositive
    (resolution.minimumDepth - parentDepth)
  { parentWidths, resolution, synchronized
    cells := synchronized.expansion.cells
    cells_eq := rfl
    model := ⟨synchronized.expansion.models⟩
    model_eq := rfl
    allowance := CoefficientBounds.parameterSlope data * Geometric.Basic.quarterRadius 1 (parentDepth +
      synchronized.depth) +
      CoefficientBounds.rootSlope data * resolution.rootDiameter
    allowance_eq := rfl }

section
open Purelib.Integration.Polynomial.Gaussian.Cell
open Purelib.Integration.Polynomial.Gaussian.Path
/-- Transport a compatible refinement along equality of the exact child list. -/
@[expose] def castChildren {parents children otherChildren : List Basic.CellModel}
    (certificate : Basic.PathModel.CompatibleConstantPathRefinement parents children)
    (equal : children = otherChildren) : Basic.PathModel.CompatibleConstantPathRefinement parents otherChildren := by
  cases equal
  exact certificate

/-- Transporting the child-list index preserves the exact comparison allowance. -/
private theorem castChildren_comparisonAllowance {parents children otherChildren : List Basic.CellModel}
    (certificate : Basic.PathModel.CompatibleConstantPathRefinement parents children) (equal : children = otherChildren)
      :
    (CompatibleRefinement.PathModel.CompatibleConstantPathRefinement.comparisonAllowance (UniformRefinement.castChildren
      certificate equal)) = (CompatibleRefinement.PathModel.CompatibleConstantPathRefinement.comparisonAllowance
      certificate) := by
  cases equal
  rfl

end

namespace Refined

variable {parentDepth : Nat} {parents : List (Purelib.Integration.Algebraic.SquareFactor.OwnedCells.Cell safe)} {target
  : Purelib.Integration.Algebraic.SquareFactor.UniformRefinement.Coordinate}
  (result : Purelib.Integration.Algebraic.SquareFactor.UniformRefinement.Refined parentDepth parents target)

/-- The total original-plus-selected depth meets the retained accuracy resolution's minimum. -/
theorem numericalDepth_le : result.resolution.minimumDepth ≤ parentDepth + result.synchronized.depth := by
  have enough := result.synchronized.minimum_le_depth
  omega

/-- The retained model cells equal the exact readback of the retained compiled cells. -/
theorem model_cells : result.model.cells = result.cells.map (fun cell => cell.model.cell) := by
  rw [result.model_eq, result.synchronized.expansion.models_eq, result.cells_eq]

section
open Purelib.Integration.Polynomial.Gaussian.Path
/-- Read the compatible refinement to the cached model using its exact expansion model equation. -/
@[expose] def refinement : Basic.PathModel.CompatibleConstantPathRefinement
    (parents.map (fun cell => cell.model.cell)) result.model.cells :=
  UniformRefinement.castChildren result.synchronized.expansion.refinement result.model_eq.symm

/-- The cached refinement has the exact comparison allowance of its retained synchronized expansion. -/
theorem comparisonAllowance_eq :
    (CompatibleRefinement.PathModel.CompatibleConstantPathRefinement.comparisonAllowance result.refinement) =
      (CompatibleRefinement.PathModel.CompatibleConstantPathRefinement.comparisonAllowance
      result.synchronized.expansion.refinement) :=
  UniformRefinement.castChildren_comparisonAllowance _ _

end

open Purelib.Data.Rat in
/-- The retained explicit local allowance is strictly below the original positive target. -/
theorem allowance_lt (positive : 0 < target) : result.allowance < target := by
  rw [result.allowance_eq]
  have bound := result.resolution.model_bound_lt safe positive (parentDepth + result.synchronized.depth)
    result.numericalDepth_le
  simpa only [Fraction.Field.one_mul] using bound

/-- Every retained compiled child cell meets the cached explicit local allowance. -/
theorem cells_allowance_le : ∀ cell ∈ result.cells, cell.model.cell.localAllowance ≤ result.allowance := by
  rw [result.cells_eq, result.allowance_eq]
  exact result.synchronized.expansion.local_allowance_le parentDepth result.parentWidths

end Refined

end Purelib.Integration.Algebraic.SquareFactor.UniformRefinement
