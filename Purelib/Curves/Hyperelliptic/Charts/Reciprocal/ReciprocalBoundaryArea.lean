module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.List.Membership
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.DyadicCount
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.Dyadic.DyadicBoundaryRibbon
import Purelib.Integration.Path.IncrementArea
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.UniformPrimitiveMesh
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPrimitiveRibbon
import Purelib.Integration.Path.IncrementAreaComparison
public import Purelib.Integration.Path.Dyadic.DyadicPrimitivePaths
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Riemann.Normalization.OwnerSeededInverseRoot
import Purelib.Tactic.Ring

open Purelib.Data.Rat.Fraction.Order

open Purelib.Data.Gaussian.Norm

public section

open Purelib
open Purelib.Approximation.Rational
open Purelib.Approximation.Rational.Geometric
open Purelib.Approximation.Rational.Geometric.Basic
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives
open Purelib.Data.Rat
open Purelib.Integration.Path
open Purelib.Integration.Path.Dyadic
open Purelib.Riemann.Meshes
open Purelib.Riemann.Normalization
open Purelib.Riemann.Branches

/-!
# Complete reciprocal primitive paths with all area cross-terms

Each reciprocal cell retains its literal fine increment path and a cached
total/area summary. Concatenation preserves the internal areas and the full
polygon of block totals. Both counts cancel against the exact dyadic widths.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalBoundaryArea

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels (Data)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover (Cell Mesh Cover ParentCovers)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives (SourcePrimitive CellPrimitive
  PrimitiveCells)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Riemann.Meshes.UniformPrimitiveMesh (firstEndpoint)
open Purelib.Riemann.Meshes.UniformPrimitiveMesh (lastEndpoint)
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision (ParameterEdge)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Data.Gaussian.Basic.Canonical
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Integration.Path.IncrementArea (Summary pathArea)
open Purelib.Integration.Path.Dyadic.DyadicBoundaryRibbon (dyadicArea)
open Purelib.Integration.Path.Dyadic.DyadicPrimitivePaths (dyadicIncrements dyadicIncrements_sum)
open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius quarterRadius_nonneg quarterRadius_eq_mul_pow)

variable {genus count index depth : Nat} {curve : HyperellipticCurve genus}
  {differential : Differential genus}
  {parent : CenteredEdge curve differential} {patch :
    PreparedPatch parent} {data :
    Data patch count}

namespace Data

/-- The pre-refinement scale paying both retained local primitive areas and all cross terms between cell totals. -/
@[expose] def boundaryAreaScale (data : Data patch count) : Coordinate :=
  2 * data.areaScale + 64 * (Data.errorScale data) * (data.sourceSlope +
    (Data.errorScale data))

/-- The complete reciprocal boundary-area error scale is nonnegative. -/
theorem boundaryAreaScale_nonnegative (data : Data patch count) : 0 ≤
  (boundaryAreaScale data) :=
  add_nonneg (Arithmetic.mul_nonneg_direct (by decide) data.areaScale_nonnegative)
    (Arithmetic.mul_nonneg_direct
      (Arithmetic.mul_nonneg_direct (by decide +kernel)
        (Data.errorScale_nonnegative data))
      (add_nonneg data.sourceSlope_nonnegative (Data.errorScale_nonnegative data)))

end Data

set_option genInjectivity false in
/-- The original source and reciprocal finite increment paths with their cached area and total summaries.

Both paths retain exact dyadic readbacks at the same spatial depth and original parameter edge. -/
structure CellArea (source : SourcePrimitive data index) (depth : Nat) (edge :
  ParameterEdge) where
  /-- The retained original reciprocal primitive or composed reciprocal path summary. -/ right :
    CellPrimitive data index edge
  /-- The cached original source primitive increment path on this cell. -/ leftPath : List
    Gaussian
  /-- The source path is exactly the original primitive's dyadic increment list at the retained spatial depth. -/
    leftPath_eq : leftPath = dyadicIncrements (fun parameter => source.primitive.value.eval
    (parent.edge.point parameter))
    depth edge.left.parameter edge.right.parameter
  /-- The cached original reciprocal primitive increment path on this cell. -/ rightPath : List
    Gaussian
  /-- The reciprocal path is exactly the retained reciprocal primitive's dyadic increments on the original endpoints. -/
    rightPath_eq : rightPath = dyadicIncrements right.reciprocalValue depth edge.left.parameter
    edge.right.parameter
  /-- The cached total and area summary of the exact original source increment path. -/ left : Summary
    leftPath
  /-- The cached total and area summary of the exact retained reciprocal increment path. -/ reciprocal :
    Summary rightPath

constructive_injectivity CellArea

namespace CellArea

variable {source : SourcePrimitive data
  index} {edge : ParameterEdge}

/-- Cache the original source and reciprocal dyadic increment paths and their exact finite summaries. -/
@[expose] def build (source : SourcePrimitive data index) (right :
  CellPrimitive data index edge) (depth : Nat) :
  CellArea source depth edge :=
  let leftPath := dyadicIncrements (fun parameter => source.primitive.value.eval (parent.edge.point
    parameter))
    depth edge.left.parameter edge.right.parameter
  let rightPath := dyadicIncrements right.reciprocalValue depth edge.left.parameter
    edge.right.parameter
  ⟨right, leftPath, rfl, rightPath, rfl, Summary.build leftPath, Summary.build rightPath⟩

/-- The cached original source-path total is the retained source primitive's exact cell increment. -/
theorem left_total (cell : CellArea source depth edge) :
  cell.left.total = source.increment edge := by
  rw [cell.left.total_eq, cell.leftPath_eq, dyadicIncrements_sum]
  rfl

/-- The cached reciprocal-path total is the original retained reciprocal primitive increment. -/
theorem right_total (cell : CellArea source depth edge) :
  cell.reciprocal.total = cell.right.increment := by
  rw [cell.reciprocal.total_eq, cell.rightPath_eq, dyadicIncrements_sum,
    cell.right.reciprocalValue_left, Data.Gaussian.Basic.sub_zero, cell.right.increment_eq]
  rfl

/-- The cached source-path area equals the original anchored primitive's finite dyadic area. -/
theorem left_area (cell : CellArea source depth edge) :
  cell.left.area =
    dyadicArea (CellPrimitive.sourceValue source edge) depth edge.left.parameter
      edge.right.parameter := by
  rw [cell.left.area_eq, cell.leftPath_eq,
    ← DyadicPrimitivePaths.dyadicIncrements_sub_constant _ (source.primitive.value.eval (parent.edge.point
      edge.left.parameter))]
  exact DyadicPrimitivePaths.pathArea_dyadicIncrements _ _ _ _ (CellPrimitive.sourceValue_left source)

/-- The cached reciprocal-path area equals the original anchored reciprocal primitive's finite dyadic area. -/
theorem right_area (cell : CellArea source depth edge) :
  cell.reciprocal.area =
    dyadicArea cell.right.reciprocalValue depth edge.left.parameter edge.right.parameter := by
  rw [cell.reciprocal.area_eq, cell.rightPath_eq]
  exact DyadicPrimitivePaths.pathArea_dyadicIncrements _ _ _ _ cell.right.reciprocalValue_left

/-- The two original cached cell areas satisfy the geometric area bound times fourth-power cell width. -/
theorem area_error (cell : CellArea source depth edge) :
    Basic.normSq (cell.left.area - cell.reciprocal.area) ≤
      quarterRadius data.areaScale index * (edge.right.parameter - edge.left.parameter) ^ 4 := by
  rw [cell.left_area, cell.right_area]
  exact cell.right.area_error_geometric source depth

/-- The original cached cell totals satisfy the primitive discrepancy bound times squared cell width. -/
theorem total_error (cell : CellArea source depth edge) :
    Basic.normSq (cell.left.total - cell.reciprocal.total) ≤
      quarterRadius (Data.errorScale data) index * (edge.right.parameter -
        edge.left.parameter) ^ 2 := by
  rw [cell.left_total, cell.right_total]
  exact cell.right.increment_error source

/-- The original source-path total satisfies the retained slope ceiling times squared cell width. -/
theorem left_bound (cell : CellArea source depth edge) :
    Basic.normSq cell.left.total ≤ data.sourceSlope * (edge.right.parameter -
      edge.left.parameter) ^ 2 := by
  rw [cell.left_total]
  exact source.increment_bound edge.left.inside edge.right.inside

/-- The reciprocal-path total satisfies the original source slope and geometric discrepancy ceiling. -/
theorem right_bound (cell : CellArea source depth edge) :
    Basic.normSq cell.reciprocal.total ≤ 2 * (data.sourceSlope +
      quarterRadius (Data.errorScale data) index) *
      (edge.right.parameter - edge.left.parameter) ^ 2 := by
  rw [cell.right_total, cell.right.increment_eq]
  have estimate := cell.right.reciprocal_increment_bound source
    ⟨le_rfl, cell.right.cell.ordered.le⟩ ⟨cell.right.cell.ordered.le, le_rfl⟩
  rw [cell.right.reciprocalValue_left, Data.Gaussian.Basic.sub_zero] at estimate
  exact estimate

end CellArea

set_option genInjectivity false in
/-- Paired finite path and summary caches indexed by the original reciprocal edge spine.

Every occurrence retains its own primitive while sharing the original source primitive and spatial depth. -/
inductive AreaCells (source : SourcePrimitive data index) (depth : Nat) : List
  ParameterEdge → Type
  /-- The empty original edge list retains no paired path caches. -/ | nil :
    AreaCells source depth []
  /-- Retain the original head edge's path caches followed by the matching original tail. -/ | cons {edge :
    ParameterEdge} {remaining : List
    ParameterEdge}
      (head : CellArea source depth edge) (tail :
        AreaCells source depth remaining) :
        AreaCells source depth (edge :: remaining)

constructive_injectivity AreaCells

namespace AreaCells

variable {source : SourcePrimitive data
  index}

/-- Cache paired path summaries along the original retained primitive-cell spine without replacing its primitives. -/
@[expose] def build (source : SourcePrimitive data index) (depth : Nat) : {edges : List
  ParameterEdge} →
    PrimitiveCells data index edges →
      AreaCells source depth edges
  | _, .nil => .nil
  | _, .cons head tail => .cons (CellArea.build source
    head depth) (build source depth
    tail)

/-- Read the original source and reciprocal increment-path pairs in retained cell order. -/
@[expose] def pairs : {edges : List ParameterEdge} →
  AreaCells source depth edges → List (List
  Gaussian × List Gaussian)
  | _, .nil => []
  | _, .cons head tail => (head.leftPath, head.rightPath) :: tail.pairs

/-- There is exactly one retained path pair per original parameter edge. -/
theorem pairs_length {edges : List ParameterEdge} (cells :
  AreaCells source depth edges) : cells.pairs.length =
  edges.length := by
  induction cells with
  | nil => rfl
  | cons _ _ ih => exact congrArg Nat.succ ih

/-- Compose the cached block summaries; do not replay the fine path to obtain its aggregate total or area. -/
@[expose] def leftSummary : {edges : List ParameterEdge} → (cells :
  AreaCells source depth edges) → Summary
  (cells.pairs.map Prod.fst).flatten
  | _, .nil => Summary.build []
  | _, .cons head tail => head.left.append tail.leftSummary

/-- Compose the cached reciprocal block summaries without replaying their original fine increment paths. -/
@[expose] def rightSummary : {edges : List ParameterEdge} → (cells :
  AreaCells source depth edges) → Summary
  (cells.pairs.map Prod.snd).flatten
  | _, .nil => Summary.build []
  | _, .cons head tail => head.reciprocal.append tail.rightSummary

/-- The retained source paths are exactly the original edgewise dyadic increments of the shared source primitive. -/
theorem left_paths {edges : List ParameterEdge} (cells :
  AreaCells source depth edges) :
    cells.pairs.map Prod.fst = edges.map (fun edge => dyadicIncrements
      (fun parameter => source.primitive.value.eval (parent.edge.point parameter)) depth edge.left.parameter
        edge.right.parameter) := by
  induction cells with
  | nil => rfl
  | cons head tail ih =>
      change head.leftPath :: tail.pairs.map Prod.fst = _
      rw [head.leftPath_eq, ih]
      rfl

/-- The retained source summary reads the original whole-parent dyadic area at the combined coarse and fine depth. -/
theorem source_area (mesh : Mesh data) (cells :
  AreaCells source depth mesh.edges) :
    cells.leftSummary.area = dyadicArea
      (fun parameter => source.primitive.value.eval (parent.edge.point parameter) - source.primitive.value.eval
        (parent.edge.point 0))
      (mesh.depth + depth) 0 1 := by
  rw [cells.leftSummary.area_eq, cells.left_paths, mesh.edges_eq, DyadicPrimitivePaths.dyadicEdges_flatten_increments,
    ← DyadicPrimitivePaths.dyadicIncrements_sub_constant _ (source.primitive.value.eval (parent.edge.point 0))]
  exact DyadicPrimitivePaths.pathArea_dyadicIncrements _ _ _ _ (_root_.sub_self _)

/-- The retained source summary total is the exact original parent endpoint difference. -/
theorem source_total (mesh : Mesh data) (cells :
  AreaCells source depth mesh.edges) :
    cells.leftSummary.total = source.primitive.value.eval (parent.edge.point 1) - source.primitive.value.eval
      (parent.edge.point 0) := by
  rw [cells.leftSummary.total_eq, cells.left_paths, mesh.edges_eq, DyadicPrimitivePaths.dyadicEdges_flatten_increments,
    dyadicIncrements_sum]
  rfl

/-- The full area trace has precisely the already cached reciprocal integral. This readback prevents a later area
consumer from changing paths. -/
theorem build_right_total (source : SourcePrimitive data index) (depth : Nat) {edges : List
  ParameterEdge}
    (primitives : PrimitiveCells data index edges) :
    (build source depth
      primitives).rightSummary.total = gaussianSum primitives.values := by
  induction primitives with
  | nil => rfl
  | cons head tail ih =>
      change (CellArea.build source head
        depth).reciprocal.total + (build source
        depth tail).rightSummary.total =
        head.increment + gaussianSum tail.values
      rw [(CellArea.build source head depth).right_total,
        ih]
      rfl

/-- Every retained original path pair satisfies the common dyadic area, total-discrepancy and total-size bounds. -/
private theorem bounds (mesh : Mesh data) {edges : List
  ParameterEdge} (cells :
  AreaCells source depth edges)
    (members : ∀ edge ∈ edges, edge ∈ mesh.edges) :
    ∀ pair ∈ cells.pairs,
      Basic.normSq (pathArea pair.1 - pathArea pair.2) ≤
        quarterRadius data.areaScale index * (quarterRadius 1 mesh.depth) ^ 2 ∧
      Basic.normSq (gaussianSum pair.1 -
        gaussianSum pair.2) ≤ quarterRadius
        (Data.errorScale data) index * quarterRadius 1 mesh.depth ∧
      Basic.normSq (gaussianSum pair.1) ≤ 2 *
        (data.sourceSlope + quarterRadius (Data.errorScale data) index) *
        quarterRadius 1 mesh.depth ∧
      Basic.normSq (gaussianSum pair.2) ≤ 2 *
        (data.sourceSlope + quarterRadius (Data.errorScale data) index) *
        quarterRadius 1 mesh.depth := by
  induction cells with
  | nil => intro _ member; exact False.elim (List.not_mem_nil member)
  | @cons edge remaining head tail ih =>
      intro pair member
      rcases Data.List.Membership.mem_cons.mp member with same | member
      · subst pair
        have width := UniformPrimitiveMesh.dyadicEdges_width mesh.depth firstEndpoint
          lastEndpoint edge
          (mesh.edges_eq ▸ members edge (List.mem_cons_self ..))
        have unit : (UniformPrimitiveMesh.lastEndpoint.parameter - UniformPrimitiveMesh.firstEndpoint.parameter) ^ 2 =
          (1 : Coordinate) := by decide
        rw [unit] at width
        change Basic.normSq (pathArea head.leftPath - pathArea
          head.rightPath) ≤ _ ∧
          Basic.normSq (gaussianSum head.leftPath -
            gaussianSum head.rightPath) ≤ _ ∧
          Basic.normSq (gaussianSum head.leftPath) ≤ _ ∧
            Basic.normSq (gaussianSum head.rightPath) ≤ _
        rw [← head.left.area_eq, ← head.reciprocal.area_eq, ← head.left.total_eq, ← head.reciprocal.total_eq]
        refine ⟨head.area_error.trans_eq ?_, head.total_error.trans_eq (by rw [width]), ?_,
          head.right_bound.trans_eq (by rw [width])⟩
        · rw [show (edge.right.parameter - edge.left.parameter) ^ 4 = ((edge.right.parameter - edge.left.parameter) ^ 2)
            ^ 2 by ring1, width]
        · have slopeLe : data.sourceSlope ≤ 2 * (data.sourceSlope + quarterRadius
            (Data.errorScale data) index) := by
            have errorNonnegative := quarterRadius_nonneg
              (Data.errorScale_nonnegative data) index
            exact (le_add_of_nonneg_right errorNonnegative).trans
              ((le_add_of_nonneg_right (add_nonneg data.sourceSlope_nonnegative errorNonnegative)).trans_eq (by ring1))
          exact head.left_bound.trans
            ((Arithmetic.mul_le_mul_of_nonneg_right_direct slopeLe
              (Arithmetic.sq_nonneg_direct _)).trans_eq (by rw [width]))
      · exact ih (fun other found => members other (List.mem_cons_of_mem _ found)) pair member

/-- The whole literal reciprocal path pays internal area errors AND the polygon of block totals. No fine depth or coarse
cell count is hidden. -/
theorem whole_area_bound (mesh : Mesh data) (cells :
  AreaCells source depth mesh.edges) :
    Basic.normSq (cells.leftSummary.area - cells.rightSummary.area) ≤
      2 * (quarterRadius data.areaScale index * quarterRadius 1 mesh.depth +
        32 * quarterRadius (Data.errorScale data) index * (data.sourceSlope
          + quarterRadius (Data.errorScale data) index)) := by
  rw [cells.leftSummary.area_eq, cells.rightSummary.area_eq]
  have bounded := cells.bounds mesh (fun _ member => member)
  have estimate := IncrementAreaComparison.blocks_area_difference_bound cells.pairs
    (Arithmetic.mul_nonneg_direct (quarterRadius_nonneg
      (Data.errorScale_nonnegative data) index)
      (quarterRadius_nonneg (by decide) mesh.depth))
    (Arithmetic.mul_nonneg_direct
      (Arithmetic.mul_nonneg_direct (by decide)
        (add_nonneg data.sourceSlope_nonnegative (quarterRadius_nonneg
          (Data.errorScale_nonnegative data) index)))
      (quarterRadius_nonneg (by decide) mesh.depth))
    (fun pair member => (bounded pair member).1) (fun pair member => (bounded pair member).2.1)
    (fun pair member => (bounded pair member).2.2.1) (fun pair member => (bounded pair member).2.2.2)
  rw [cells.pairs_length] at estimate
  have countWidth : (mesh.edges.length : Coordinate) ^ 2 * quarterRadius 1
    mesh.depth = 1 := by
    rw [mesh.edges_length, mesh.edgeCount_eq]
    exact (by ring1 : (((2 ^ mesh.depth : Nat) : Coordinate) ^ 2 * quarterRadius 1
      mesh.depth) =
      ((2 ^ mesh.depth : Nat) : Coordinate) * (((2 ^ mesh.depth : Nat) :
        Coordinate) * quarterRadius 1 mesh.depth)).trans
      (DyadicCount.dyadic_count_cancel 1 mesh.depth)
  apply estimate.trans_eq
  calc
    _ = 2 * (quarterRadius data.areaScale index * quarterRadius 1 mesh.depth *
        ((mesh.edges.length : Coordinate) ^ 2 * quarterRadius 1 mesh.depth) +
        32 * quarterRadius (Data.errorScale data) index * (data.sourceSlope
          + quarterRadius (Data.errorScale data) index) *
          ((mesh.edges.length : Coordinate) ^ 2 * quarterRadius 1 mesh.depth) ^ 2)
            := by ring1
    _ = _ := by rw [countWidth]; ring1

/-- A single pre-index scale pays the entire concatenated path area at every fine spatial depth. The geometric rate has
no count-dependent floor. -/
theorem whole_area_error (mesh : Mesh data) (cells :
  AreaCells source depth mesh.edges) :
    Basic.normSq (cells.leftSummary.area - cells.rightSummary.area) ≤
      quarterRadius
      (Data.boundaryAreaScale data) index := by
  have errorLe : quarterRadius (Data.errorScale data) index ≤
    (Data.errorScale data) := by
    simpa only [quarterRadius_eq_mul_pow, pow_zero, Fraction.Field.mul_one_direct, -eq_self, -iff_self]
      using
      quarterRadius_antitone (Data.errorScale_nonnegative data) (Nat.zero_le
        index)
  have widthLe : quarterRadius (1 : Coordinate) mesh.depth ≤ 1 := by
    simpa only [quarterRadius_eq_mul_pow, pow_zero, Fraction.Field.mul_one_direct, -eq_self, -iff_self]
      using
      quarterRadius_antitone (by decide : (0 : Coordinate) ≤ 1) (Nat.zero_le mesh.depth)
  have fineBound : quarterRadius data.areaScale index * quarterRadius 1 mesh.depth ≤
    quarterRadius data.areaScale index := by
    simpa only [Fraction.Field.mul_one_direct, -eq_self, -iff_self] using
      Arithmetic.mul_le_mul_of_nonneg_left_direct widthLe (quarterRadius_nonneg
        data.areaScale_nonnegative index)
  have coarseBound : 32 * quarterRadius (Data.errorScale data) index *
    (data.sourceSlope + quarterRadius (Data.errorScale data) index) ≤
      32 * quarterRadius (Data.errorScale data) index * (data.sourceSlope +
        (Data.errorScale data)) :=
    Arithmetic.mul_le_mul_of_nonneg_left_direct (add_le_add le_rfl errorLe)
      (Arithmetic.mul_nonneg_direct (by decide +kernel) (quarterRadius_nonneg
        (Data.errorScale_nonnegative data) index))
  exact (cells.whole_area_bound mesh).trans
    ((Arithmetic.mul_le_mul_of_nonneg_left_direct (add_le_add fineBound coarseBound) (by
      decide)).trans_eq (by
      simp only [quarterRadius_eq_mul_pow,
        Data.boundaryAreaScale, -eq_self, -iff_self]
      ring1))

end AreaCells

namespace Cover

set_option genInjectivity false in
/-- A requested complete reciprocal path-area comparison on the original cover.

The retained source primitive, fine cell paths and composed summaries share one polynomial stage with its exact paid
geometric error. -/
structure AreaRequest (cover : Cover data) (depth : Nat) (target :
  Coordinate) where
  /-- The shared original polynomial refinement stage. -/ index : Nat
  /-- The original source primitive shared by all retained reciprocal cells. -/ source :
    SourcePrimitive data index
  /-- The original finite edge-indexed bank of paired paths and cached summaries. -/ cells :
    AreaCells source depth cover.mesh.edges
  /-- The cached total and area summary of the exact original source increment path. -/ left : Summary
    (cells.pairs.map Prod.fst).flatten
  /-- The composed summary of the exact concatenated original reciprocal cell paths. -/ right : Summary
    (cells.pairs.map Prod.snd).flatten
  /-- The cached squared-norm ceiling for the complete source-minus-reciprocal area discrepancy. -/ error :
    Coordinate
  /-- The cached error is the full boundary-area scale's geometric quarter-radius at the retained polynomial stage. -/
    error_eq : error = quarterRadius
    (Data.boundaryAreaScale data) index
  /-- The cached complete area error is strictly below the requested target. -/ error_lt : error < target
  /-- The exact retained source and reciprocal summary areas satisfy the cached discrepancy bound. -/ close :
    Basic.normSq (left.area - right.area) ≤ error

constructive_injectivity AreaRequest

/-- Reuse a primitive bank already shared with the prepared integrator and grid. Its summaries are composed from cached
fine-block totals and areas. -/
@[expose] def AreaRequest.ofPrimitives (cover : Cover data) (source :
  SourcePrimitive data index)
    (primitives : PrimitiveCells data index cover.mesh.edges) (depth : Nat) (target :
      Coordinate)
    (accurate : quarterRadius
      (Data.boundaryAreaScale data) index < target) :
      AreaRequest cover depth target :=
  let cells := AreaCells.build source depth primitives
  ⟨index, source, cells, cells.leftSummary, cells.rightSummary, quarterRadius
    (Data.boundaryAreaScale data) index, rfl,
    accurate, cells.whole_area_error cover.mesh⟩

/-- Select a common polynomial stage paying the area target and cache the original source and reciprocal path summaries.
-/
@[expose] def areaRequest (cover : Cover data) (depth : Nat) (target :
  Coordinate) (positive : 0 < target) :
  AreaRequest cover depth target :=
  let index := Search.firstQuarterBelow
    (Data.boundaryAreaScale data) 0 target
  let source := SourcePrimitive.build data index
  let primitives := PrimitiveCells.build index cover.cells
  AreaRequest.ofPrimitives cover source primitives
    depth target
    (Search.firstQuarterBelow_accurate _
      (Data.boundaryAreaScale_nonnegative data) 0 _
      positive)

/-- The retained source summary reads the original whole-parent dyadic area at the combined coarse and fine depth. -/
theorem AreaRequest.source_area {cover : Cover data} {target : Coordinate}
  (request : AreaRequest cover depth target) :
    request.left.area = dyadicArea
      (fun parameter => request.source.primitive.value.eval (parent.edge.point parameter) -
        request.source.primitive.value.eval (parent.edge.point 0))
      (cover.mesh.depth + depth) 0 1 := by
  rw [request.left.area_eq, ← request.cells.leftSummary.area_eq]
  exact request.cells.source_area cover.mesh

/-- The retained source summary total is the exact original parent endpoint difference. -/
theorem AreaRequest.source_total {cover : Cover data} {target : Coordinate}
  (request : AreaRequest cover depth target) :
    request.left.total = request.source.primitive.value.eval (parent.edge.point 1) - request.source.primitive.value.eval
      (parent.edge.point 0) := by
  rw [request.left.total_eq, ← request.cells.leftSummary.total_eq]
  exact request.cells.source_total cover.mesh

end Cover
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalBoundaryArea
