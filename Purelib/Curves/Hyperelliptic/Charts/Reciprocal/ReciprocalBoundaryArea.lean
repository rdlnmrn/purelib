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
@[expose] def boundaryAreaScale (data : UniformReciprocalModels.Data patch count) : Coordinate :=
  2 * data.areaScale + 64 * (UniformReciprocalPrimitives.Data.errorScale data) * (data.sourceSlope +
    (UniformReciprocalPrimitives.Data.errorScale data))

/-- The complete reciprocal boundary-area error scale is nonnegative. -/
theorem boundaryAreaScale_nonnegative (data : UniformReciprocalModels.Data patch count) : 0 ≤
  (boundaryAreaScale data) :=
  add_nonneg (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) data.areaScale_nonnegative)
    (Fraction.Order.Arithmetic.mul_nonneg_direct
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel)
        (UniformReciprocalPrimitives.Data.errorScale_nonnegative data))
      (add_nonneg data.sourceSlope_nonnegative (UniformReciprocalPrimitives.Data.errorScale_nonnegative data)))

end Data

set_option genInjectivity false in
/-- The original source and reciprocal finite increment paths with their cached area and total summaries.

Both paths retain exact dyadic readbacks at the same spatial depth and original parameter edge. -/
structure CellArea (source : UniformReciprocalPrimitives.SourcePrimitive data index) (depth : Nat) (edge :
  ClearSheetContinuation.Subdivision.ParameterEdge) where
  /-- The retained original reciprocal primitive or composed reciprocal path summary. -/ right :
    UniformReciprocalPrimitives.CellPrimitive data index edge
  /-- The cached original source primitive increment path on this cell. -/ leftPath : List
    InverseRootPolynomial.Gaussian
  /-- The source path is exactly the original primitive's dyadic increment list at the retained spatial depth. -/
    leftPath_eq : leftPath = DyadicPrimitivePaths.dyadicIncrements (fun parameter => source.primitive.value.eval
    (parent.edge.point parameter))
    depth edge.left.parameter edge.right.parameter
  /-- The cached original reciprocal primitive increment path on this cell. -/ rightPath : List
    InverseRootPolynomial.Gaussian
  /-- The reciprocal path is exactly the retained reciprocal primitive's dyadic increments on the original endpoints. -/
    rightPath_eq : rightPath = DyadicPrimitivePaths.dyadicIncrements right.reciprocalValue depth edge.left.parameter
    edge.right.parameter
  /-- The cached total and area summary of the exact original source increment path. -/ left : IncrementArea.Summary
    leftPath
  /-- The cached total and area summary of the exact retained reciprocal increment path. -/ reciprocal :
    IncrementArea.Summary rightPath

constructive_injectivity CellArea

namespace CellArea

variable {source : SourcePrimitive data
  index} {edge : ParameterEdge}

/-- Cache the original source and reciprocal dyadic increment paths and their exact finite summaries. -/
@[expose] def build (source : UniformReciprocalPrimitives.SourcePrimitive data index) (right :
  UniformReciprocalPrimitives.CellPrimitive data index edge) (depth : Nat) :
  Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalBoundaryArea.CellArea source depth edge :=
  let leftPath := DyadicPrimitivePaths.dyadicIncrements (fun parameter => source.primitive.value.eval (parent.edge.point
    parameter))
    depth edge.left.parameter edge.right.parameter
  let rightPath := DyadicPrimitivePaths.dyadicIncrements right.reciprocalValue depth edge.left.parameter
    edge.right.parameter
  ⟨right, leftPath, rfl, rightPath, rfl, IncrementArea.Summary.build leftPath, IncrementArea.Summary.build rightPath⟩

/-- The cached original source-path total is the retained source primitive's exact cell increment. -/
theorem left_total (cell : Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalBoundaryArea.CellArea source depth edge) :
  cell.left.total = source.increment edge := by
  rw [cell.left.total_eq, cell.leftPath_eq, DyadicPrimitivePaths.dyadicIncrements_sum]
  rfl

/-- The cached reciprocal-path total is the original retained reciprocal primitive increment. -/
theorem right_total (cell : Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalBoundaryArea.CellArea source depth edge) :
  cell.reciprocal.total = cell.right.increment := by
  rw [cell.reciprocal.total_eq, cell.rightPath_eq, DyadicPrimitivePaths.dyadicIncrements_sum,
    cell.right.reciprocalValue_left, Data.Gaussian.Basic.sub_zero, cell.right.increment_eq]
  rfl

/-- The cached source-path area equals the original anchored primitive's finite dyadic area. -/
theorem left_area (cell : Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalBoundaryArea.CellArea source depth edge) :
  cell.left.area =
    DyadicBoundaryRibbon.dyadicArea (CellPrimitive.sourceValue source edge) depth edge.left.parameter
      edge.right.parameter := by
  rw [cell.left.area_eq, cell.leftPath_eq,
    ← DyadicPrimitivePaths.dyadicIncrements_sub_constant _ (source.primitive.value.eval (parent.edge.point
      edge.left.parameter))]
  exact DyadicPrimitivePaths.pathArea_dyadicIncrements _ _ _ _ (CellPrimitive.sourceValue_left source)

/-- The cached reciprocal-path area equals the original anchored reciprocal primitive's finite dyadic area. -/
theorem right_area (cell : Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalBoundaryArea.CellArea source depth edge) :
  cell.reciprocal.area =
    DyadicBoundaryRibbon.dyadicArea cell.right.reciprocalValue depth edge.left.parameter edge.right.parameter := by
  rw [cell.reciprocal.area_eq, cell.rightPath_eq]
  exact DyadicPrimitivePaths.pathArea_dyadicIncrements _ _ _ _ cell.right.reciprocalValue_left

/-- The two original cached cell areas satisfy the geometric area bound times fourth-power cell width. -/
theorem area_error (cell : Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalBoundaryArea.CellArea source depth edge) :
    Data.Gaussian.Norm.Basic.normSq (cell.left.area - cell.reciprocal.area) ≤
      Geometric.Basic.quarterRadius data.areaScale index * (edge.right.parameter - edge.left.parameter) ^ 4 := by
  rw [cell.left_area, cell.right_area]
  exact cell.right.area_error_geometric source depth

/-- The original cached cell totals satisfy the primitive discrepancy bound times squared cell width. -/
theorem total_error (cell : Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalBoundaryArea.CellArea source depth edge) :
    Data.Gaussian.Norm.Basic.normSq (cell.left.total - cell.reciprocal.total) ≤
      Geometric.Basic.quarterRadius (UniformReciprocalPrimitives.Data.errorScale data) index * (edge.right.parameter -
        edge.left.parameter) ^ 2 := by
  rw [cell.left_total, cell.right_total]
  exact cell.right.increment_error source

/-- The original source-path total satisfies the retained slope ceiling times squared cell width. -/
theorem left_bound (cell : Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalBoundaryArea.CellArea source depth edge) :
    Data.Gaussian.Norm.Basic.normSq cell.left.total ≤ data.sourceSlope * (edge.right.parameter -
      edge.left.parameter) ^ 2 := by
  rw [cell.left_total]
  exact source.increment_bound edge.left.inside edge.right.inside

/-- The reciprocal-path total satisfies the original source slope and geometric discrepancy ceiling. -/
theorem right_bound (cell : Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalBoundaryArea.CellArea source depth edge) :
    Data.Gaussian.Norm.Basic.normSq cell.reciprocal.total ≤ 2 * (data.sourceSlope +
      Geometric.Basic.quarterRadius (UniformReciprocalPrimitives.Data.errorScale data) index) *
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
inductive AreaCells (source : UniformReciprocalPrimitives.SourcePrimitive data index) (depth : Nat) : List
  ClearSheetContinuation.Subdivision.ParameterEdge → Type
  /-- The empty original edge list retains no paired path caches. -/ | nil :
    AreaCells source depth []
  /-- Retain the original head edge's path caches followed by the matching original tail. -/ | cons {edge :
    ClearSheetContinuation.Subdivision.ParameterEdge} {remaining : List
    ClearSheetContinuation.Subdivision.ParameterEdge}
      (head : CellArea source depth edge) (tail :
        AreaCells source depth remaining) :
        AreaCells source depth (edge :: remaining)

constructive_injectivity AreaCells

namespace AreaCells

variable {source : SourcePrimitive data
  index}

/-- Cache paired path summaries along the original retained primitive-cell spine without replacing its primitives. -/
@[expose] def build (source : UniformReciprocalPrimitives.SourcePrimitive data index) (depth : Nat) : {edges : List
  ClearSheetContinuation.Subdivision.ParameterEdge} →
    UniformReciprocalPrimitives.PrimitiveCells data index edges →
      Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalBoundaryArea.AreaCells source depth edges
  | _, .nil => .nil
  | _, .cons head tail => .cons (Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalBoundaryArea.CellArea.build source
    head depth) (build source depth
    tail)

/-- Read the original source and reciprocal increment-path pairs in retained cell order. -/
@[expose] def pairs : {edges : List ClearSheetContinuation.Subdivision.ParameterEdge} →
  Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalBoundaryArea.AreaCells source depth edges → List (List
  InverseRootPolynomial.Gaussian × List InverseRootPolynomial.Gaussian)
  | _, .nil => []
  | _, .cons head tail => (head.leftPath, head.rightPath) :: tail.pairs

/-- There is exactly one retained path pair per original parameter edge. -/
theorem pairs_length {edges : List ClearSheetContinuation.Subdivision.ParameterEdge} (cells :
  Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalBoundaryArea.AreaCells source depth edges) : cells.pairs.length =
  edges.length := by
  induction cells with
  | nil => rfl
  | cons _ _ ih => exact congrArg Nat.succ ih

/-- Compose the cached block summaries; do not replay the fine path to obtain its aggregate total or area. -/
@[expose] def leftSummary : {edges : List ClearSheetContinuation.Subdivision.ParameterEdge} → (cells :
  Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalBoundaryArea.AreaCells source depth edges) → IncrementArea.Summary
  (cells.pairs.map Prod.fst).flatten
  | _, .nil => IncrementArea.Summary.build []
  | _, .cons head tail => head.left.append tail.leftSummary

/-- Compose the cached reciprocal block summaries without replaying their original fine increment paths. -/
@[expose] def rightSummary : {edges : List ClearSheetContinuation.Subdivision.ParameterEdge} → (cells :
  Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalBoundaryArea.AreaCells source depth edges) → IncrementArea.Summary
  (cells.pairs.map Prod.snd).flatten
  | _, .nil => IncrementArea.Summary.build []
  | _, .cons head tail => head.reciprocal.append tail.rightSummary

/-- The retained source paths are exactly the original edgewise dyadic increments of the shared source primitive. -/
theorem left_paths {edges : List ClearSheetContinuation.Subdivision.ParameterEdge} (cells :
  Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalBoundaryArea.AreaCells source depth edges) :
    cells.pairs.map Prod.fst = edges.map (fun edge => DyadicPrimitivePaths.dyadicIncrements
      (fun parameter => source.primitive.value.eval (parent.edge.point parameter)) depth edge.left.parameter
        edge.right.parameter) := by
  induction cells with
  | nil => rfl
  | cons head tail ih =>
      change head.leftPath :: tail.pairs.map Prod.fst = _
      rw [head.leftPath_eq, ih]
      rfl

/-- The retained source summary reads the original whole-parent dyadic area at the combined coarse and fine depth. -/
theorem source_area (mesh : UniformReciprocalCover.Mesh data) (cells :
  Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalBoundaryArea.AreaCells source depth mesh.edges) :
    cells.leftSummary.area = DyadicBoundaryRibbon.dyadicArea
      (fun parameter => source.primitive.value.eval (parent.edge.point parameter) - source.primitive.value.eval
        (parent.edge.point 0))
      (mesh.depth + depth) 0 1 := by
  rw [cells.leftSummary.area_eq, cells.left_paths, mesh.edges_eq, DyadicPrimitivePaths.dyadicEdges_flatten_increments,
    ← DyadicPrimitivePaths.dyadicIncrements_sub_constant _ (source.primitive.value.eval (parent.edge.point 0))]
  exact DyadicPrimitivePaths.pathArea_dyadicIncrements _ _ _ _ (_root_.sub_self _)

/-- The retained source summary total is the exact original parent endpoint difference. -/
theorem source_total (mesh : UniformReciprocalCover.Mesh data) (cells :
  Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalBoundaryArea.AreaCells source depth mesh.edges) :
    cells.leftSummary.total = source.primitive.value.eval (parent.edge.point 1) - source.primitive.value.eval
      (parent.edge.point 0) := by
  rw [cells.leftSummary.total_eq, cells.left_paths, mesh.edges_eq, DyadicPrimitivePaths.dyadicEdges_flatten_increments,
    DyadicPrimitivePaths.dyadicIncrements_sum]
  rfl

/-- The full area trace has precisely the already cached reciprocal integral. This readback prevents a later area
consumer from changing paths. -/
theorem build_right_total (source : UniformReciprocalPrimitives.SourcePrimitive data index) (depth : Nat) {edges : List
  ClearSheetContinuation.Subdivision.ParameterEdge}
    (primitives : UniformReciprocalPrimitives.PrimitiveCells data index edges) :
    (build source depth
      primitives).rightSummary.total = Data.Gaussian.Norm.Sum.Basic.gaussianSum primitives.values := by
  induction primitives with
  | nil => rfl
  | cons head tail ih =>
      change (Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalBoundaryArea.CellArea.build source head
        depth).reciprocal.total + (build source
        depth tail).rightSummary.total =
        head.increment + Data.Gaussian.Norm.Sum.Basic.gaussianSum tail.values
      rw [(Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalBoundaryArea.CellArea.build source head depth).right_total,
        ih]
      rfl

/-- Every retained original path pair satisfies the common dyadic area, total-discrepancy and total-size bounds. -/
private theorem bounds (mesh : UniformReciprocalCover.Mesh data) {edges : List
  ClearSheetContinuation.Subdivision.ParameterEdge} (cells :
  Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalBoundaryArea.AreaCells source depth edges)
    (members : ∀ edge ∈ edges, edge ∈ mesh.edges) :
    ∀ pair ∈ cells.pairs,
      Data.Gaussian.Norm.Basic.normSq (IncrementArea.pathArea pair.1 - IncrementArea.pathArea pair.2) ≤
        Geometric.Basic.quarterRadius data.areaScale index * (Geometric.Basic.quarterRadius 1 mesh.depth) ^ 2 ∧
      Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum pair.1 -
        Data.Gaussian.Norm.Sum.Basic.gaussianSum pair.2) ≤ Geometric.Basic.quarterRadius
        (UniformReciprocalPrimitives.Data.errorScale data) index * Geometric.Basic.quarterRadius 1 mesh.depth ∧
      Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum pair.1) ≤ 2 *
        (data.sourceSlope + Geometric.Basic.quarterRadius (UniformReciprocalPrimitives.Data.errorScale data) index) *
        Geometric.Basic.quarterRadius 1 mesh.depth ∧
      Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum pair.2) ≤ 2 *
        (data.sourceSlope + Geometric.Basic.quarterRadius (UniformReciprocalPrimitives.Data.errorScale data) index) *
        Geometric.Basic.quarterRadius 1 mesh.depth := by
  induction cells with
  | nil => intro _ member; exact False.elim (List.not_mem_nil member)
  | @cons edge remaining head tail ih =>
      intro pair member
      rcases Data.List.Membership.mem_cons.mp member with same | member
      · subst pair
        have width := UniformPrimitiveMesh.dyadicEdges_width mesh.depth UniformPrimitiveMesh.firstEndpoint
          UniformPrimitiveMesh.lastEndpoint edge
          (mesh.edges_eq ▸ members edge (List.mem_cons_self ..))
        have unit : (UniformPrimitiveMesh.lastEndpoint.parameter - UniformPrimitiveMesh.firstEndpoint.parameter) ^ 2 =
          (1 : InverseRootPolynomial.Coordinate) := by decide
        rw [unit] at width
        change Data.Gaussian.Norm.Basic.normSq (IncrementArea.pathArea head.leftPath - IncrementArea.pathArea
          head.rightPath) ≤ _ ∧
          Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum head.leftPath -
            Data.Gaussian.Norm.Sum.Basic.gaussianSum head.rightPath) ≤ _ ∧
          Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum head.leftPath) ≤ _ ∧
            Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum head.rightPath) ≤ _
        rw [← head.left.area_eq, ← head.reciprocal.area_eq, ← head.left.total_eq, ← head.reciprocal.total_eq]
        refine ⟨head.area_error.trans_eq ?_, head.total_error.trans_eq (by rw [width]), ?_,
          head.right_bound.trans_eq (by rw [width])⟩
        · rw [show (edge.right.parameter - edge.left.parameter) ^ 4 = ((edge.right.parameter - edge.left.parameter) ^ 2)
            ^ 2 by ring1, width]
        · have slopeLe : data.sourceSlope ≤ 2 * (data.sourceSlope + Geometric.Basic.quarterRadius
            (UniformReciprocalPrimitives.Data.errorScale data) index) := by
            have errorNonnegative := Geometric.Basic.quarterRadius_nonneg
              (UniformReciprocalPrimitives.Data.errorScale_nonnegative data) index
            exact (le_add_of_nonneg_right errorNonnegative).trans
              ((le_add_of_nonneg_right (add_nonneg data.sourceSlope_nonnegative errorNonnegative)).trans_eq (by ring1))
          exact head.left_bound.trans
            ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct slopeLe
              (Fraction.Order.Arithmetic.sq_nonneg_direct _)).trans_eq (by rw [width]))
      · exact ih (fun other found => members other (List.mem_cons_of_mem _ found)) pair member

/-- The whole literal reciprocal path pays internal area errors AND the polygon of block totals. No fine depth or coarse
cell count is hidden. -/
theorem whole_area_bound (mesh : UniformReciprocalCover.Mesh data) (cells :
  Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalBoundaryArea.AreaCells source depth mesh.edges) :
    Data.Gaussian.Norm.Basic.normSq (cells.leftSummary.area - cells.rightSummary.area) ≤
      2 * (Geometric.Basic.quarterRadius data.areaScale index * Geometric.Basic.quarterRadius 1 mesh.depth +
        32 * Geometric.Basic.quarterRadius (UniformReciprocalPrimitives.Data.errorScale data) index * (data.sourceSlope
          + Geometric.Basic.quarterRadius (UniformReciprocalPrimitives.Data.errorScale data) index)) := by
  rw [cells.leftSummary.area_eq, cells.rightSummary.area_eq]
  have bounded := cells.bounds mesh (fun _ member => member)
  have estimate := IncrementAreaComparison.blocks_area_difference_bound cells.pairs
    (Fraction.Order.Arithmetic.mul_nonneg_direct (Geometric.Basic.quarterRadius_nonneg
      (UniformReciprocalPrimitives.Data.errorScale_nonnegative data) index)
      (Geometric.Basic.quarterRadius_nonneg (by decide) mesh.depth))
    (Fraction.Order.Arithmetic.mul_nonneg_direct
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
        (add_nonneg data.sourceSlope_nonnegative (Geometric.Basic.quarterRadius_nonneg
          (UniformReciprocalPrimitives.Data.errorScale_nonnegative data) index)))
      (Geometric.Basic.quarterRadius_nonneg (by decide) mesh.depth))
    (fun pair member => (bounded pair member).1) (fun pair member => (bounded pair member).2.1)
    (fun pair member => (bounded pair member).2.2.1) (fun pair member => (bounded pair member).2.2.2)
  rw [cells.pairs_length] at estimate
  have countWidth : (mesh.edges.length : InverseRootPolynomial.Coordinate) ^ 2 * Geometric.Basic.quarterRadius 1
    mesh.depth = 1 := by
    rw [mesh.edges_length, mesh.edgeCount_eq]
    exact (by ring1 : (((2 ^ mesh.depth : Nat) : InverseRootPolynomial.Coordinate) ^ 2 * Geometric.Basic.quarterRadius 1
      mesh.depth) =
      ((2 ^ mesh.depth : Nat) : InverseRootPolynomial.Coordinate) * (((2 ^ mesh.depth : Nat) :
        InverseRootPolynomial.Coordinate) * Geometric.Basic.quarterRadius 1 mesh.depth)).trans
      (DyadicCount.dyadic_count_cancel 1 mesh.depth)
  apply estimate.trans_eq
  calc
    _ = 2 * (Geometric.Basic.quarterRadius data.areaScale index * Geometric.Basic.quarterRadius 1 mesh.depth *
        ((mesh.edges.length : InverseRootPolynomial.Coordinate) ^ 2 * Geometric.Basic.quarterRadius 1 mesh.depth) +
        32 * Geometric.Basic.quarterRadius (UniformReciprocalPrimitives.Data.errorScale data) index * (data.sourceSlope
          + Geometric.Basic.quarterRadius (UniformReciprocalPrimitives.Data.errorScale data) index) *
          ((mesh.edges.length : InverseRootPolynomial.Coordinate) ^ 2 * Geometric.Basic.quarterRadius 1 mesh.depth) ^ 2)
            := by ring1
    _ = _ := by rw [countWidth]; ring1

/-- A single pre-index scale pays the entire concatenated path area at every fine spatial depth. The geometric rate has
no count-dependent floor. -/
theorem whole_area_error (mesh : UniformReciprocalCover.Mesh data) (cells :
  Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalBoundaryArea.AreaCells source depth mesh.edges) :
    Data.Gaussian.Norm.Basic.normSq (cells.leftSummary.area - cells.rightSummary.area) ≤
      Geometric.Basic.quarterRadius
      (Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalBoundaryArea.Data.boundaryAreaScale data) index := by
  have errorLe : Geometric.Basic.quarterRadius (UniformReciprocalPrimitives.Data.errorScale data) index ≤
    (UniformReciprocalPrimitives.Data.errorScale data) := by
    simpa only [Geometric.Basic.quarterRadius_eq_mul_pow, pow_zero, Fraction.Field.mul_one_direct, -eq_self, -iff_self]
      using
      quarterRadius_antitone (UniformReciprocalPrimitives.Data.errorScale_nonnegative data) (Nat.zero_le
        index)
  have widthLe : Geometric.Basic.quarterRadius (1 : InverseRootPolynomial.Coordinate) mesh.depth ≤ 1 := by
    simpa only [Geometric.Basic.quarterRadius_eq_mul_pow, pow_zero, Fraction.Field.mul_one_direct, -eq_self, -iff_self]
      using
      quarterRadius_antitone (by decide : (0 : InverseRootPolynomial.Coordinate) ≤ 1) (Nat.zero_le mesh.depth)
  have fineBound : Geometric.Basic.quarterRadius data.areaScale index * Geometric.Basic.quarterRadius 1 mesh.depth ≤
    Geometric.Basic.quarterRadius data.areaScale index := by
    simpa only [Fraction.Field.mul_one_direct, -eq_self, -iff_self] using
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct widthLe (Geometric.Basic.quarterRadius_nonneg
        data.areaScale_nonnegative index)
  have coarseBound : 32 * Geometric.Basic.quarterRadius (UniformReciprocalPrimitives.Data.errorScale data) index *
    (data.sourceSlope + Geometric.Basic.quarterRadius (UniformReciprocalPrimitives.Data.errorScale data) index) ≤
      32 * Geometric.Basic.quarterRadius (UniformReciprocalPrimitives.Data.errorScale data) index * (data.sourceSlope +
        (UniformReciprocalPrimitives.Data.errorScale data)) :=
    Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (add_le_add le_rfl errorLe)
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel) (Geometric.Basic.quarterRadius_nonneg
        (UniformReciprocalPrimitives.Data.errorScale_nonnegative data) index))
  exact (cells.whole_area_bound mesh).trans
    ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (add_le_add fineBound coarseBound) (by
      decide)).trans_eq (by
      simp only [Geometric.Basic.quarterRadius_eq_mul_pow,
        Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalBoundaryArea.Data.boundaryAreaScale, -eq_self, -iff_self]
      ring1))

end AreaCells

namespace Cover

set_option genInjectivity false in
/-- A requested complete reciprocal path-area comparison on the original cover.

The retained source primitive, fine cell paths and composed summaries share one polynomial stage with its exact paid
geometric error. -/
structure AreaRequest (cover : UniformReciprocalCover.Cover data) (depth : Nat) (target :
  InverseRootPolynomial.Coordinate) where
  /-- The shared original polynomial refinement stage. -/ index : Nat
  /-- The original source primitive shared by all retained reciprocal cells. -/ source :
    UniformReciprocalPrimitives.SourcePrimitive data index
  /-- The original finite edge-indexed bank of paired paths and cached summaries. -/ cells :
    Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalBoundaryArea.AreaCells source depth cover.mesh.edges
  /-- The cached total and area summary of the exact original source increment path. -/ left : IncrementArea.Summary
    (cells.pairs.map Prod.fst).flatten
  /-- The composed summary of the exact concatenated original reciprocal cell paths. -/ right : IncrementArea.Summary
    (cells.pairs.map Prod.snd).flatten
  /-- The cached squared-norm ceiling for the complete source-minus-reciprocal area discrepancy. -/ error :
    InverseRootPolynomial.Coordinate
  /-- The cached error is the full boundary-area scale's geometric quarter-radius at the retained polynomial stage. -/
    error_eq : error = Geometric.Basic.quarterRadius
    (Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalBoundaryArea.Data.boundaryAreaScale data) index
  /-- The cached complete area error is strictly below the requested target. -/ error_lt : error < target
  /-- The exact retained source and reciprocal summary areas satisfy the cached discrepancy bound. -/ close :
    Data.Gaussian.Norm.Basic.normSq (left.area - right.area) ≤ error

constructive_injectivity AreaRequest

/-- Reuse a primitive bank already shared with the prepared integrator and grid. Its summaries are composed from cached
fine-block totals and areas. -/
@[expose] def AreaRequest.ofPrimitives (cover : UniformReciprocalCover.Cover data) (source :
  UniformReciprocalPrimitives.SourcePrimitive data index)
    (primitives : UniformReciprocalPrimitives.PrimitiveCells data index cover.mesh.edges) (depth : Nat) (target :
      InverseRootPolynomial.Coordinate)
    (accurate : Geometric.Basic.quarterRadius
      (Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalBoundaryArea.Data.boundaryAreaScale data) index < target) :
      AreaRequest cover depth target :=
  let cells := Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalBoundaryArea.AreaCells.build source depth primitives
  ⟨index, source, cells, cells.leftSummary, cells.rightSummary, Geometric.Basic.quarterRadius
    (Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalBoundaryArea.Data.boundaryAreaScale data) index, rfl,
    accurate, cells.whole_area_error cover.mesh⟩

/-- Select a common polynomial stage paying the area target and cache the original source and reciprocal path summaries.
-/
@[expose] def areaRequest (cover : UniformReciprocalCover.Cover data) (depth : Nat) (target :
  InverseRootPolynomial.Coordinate) (positive : 0 < target) :
  AreaRequest cover depth target :=
  let index := Search.firstQuarterBelow
    (Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalBoundaryArea.Data.boundaryAreaScale data) 0 target
  let source := SourcePrimitive.build data index
  let primitives := PrimitiveCells.build index cover.cells
  Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalBoundaryArea.Cover.AreaRequest.ofPrimitives cover source primitives
    depth target
    (Search.firstQuarterBelow_accurate _
      (Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalBoundaryArea.Data.boundaryAreaScale_nonnegative data) 0 _
      positive)

/-- The retained source summary reads the original whole-parent dyadic area at the combined coarse and fine depth. -/
theorem AreaRequest.source_area {cover : UniformReciprocalCover.Cover data} {target : InverseRootPolynomial.Coordinate}
  (request : AreaRequest cover depth target) :
    request.left.area = DyadicBoundaryRibbon.dyadicArea
      (fun parameter => request.source.primitive.value.eval (parent.edge.point parameter) -
        request.source.primitive.value.eval (parent.edge.point 0))
      (cover.mesh.depth + depth) 0 1 := by
  rw [request.left.area_eq, ← request.cells.leftSummary.area_eq]
  exact request.cells.source_area cover.mesh

/-- The retained source summary total is the exact original parent endpoint difference. -/
theorem AreaRequest.source_total {cover : UniformReciprocalCover.Cover data} {target : InverseRootPolynomial.Coordinate}
  (request : AreaRequest cover depth target) :
    request.left.total = request.source.primitive.value.eval (parent.edge.point 1) - request.source.primitive.value.eval
      (parent.edge.point 0) := by
  rw [request.left.total_eq, ← request.cells.leftSummary.total_eq]
  exact request.cells.source_total cover.mesh

end Cover
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalBoundaryArea
