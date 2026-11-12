module

meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Integration.Program.Gaussian.Cached.Basic
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.CompatibleRefinement
import Purelib.Integration.Polynomial.Gaussian.Path.Uniform

import Purelib.Curves.Hyperelliptic.Differentials.SquareFactor
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Algebraic.SquareFactor.Accuracy
import Purelib.Integration.Algebraic.SquareFactor.CoefficientBounds
public import Purelib.Integration.Algebraic.SquareFactor.MeshBounds
import Purelib.Integration.Algebraic.SquareFactor.OwnedCells
import Purelib.Integration.Algebraic.SquareFactor.PathContinuation
import Purelib.Integration.Algebraic.SquareFactor.PathInput
import Purelib.Integration.Algebraic.SquareFactor.UniformRefinement
import Purelib.Riemann.Branches.ClearSheetContinuation
public import Purelib.Integration.Algebraic.SquareFactor.RefinementGeometry
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Integration.Algebraic.SquareFactor.CellModels
import Purelib.Integration.Polynomial.Gaussian.Path.Allowance
import Purelib.Data.Rat.Fraction.Order.Basic
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

open Purelib.Integration.Polynomial.Gaussian.Path.CompatibleRefinement.PathModel

open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius_antitone)

public section

/-!
# Geometrically shrinking layers of the original-differential integrator

Every layer caches the actual inherited cells and numerical model.  Exact
whole-path geometry and generated local allowances justify both its own
accuracy and its comparison with the next layer.  The layer index is an
ordinary finite refinement count, not a completed integral.
-/

namespace Purelib.Integration.Algebraic.SquareFactor.IntegrationLayers

open Purelib.Integration.Polynomial.Gaussian.Path
open Purelib.Riemann
open Purelib.Riemann.Branches Purelib.Integration.Algebraic.SquareFactor Purelib.Riemann.Integration
open Purelib.Integration.Algebraic.SquareFactor.RefinementGeometry (parameterEdge)

open Purelib.Curves.Hyperelliptic.Differentials.SquareFactor
open Purelib.Integration.Algebraic.SquareFactor.PathInput
open Purelib.Integration.Algebraic.SquareFactor.PathContinuation
open Purelib.Integration.Algebraic.SquareFactor.OwnedCells
open Purelib.Integration.Algebraic.SquareFactor.CoefficientBounds
open Purelib.Integration.Algebraic.SquareFactor.UniformRefinement

open Purelib.Data.Gaussian.Basic.Canonical

open Purelib.Data.Rat in
/-- The rational carrier for retained integration-layer allowances. -/
abbrev Coordinate := Fraction.Rational

variable {polynomial : GaussianPolynomial} {request :
  Request}
  {prepared : Prepared polynomial request} {segment :
    Segment}
  {data : Data prepared segment}

open Purelib.Approximation.Rational in
open Purelib.Integration.Algebraic.SquareFactor in
open Purelib.Integration.Polynomial.Gaussian.Path in
open Purelib.Riemann.Branches in
set_option genInjectivity false in
/-- A retained dyadic path model with cached cells and a uniform local allowance at the requested accuracy index.

The exact geometry and model equations retain the original compiled cells, while the allowance meets the index's
quarter-radius target. -/
structure Layer (safe : data.Safe) (index : Nat) where
  /-- The actual retained dyadic mesh depth. -/ depth : Nat
  /-- The cached ordered compiled continuation cells. -/ cells : List (Cell safe)
  /-- The exact cached parameter edges form the retained-depth unit-interval dyadic mesh. -/ geometry : cells.map
    parameterEdge = ClearSheetContinuation.Subdivision.dyadicEdges depth PathContinuation.first
    PathContinuation.last
  /-- The cached original path model. -/ model : Basic.PathModel
  /-- The cached model cells equal the exact model readback of the retained compiled cells. -/ model_cells : model.cells
    = cells.map (fun cell => cell.model.cell)
  /-- The retained common local cell allowance. -/ allowance : Coordinate
  /-- The common local allowance meets the quarter-radius target at the original index. -/ allowance_le : allowance ≤
    Geometric.Basic.quarterRadius 1 index
  /-- Every exact retained cell meets the common local allowance. -/ cells_allowance_le : ∀ cell ∈ cells,
    cell.model.cell.localAllowance ≤ allowance

constructive_injectivity Layer

namespace Layer

variable {safe : data.Safe} {index : Nat} (layer : IntegrationLayers.Layer
  safe index)

open Purelib.Integration.Algebraic.SquareFactor.IntegrationLayers.Layer in
open Purelib.Riemann.Branches in
/-- The retained layer has exactly two to the power of its actual dyadic depth cells. -/
theorem count : layer.cells.length = 2 ^ layer.depth := by
  have count := congrArg List.length layer.geometry
  rw [Data.List.Map.length_map, ClearSheetContinuation.Subdivision.dyadicEdges_length] at count
  exact count

/-- The retained model has exactly the original layer's dyadic cell count. -/
theorem model_count : layer.model.cells.length = 2 ^ layer.depth := by
  rw [layer.model_cells, Data.List.Map.length_map, layer.count]

open Purelib.Approximation.Rational in
open Purelib.Data.List in
open Purelib.Integration.Algebraic.SquareFactor in
/-- Every retained layer cell has the exact squared dyadic width at the original layer depth. -/
theorem width_sq (cell : Cell safe) (member : cell ∈ layer.cells) :
    cell.edge.span.width ^ 2 = Geometric.Basic.quarterRadius 1 layer.depth := by
  have edgeMember : parameterEdge cell ∈ layer.cells.map parameterEdge :=
    Map.mem_map.mpr ⟨cell, member, rfl⟩
  rw [layer.geometry] at edgeMember
  have width := MeshBounds.dyadic_width_sq _ PathContinuation.first PathContinuation.last _ edgeMember
  have unitWidth : (last.parameter - first.parameter) ^ 2 = (1 :
    Coordinate) := by decide
  rw [unitWidth] at width
  exact width

open Purelib.Approximation.Rational in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Integration.Algebraic.SquareFactor in
/-- Every retained layer cell has the direction-norm quarter-radius displacement at its original depth. -/
theorem displacement_sq (cell : Cell safe) (member : cell ∈ layer.cells) :
    Norm.Basic.normSq cell.model.cell.displacement = Geometric.Basic.quarterRadius
      (Norm.Basic.normSq
      segment.direction) layer.depth := by
  change Norm.Basic.normSq (segment.point cell.edge.span.interval.upper - segment.point
    cell.edge.span.interval.lower) = _
  rw [MeshBounds.pointMovement]
  change Norm.Basic.normSq segment.direction * cell.edge.span.width ^ 2 = _
  rw [layer.width_sq cell member, Geometric.Basic.quarterRadius_eq_mul_pow,
    Geometric.Basic.quarterRadius_eq_mul_pow, Fraction.Field.one_mul]

open Purelib.Data.Gaussian in
open Purelib.Data.List in
open Purelib.Integration.Algebraic.SquareFactor in
/-- The retained layer's aggregate allowance meets the original direction norm times its local allowance. -/
theorem aggregateAllowance_le : layer.model.aggregateAllowance ≤ Norm.Basic.normSq segment.direction *
  layer.allowance := by
  apply Basic.PathModel.uniform_aggregateAllowance_le layer.model layer.depth _ _
    (Norm.Basic.normSq_nonneg segment.direction) layer.model_count
  intro model member
  rw [layer.model_cells] at member
  rcases Map.mem_map.mp member with ⟨cell, cellMember, rfl⟩
  exact ⟨(layer.displacement_sq cell cellMember).le, layer.cells_allowance_le cell cellMember⟩

open Purelib.Approximation.Rational in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- The retained model allowance meets the direction-norm quarter radius at the original accuracy index. -/
theorem modelAllowance_le : layer.model.aggregateAllowance ≤
    Geometric.Basic.quarterRadius (Norm.Basic.normSq segment.direction) index := by
  calc
    layer.model.aggregateAllowance ≤ Norm.Basic.normSq segment.direction * layer.allowance :=
      layer.aggregateAllowance_le
    _ ≤ Norm.Basic.normSq segment.direction * Geometric.Basic.quarterRadius 1 index :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct layer.allowance_le (Norm.Basic.normSq_nonneg
        segment.direction)
    _ = _ := by
      rw [Geometric.Basic.quarterRadius_eq_mul_pow, Geometric.Basic.quarterRadius_eq_mul_pow,
        Fraction.Field.one_mul]

end Layer

open Purelib.Approximation.Rational in
open Purelib.Data.Rat in
open Purelib.Integration.Algebraic.SquareFactor in
/-- Assemble a unit-accuracy initial layer from its supplied original resolution and already compiled run.

The returned layer retains the exact cell list, path model and dyadic depth
from the supplied run. Geometry and allowance bounds consume that same
resolution and its cached mesh; no isolation or cell compilation is repeated.
-/
@[expose] def Layer.ofInitialRun {data : Data prepared segment} (safe : data.Safe) (sheet : Fin 2)
    (resolution : Accuracy.Resolution data 1 1)
    (run : CompiledRun safe sheet resolution.rootDiameter
      resolution.rootDiameterPositive resolution.minimumDepth) : Layer safe 0 :=
  let depth := run.depth
  { depth
    cells := run.cells
    geometry := MeshBounds.CompiledRun.parameterEdges run
    model := run.pathModel
    model_cells := rfl
    allowance := CoefficientBounds.parameterSlope data * Geometric.Basic.quarterRadius 1 depth +
      CoefficientBounds.rootSlope data * resolution.rootDiameter
    allowance_le := by
      have bound := resolution.model_bound_lt safe (by decide) depth run.minimumDepth_le
      simpa only [Geometric.Basic.quarterRadius_eq_mul_pow, pow_zero,
        Fraction.Field.mul_one_direct, Fraction.Field.one_mul] using bound.le
    cells_allowance_le := by
      intro cell member
      have bound := MeshBounds.cell_allowance_le cell
      rw [MeshBounds.CompiledRun.width_sq run cell member,
        MeshBounds.CompiledRun.diameter run cell member] at bound
      exact bound }

open Purelib.Integration.Algebraic.SquareFactor in
/-- Resolve unit local accuracy and compile the original selected sheet into the retained initial layer.

The original selected run supplies the cached cells, exact dyadic geometry
and common local allowance bound through the named retained-run constructor.
-/
@[expose] def initial {data : Data prepared segment} (safe : data.Safe) (sheet : Fin 2) :
    Layer safe 0 :=
  let resolution := Accuracy.resolve safe 1 (by decide) 1 (by decide)
  let run := OwnedCells.compile (safe := safe) sheet resolution.rootDiameter
    resolution.rootDiameterPositive resolution.minimumDepth
  Layer.ofInitialRun safe sheet resolution run

open Purelib.Integration.Algebraic.SquareFactor in
/-- Original resolution and compiled-run identities preserve the exact original initial layer and every cache. -/
theorem Layer.ofInitialRun_eq_initial {data : Data prepared segment} (safe : data.Safe) (sheet : Fin 2)
    (resolution : Accuracy.Resolution data 1 1)
    (resolutionEq : resolution = Accuracy.resolve safe 1 (by decide) 1 (by decide))
    (run : CompiledRun safe sheet resolution.rootDiameter
      resolution.rootDiameterPositive resolution.minimumDepth)
    (runEq : run = OwnedCells.compile sheet resolution.rootDiameter
      resolution.rootDiameterPositive resolution.minimumDepth) :
    Layer.ofInitialRun safe sheet resolution run = initial safe sheet := by
  cases resolutionEq
  cases runEq
  rfl

open Purelib.Approximation.Rational in
open Purelib.Integration.Algebraic.SquareFactor in
set_option genInjectivity false in
/-- The exact retained refinement of one original layer to the next quarter-radius accuracy target. -/
structure Next {safe : data.Safe} {index : Nat} (layer : Layer safe index) where
  /-- The exact target-indexed refinement of the original layer's retained cells and depth. -/ result :
    Refined layer.depth layer.cells (Geometric.Basic.quarterRadius 1 (index + 1))

constructive_injectivity Next

namespace Next

variable {safe : data.Safe} {index : Nat} {parent : Layer
  safe index}

section
open Purelib.Approximation.Rational
open Purelib.Integration.Algebraic.SquareFactor
/-- Retain the supplied next-target refinement of the exact original parent without rebuilding its cached result. -/
@[expose] def ofRefined (parent : Layer safe index)
    (result : Refined parent.depth parent.cells (Geometric.Basic.quarterRadius 1 (index + 1))) :
    Next parent := ⟨result⟩

/-- Refine the original layer using its retained widths and the next positive quarter-radius target. -/
@[expose] def make (parent : Layer safe index) : Next parent :=
  ofRefined parent (UniformRefinement.refine parent.depth parent.cells parent.width_sq
    (Geometric.Basic.quarterRadius 1 (index + 1))
    (Geometric.Basic.quarterRadius_pos (by decide) _))

/-- Retaining the original next-target refinement preserves the exact original next-layer construction. -/
theorem ofRefined_eq_make (parent : Layer safe index)
    (result : Refined parent.depth parent.cells (Geometric.Basic.quarterRadius 1 (index + 1)))
    (same : result = UniformRefinement.refine parent.depth parent.cells parent.width_sq
      (Geometric.Basic.quarterRadius 1 (index + 1)) (Geometric.Basic.quarterRadius_pos (by decide) _)) :
    ofRefined parent result = make parent := by
  cases same
  rfl

/-- Read the next layer from the exact retained refinement, preserving its cached cells, model and allowance. -/
@[expose] def layer (next : Next parent) : Layer safe (index + 1) where
  depth := parent.depth + next.result.synchronized.depth
  cells := next.result.cells
  geometry := RefinementGeometry.Refined.geometry
    next.result parent.geometry
  model := next.result.model
  model_cells := next.result.model_cells
  allowance := next.result.allowance
  allowance_le := (next.result.allowance_lt (Geometric.Basic.quarterRadius_pos (by decide) _)).le
  cells_allowance_le := next.result.cells_allowance_le

end

open Purelib.Integration.Polynomial.Gaussian.Cell in
open Purelib.Integration.Polynomial.Gaussian.Path in
/-- Transport a compatible refinement along equality of the exact original parent list.

The supplied equality changes only the parent-list index. The original
refinement certificate and its comparison data remain retained. -/
@[expose] def castParents {parents otherParents children : List Basic.CellModel}
    (certificate : Basic.PathModel.CompatibleConstantPathRefinement parents children) (equal : parents = otherParents) :
    Basic.PathModel.CompatibleConstantPathRefinement otherParents children := by
  cases equal
  exact certificate

open Purelib.Integration.Algebraic.SquareFactor in
open Purelib.Integration.Polynomial.Gaussian.Cell in
open Purelib.Integration.Polynomial.Gaussian.Path in
/-- Transporting the parent-list index preserves the exact comparison allowance. -/
private theorem castParents_comparisonAllowance {parents otherParents children : List Basic.CellModel}
    (certificate : Basic.PathModel.CompatibleConstantPathRefinement parents children) (equal : parents = otherParents) :
    (CompatibleConstantPathRefinement.comparisonAllowance
      (castParents certificate equal)) =
      (CompatibleConstantPathRefinement.comparisonAllowance certificate) := by
  cases equal
  rfl

open Purelib.Integration.Algebraic.SquareFactor in
open Purelib.Integration.Polynomial.Gaussian.Path in
/-- Read the compatible refinement between the original parent model and retained next-layer model. -/
@[expose] def refinement (next : Next parent) :
    Basic.PathModel.CompatibleConstantPathRefinement parent.model.cells next.layer.model.cells :=
  castParents next.result.refinement parent.model_cells.symm

open Purelib.Data.Gaussian in
open Purelib.Integration.Algebraic.SquareFactor in
open Purelib.Integration.Polynomial.Gaussian.Path in
/-- The next refinement's comparison allowance meets the original direction norm times twice the two layer allowances.
-/
theorem comparisonAllowance_le (next : Next parent) :
  (CompatibleConstantPathRefinement.comparisonAllowance next.refinement) ≤
    Norm.Basic.normSq segment.direction * (2 * (parent.allowance + next.layer.allowance)) := by
  let expansion := next.result.synchronized.expansion
  have equal : (CompatibleConstantPathRefinement.comparisonAllowance next.refinement) =
    (CompatibleConstantPathRefinement.comparisonAllowance expansion.refinement) :=
    (castParents_comparisonAllowance next.result.refinement parent.model_cells.symm).trans
      next.result.comparisonAllowance_eq
  apply equal.le.trans
  change (Basic.PathModel.mk (CompatibleConstantPathRefinement.comparisonCells
    expansion.refinement)).aggregateAllowance ≤ _
  apply Basic.PathModel.uniform_aggregateAllowance_le _ next.layer.depth _ _
    (Norm.Basic.normSq_nonneg segment.direction)
  · rw [CompatibleConstantPathRefinement.comparisonCells_length, expansion.models_eq,
      Data.List.Map.length_map, ← next.result.cells_eq]
    exact next.layer.count
  · apply expansion.comparison_bounds _ parent.allowance next.layer.allowance parent.cells_allowance_le
    intro child member
    have inLayer : child ∈ next.layer.cells := by
      change child ∈ next.result.cells
      rw [next.result.cells_eq]
      exact member
    exact ⟨(next.layer.displacement_sq child inLayer).le, next.layer.cells_allowance_le child inLayer⟩

open Purelib.Approximation.Rational in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Integration.Algebraic.SquareFactor in
open Purelib.Integration.Polynomial.Gaussian.Path in
/-- The retained next-layer comparison allowance meets the original index's quarter radius with four times the
direction-norm scale. -/
theorem comparisonAllowance_le_quarter (next : Next parent) :
  (CompatibleConstantPathRefinement.comparisonAllowance next.refinement) ≤
    Geometric.Basic.quarterRadius (4 * Norm.Basic.normSq segment.direction) index := by
  have childAllowance : next.layer.allowance ≤ Geometric.Basic.quarterRadius 1 index :=
    next.layer.allowance_le.trans (quarterRadius_antitone (by decide) (Nat.le_succ index))
  calc
    (CompatibleConstantPathRefinement.comparisonAllowance next.refinement) ≤
        Norm.Basic.normSq segment.direction * (2 * (parent.allowance + next.layer.allowance)) :=
          next.comparisonAllowance_le
    _ ≤ Norm.Basic.normSq segment.direction *
        (2 * (Geometric.Basic.quarterRadius 1 index + Geometric.Basic.quarterRadius 1 index)) :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          (add_le_add parent.allowance_le childAllowance) (by decide)) (Norm.Basic.normSq_nonneg segment.direction)
    _ = _ := by
      rw [Geometric.Basic.quarterRadius_eq_mul_pow, Geometric.Basic.quarterRadius_eq_mul_pow]
      ring1

end Next

end Purelib.Integration.Algebraic.SquareFactor.IntegrationLayers
