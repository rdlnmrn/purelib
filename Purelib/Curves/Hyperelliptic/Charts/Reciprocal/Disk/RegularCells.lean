module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentCells
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularComparison
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SheetAlignment
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.Dyadic.DyadicBoundaryRibbon
import Purelib.Integration.Path.Dyadic.DyadicPrimitivePaths
import Purelib.Integration.Path.IncrementArea
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularArea
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentPaths
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalBoundaryArea
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPrimitiveRibbon
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Riemann.Normalization.OwnerSeededInverseRoot
import Purelib.Tactic.Ring
meta import Mathlib.Tactic.Linter.Lint

public section

open Purelib
open Purelib.Approximation.Rational
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularArea
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularComparison
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SheetAlignment
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives
open Purelib.Data.Rat
open Purelib.Integration.Path
open Purelib.Integration.Path.Dyadic
open Purelib.Riemann.Branches
open Purelib.Riemann.Normalization

/-!
# Shared regular-cap paths consuming retained parent cells

The existing compared cell supplies its source path and inverse sample.
Only the signed shared primitive's endpoint values and increment path are
materialized. The source summary and root preparation are reused.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover (Cell Mesh)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives (SourcePrimitive)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBank
    (Bank
    Budget quarterRadius_mono)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentCells (ComparedCell)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentPaths (ComparedCells)
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision (ParameterEdge)
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Integration.Path.IncrementArea (Summary)
open Purelib.Integration.Path.Dyadic.DyadicBoundaryRibbon (dyadicArea)
open Purelib.Integration.Path.Dyadic.DyadicPrimitivePaths (dyadicIncrements dyadicIncrements_sum)
open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius)
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)

variable {genus count index depth : Nat} {curve : HyperellipticCurve genus}
  {differential : Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {parent : Purelib.Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : PreparedPatch parent} {data :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {edge :
    ParameterEdge} {cell :
    Cell data edge}
  {comparison : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples.Data regular cell} {source :
    SourcePrimitive data index}
  {box : Purelib.Geometry.Rational.Box} {capSample :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}

namespace RegularCells.Bank

/-- Compute a shared ceiling for the original comparison bank's signed regular-cap scales. -/
@[expose] def regularMaximum : {edges : List ClearSheetContinuation.Subdivision.ParameterEdge} → ParentBank.Bank regular
  data edges → InverseRootPolynomial.Coordinate
  | _, .nil => 0
  | _, .cons head tail => max (RegularComparison.Data.regularScale head)
    (regularMaximum tail)

/-- Every original retained cell's signed regular comparison scale lies below the supplied common bound. -/
@[expose] def RegularBounded : {edges : List ClearSheetContinuation.Subdivision.ParameterEdge} → ParentBank.Bank regular
  data edges → InverseRootPolynomial.Coordinate → Prop
  | _, .nil, _ => True
  | _, .cons head tail, upper => (RegularComparison.Data.regularScale head) ≤ upper ∧
    RegularBounded tail upper

/-- An upper bound on the original regular comparison bank remains valid after increasing the ceiling. -/
theorem regular_bounded_mono {edges : List ClearSheetContinuation.Subdivision.ParameterEdge} (bank : ParentBank.Bank
  regular data edges) {small large : InverseRootPolynomial.Coordinate}
    (bounded : RegularBounded bank small) (order : small ≤
      large) : RegularBounded bank large := by
  induction bank with
  | nil => trivial
  | cons head tail ih => exact ⟨bounded.1.trans order, ih bounded.2⟩

/-- The original regular comparison bank's computed maximum is nonnegative. -/
theorem regularMaximum_nonnegative {edges : List ClearSheetContinuation.Subdivision.ParameterEdge} (bank :
  ParentBank.Bank regular data edges) : 0 ≤ regularMaximum
  bank := by
  cases bank with
  | nil => exact le_rfl
  | cons head tail =>
    exact (RegularComparison.Data.regularScale_nonnegative head).trans (Fraction.Order.Basic.le_max_left _ _)

/-- The computed original regular maximum bounds every retained cell comparison scale. -/
theorem regularMaximum_bounded {edges : List ClearSheetContinuation.Subdivision.ParameterEdge} (bank : ParentBank.Bank
  regular data edges) : RegularBounded bank
  (regularMaximum bank) := by
  induction bank with
  | nil => trivial
  | cons head tail ih =>
    exact ⟨Fraction.Order.Basic.le_max_left _ _,
      regular_bounded_mono tail ih
      (Fraction.Order.Basic.le_max_right _ _)⟩

end RegularCells.Bank

namespace RegularCells.Budget

/-- A paid original regular comparison scale is bounded by the retained parent area budget. -/
theorem regular_areaScale_le (budget : ParentBank.Budget data) {edge : ClearSheetContinuation.Subdivision.ParameterEdge}
  {cell : UniformReciprocalCover.Cell data edge}
    (comparison : ArcSamples.Data regular cell) (bounded : (RegularComparison.Data.regularScale comparison) ≤
      budget.scale) :
    (RegularArea.Data.regularAreaScale comparison) ≤ budget.areaScale := by
  rw [RegularArea.Data.regularAreaScale, budget.areaScale_eq, budget.slope_eq]
  exact Fraction.Order.Arithmetic.mul_le_mul_direct bounded
    (add_le_add le_rfl (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct bounded (by decide +kernel)))
    (add_nonneg (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel) data.sourceSlope_nonnegative)
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel) (RegularComparison.Data.regularScale_nonnegative
        comparison))) budget.nonnegative

end RegularCells.Budget

namespace RegularCells

set_option genInjectivity false in
/-- The original compared cell with a cached signed shared-cap path and its endpoint values.

The actual retained source primitive and inverse sample remain unchanged; the shared primitive's sign and exact path
summary are stored together. -/
structure RegularCell (retained : ParentCells.ComparedCell comparison source capSample depth) where
  /-- The retained sheet sign aligning the original sample with the shared cap primitive. -/ alignment :
    SheetAlignment.RegularAlignment retained.sample
  /-- The cached signed primitive value at the original first cell endpoint. -/ firstValue :
    InverseRootPolynomial.Gaussian
  /-- The first value evaluates the actual retained signed primitive at the reciprocal left endpoint. -/ firstValue_eq :
    firstValue = alignment.primitive.eval (parent.edge.point edge.left.parameter)⁻¹
  /-- The cached signed primitive value at the original last cell endpoint. -/ lastValue :
    InverseRootPolynomial.Gaussian
  /-- The last value evaluates the actual retained signed primitive at the reciprocal right endpoint. -/ lastValue_eq :
    lastValue = alignment.primitive.eval (parent.edge.point edge.right.parameter)⁻¹
  /-- The cached original signed-cap endpoint difference. -/ increment : InverseRootPolynomial.Gaussian
  /-- The cached increment is exactly the original last signed value minus the first. -/ increment_eq : increment =
    lastValue - firstValue
  /-- The cached original finite dyadic signed-cap increment path. -/ capPath : List InverseRootPolynomial.Gaussian
  /-- The retained path consists exactly of the original signed cap value's dyadic increments. -/ capPath_eq : capPath =
    DyadicPrimitivePaths.dyadicIncrements (RegularAlignment.capValue alignment) depth edge.left.parameter
    edge.right.parameter
  /-- The cached total and area certificate for the original signed-cap path. -/ capSummary : IncrementArea.Summary
    capPath

constructive_injectivity RegularCell

end RegularCells

namespace RegularCells.RegularCell

variable {retained : ComparedCell comparison source
  capSample depth}

/-- Reuse the original compared cells and cache their signed shared-cap endpoint values and finite increment paths. -/
@[expose] def build (retained : ParentCells.ComparedCell comparison source capSample depth)
    (regularChart : HyperellipticReciprocal.originOrder curve = 0) :
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularCells.RegularCell retained := by
  let alignment := RegularAlignment.build retained.sample regularChart
  let firstValue := alignment.primitive.eval (parent.edge.point edge.left.parameter)⁻¹
  let lastValue := alignment.primitive.eval (parent.edge.point edge.right.parameter)⁻¹
  let capPath := DyadicPrimitivePaths.dyadicIncrements (fun parameter => alignment.primitive.eval (parent.edge.point
    parameter)⁻¹ - firstValue)
    depth edge.left.parameter edge.right.parameter
  exact ⟨alignment, firstValue, rfl, lastValue, rfl, lastValue - firstValue, rfl, capPath, rfl,
    IncrementArea.Summary.build capPath⟩

/-- The cached original regular increment is exactly the signed shared primitive's cell increment. -/
theorem increment_spec (compared : Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularCells.RegularCell retained) :
  compared.increment = (RegularAlignment.increment compared.alignment) := by
  rw [compared.increment_eq, compared.firstValue_eq, compared.lastValue_eq]
  rfl

/-- The retained regular-cap path total is exactly its original cached endpoint increment. -/
theorem cap_total (compared : Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularCells.RegularCell retained) :
  compared.capSummary.total = compared.increment := by
  rw [compared.capSummary.total_eq, compared.capPath_eq, DyadicPrimitivePaths.dyadicIncrements_sum,
    RegularAlignment.capValue_left compared.alignment, Data.Gaussian.Basic.sub_zero, RegularAlignment.capValue_right
      compared.alignment, compared.increment_spec]

/-- The retained regular-cap path area is the finite dyadic area of its original signed primitive. -/
theorem cap_area (compared : Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularCells.RegularCell retained) :
    compared.capSummary.area = DyadicBoundaryRibbon.dyadicArea (RegularAlignment.capValue compared.alignment) depth
      edge.left.parameter edge.right.parameter := by
  rw [compared.capSummary.area_eq, compared.capPath_eq]
  exact DyadicPrimitivePaths.pathArea_dyadicIncrements _ _ _ _ (RegularAlignment.capValue_left compared.alignment)

/-- The original source and signed-cap totals satisfy the retained regular comparison scale times squared width. -/
theorem total_error (compared : Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularCells.RegularCell retained) :
    Data.Gaussian.Norm.Basic.normSq (retained.original.left.total - compared.capSummary.total) ≤
      Geometric.Basic.quarterRadius (RegularComparison.Data.regularScale comparison) index * (edge.right.parameter -
        edge.left.parameter) ^ 2 := by
  rw [retained.original.left_total, compared.cap_total, compared.increment_spec]
  have bound := RegularAlignment.comparison_error compared.alignment source ⟨le_rfl, cell.ordered.le⟩ ⟨cell.ordered.le,
    le_rfl⟩
  have same : source.increment edge - (RegularAlignment.increment compared.alignment) =
      RegularAlignment.comparisonValue compared.alignment source edge.right.parameter -
        RegularAlignment.comparisonValue compared.alignment source edge.left.parameter := by
    dsimp only [SourcePrimitive.increment,
      RegularAlignment.increment, RegularAlignment.comparisonValue]
    ring1
  rw [same]
  exact bound

/-- The original source and signed-cap areas satisfy the retained regular area scale times fourth-power width. -/
theorem area_error (compared : Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularCells.RegularCell retained) :
    Data.Gaussian.Norm.Basic.normSq (retained.original.left.area - compared.capSummary.area) ≤
      Geometric.Basic.quarterRadius (RegularArea.Data.regularAreaScale comparison) index * (edge.right.parameter -
        edge.left.parameter) ^ 4 := by
  rw [retained.original.left_area, compared.cap_area]
  exact RegularAlignment.area_error_geometric source compared.alignment depth

/-- The original signed-cap total satisfies its retained source slope and regular discrepancy bound. -/
theorem cap_bound (compared : Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularCells.RegularCell retained) :
    Data.Gaussian.Norm.Basic.normSq compared.capSummary.total ≤ 2 * (data.sourceSlope +
      Geometric.Basic.quarterRadius (RegularComparison.Data.regularScale comparison) index) *
      (edge.right.parameter - edge.left.parameter) ^ 2 := by
  rw [compared.cap_total, compared.increment_spec]
  have bound := RegularAlignment.cap_increment_bound source compared.alignment ⟨le_rfl, cell.ordered.le⟩
    ⟨cell.ordered.le, le_rfl⟩
  rw [RegularAlignment.capValue_left compared.alignment, Data.Gaussian.Basic.sub_zero, RegularAlignment.capValue_right
    compared.alignment] at bound
  exact bound

/-- Transport the original signed-cap total discrepancy to the retained shared parent budget. -/
theorem total_error_budget (compared : Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularCells.RegularCell retained)
  (budget : ParentBank.Budget data)
    (bounded : (RegularComparison.Data.regularScale comparison) ≤ budget.scale) :
    Data.Gaussian.Norm.Basic.normSq (retained.original.left.total - compared.capSummary.total) ≤
      Geometric.Basic.quarterRadius budget.scale index * (edge.right.parameter - edge.left.parameter) ^ 2 :=
  compared.total_error.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
    (ParentBank.quarterRadius_mono bounded index) (Fraction.Order.Arithmetic.sq_nonneg_direct _))

/-- Transport the original signed-cap area discrepancy to the retained shared parent area budget. -/
theorem area_error_budget (compared : Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularCells.RegularCell retained)
  (budget : ParentBank.Budget data)
    (bounded : (RegularComparison.Data.regularScale comparison) ≤ budget.scale) :
    Data.Gaussian.Norm.Basic.normSq (retained.original.left.area - compared.capSummary.area) ≤
      Geometric.Basic.quarterRadius budget.areaScale index * (edge.right.parameter - edge.left.parameter) ^ 4 :=
  compared.area_error.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
    (ParentBank.quarterRadius_mono (Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularCells.Budget.regular_areaScale_le
      budget comparison bounded) index)
    (Fraction.Order.Arithmetic.pow_nonneg_direct (Fraction.Order.Arithmetic.sub_nonneg_direct cell.ordered.le) 4))

/-- The original source total remains bounded by the retained parent slope and actual cell width. -/
theorem left_bound (_compared : Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularCells.RegularCell retained) (budget :
  ParentBank.Budget data) :
    Data.Gaussian.Norm.Basic.normSq retained.original.left.total ≤ budget.slope * (edge.right.parameter -
      edge.left.parameter) ^ 2 := by
  rw [budget.slope_eq]
  exact retained.original.left_bound

/-- The actual signed-cap total satisfies the retained common parent slope and discrepancy budget. -/
theorem cap_bound_budget (compared : Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularCells.RegularCell retained)
  (budget : ParentBank.Budget data)
    (bounded : (RegularComparison.Data.regularScale comparison) ≤ budget.scale) :
    Data.Gaussian.Norm.Basic.normSq compared.capSummary.total ≤ 2 * (budget.slope +
      Geometric.Basic.quarterRadius budget.scale index) *
      (edge.right.parameter - edge.left.parameter) ^ 2 := by
  rw [budget.slope_eq]
  exact compared.cap_bound.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (add_le_add le_rfl (ParentBank.quarterRadius_mono bounded index)) (by decide))
    (Fraction.Order.Arithmetic.sq_nonneg_direct _))

end RegularCells.RegularCell

-- Preserve the original RegularCells.RegularCells nominal path.
set_option genInjectivity false in
/-- A dependent bank of signed regular-cap paths indexed by the exact original compared-cell spine. -/
inductive RegularCells : {edges : List ClearSheetContinuation.Subdivision.ParameterEdge} → {bank : ParentBank.Bank
  regular data edges} →
    ParentPaths.ComparedCells source capSample depth bank → Type
  /-- The empty original compared-cell spine has no signed regular-cap cells. -/ | nil :
    RegularCells .nil
  /-- Prepend the signed shared-cap path of one original compared cell to the retained tail. -/ | cons {edge :
    ClearSheetContinuation.Subdivision.ParameterEdge} {remaining : List
    ClearSheetContinuation.Subdivision.ParameterEdge} {cell : UniformReciprocalCover.Cell data edge}
      {comparison : ArcSamples.Data regular cell} {bank : ParentBank.Bank regular data remaining}
      {head : ParentCells.ComparedCell comparison source capSample depth} {tail : ParentPaths.ComparedCells source
        capSample depth bank}
      (first : Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularCells.RegularCell head) (rest :
        RegularCells tail) :
        RegularCells (.cons head tail)

constructive_injectivity RegularCells

namespace RegularCells

-- Preserve the original RegularCells.RegularCells nominal path.
/-- Reuse the original compared cells and cache their signed shared-cap endpoint values and finite increment paths. -/
@[expose] def build (regularChart : HyperellipticReciprocal.originOrder curve = 0) :
    {edges : List ClearSheetContinuation.Subdivision.ParameterEdge} → {bank : ParentBank.Bank regular data edges} →
    (retained : ParentPaths.ComparedCells source capSample depth bank) →
      RegularCells retained
  | _, _, .nil => .nil
  | _, _, .cons head tail => .cons (Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularCells.RegularCell.build head
    regularChart) (build regularChart
    tail)

-- Preserve the original RegularCells.RegularCells nominal path.
/-- Read each original source path and its actual signed regular-cap path in retained cell order. -/
@[expose] def pairs : {edges : List ClearSheetContinuation.Subdivision.ParameterEdge} → {bank : ParentBank.Bank regular
  data edges} →
    {retained : ParentPaths.ComparedCells source capSample depth bank} →
      RegularCells retained → List (List
      InverseRootPolynomial.Gaussian × List InverseRootPolynomial.Gaussian)
  | _, _, _, .nil => []
  | _, _, _, @cons _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    _ _ _ _ head _ first rest =>
      (head.original.leftPath, first.capPath) :: rest.pairs

-- Preserve the original RegularCells.RegularCells nominal path.
/-- There is one retained source-to-regular-cap path pair per original covered edge. -/
theorem pairs_length {edges : List ClearSheetContinuation.Subdivision.ParameterEdge} {bank : ParentBank.Bank regular
  data edges} {retained : ParentPaths.ComparedCells source capSample depth bank} (cells :
  RegularCells retained) :
    cells.pairs.length = edges.length := by
  induction cells with
  | nil => rfl
  | cons _ _ ih => exact congrArg Nat.succ ih

-- Preserve the original RegularCells.RegularCells nominal path.
/-- Append the cached original source path summaries with their exact cross terms. -/
@[expose] def leftSummary : {edges : List ClearSheetContinuation.Subdivision.ParameterEdge} → {bank : ParentBank.Bank
  regular data edges} → {retained : ParentPaths.ComparedCells source capSample depth bank} →
    (cells : RegularCells retained) → IncrementArea.Summary
      (cells.pairs.map Prod.fst).flatten
  | _, _, _, .nil => IncrementArea.Summary.build []
  | _, _, .cons originalHead _, .cons _ tail => originalHead.original.left.append tail.leftSummary

-- Preserve the original RegularCells.RegularCells nominal path.
/-- Append the cached signed regular-cap path summaries with their exact cross terms. -/
@[expose] def capSummary : {edges : List ClearSheetContinuation.Subdivision.ParameterEdge} → {bank : ParentBank.Bank
  regular data edges} → {retained : ParentPaths.ComparedCells source capSample depth bank} →
    (cells : RegularCells retained) → IncrementArea.Summary
      (cells.pairs.map Prod.snd).flatten
  | _, _, _, .nil => IncrementArea.Summary.build []
  | _, _, _, .cons head tail => head.capSummary.append tail.capSummary

-- Preserve the original RegularCells.RegularCells nominal path.
/-- The signed regular-cap bank preserves exactly the original source path list. -/
theorem left_paths {edges : List ClearSheetContinuation.Subdivision.ParameterEdge} {bank : ParentBank.Bank regular data
  edges} {retained : ParentPaths.ComparedCells source capSample depth bank} (cells :
  RegularCells retained) :
    cells.pairs.map Prod.fst = retained.pairs.map Prod.fst := by
  induction cells with
  | nil => rfl
  | @cons edge remaining cell comparison bank originalHead originalTail head tail ih =>
    exact congrArg (List.cons originalHead.original.leftPath) ih

-- Preserve the original RegularCells.RegularCells nominal path.
/-- The retained original source total is exactly its endpoint primitive difference. -/
theorem source_total (mesh : UniformReciprocalCover.Mesh data) {bank : ParentBank.Bank regular data mesh.edges}
  {retained : ParentPaths.ComparedCells source capSample depth bank} (cells :
  RegularCells retained) :
    cells.leftSummary.total = source.primitive.value.eval (parent.edge.point 1) - source.primitive.value.eval
      (parent.edge.point 0) := by
  rw [cells.leftSummary.total_eq, cells.left_paths, ← retained.leftSummary.total_eq]
  exact retained.source_total mesh

-- Preserve the original RegularCells.RegularCells nominal path.
/-- The retained original source area is its actual finite dyadic area at the combined depths. -/
theorem source_area (mesh : UniformReciprocalCover.Mesh data) {bank : ParentBank.Bank regular data mesh.edges} {retained
  : ParentPaths.ComparedCells source capSample depth bank} (cells :
  RegularCells retained) :
    cells.leftSummary.area = DyadicBoundaryRibbon.dyadicArea
      (fun parameter => source.primitive.value.eval (parent.edge.point parameter) - source.primitive.value.eval
        (parent.edge.point 0))
      (mesh.depth + depth) 0 1 := by
  rw [cells.leftSummary.area_eq, cells.left_paths, ← retained.leftSummary.area_eq]
  exact retained.source_area mesh

-- Preserve the original RegularCells.RegularCells nominal path.
/-- Read the original source-minus-signed-cap total discrepancy of each retained cell. -/
@[expose] def errors : {edges : List ClearSheetContinuation.Subdivision.ParameterEdge} → {bank : ParentBank.Bank regular
  data edges} → {retained : ParentPaths.ComparedCells source capSample depth bank} →
    RegularCells retained → List InverseRootPolynomial.Gaussian
  | _, _, _, .nil => []
  | _, _, .cons originalHead _, .cons head tail => (originalHead.original.left.total - head.capSummary.total) ::
    tail.errors

-- Preserve the original RegularCells.RegularCells nominal path.
/-- Read the cached signed regular-cap increment of each original cell. -/
@[expose] def increments : {edges : List ClearSheetContinuation.Subdivision.ParameterEdge} → {bank : ParentBank.Bank
  regular data edges} → {retained : ParentPaths.ComparedCells source capSample depth bank} →
    RegularCells retained → List InverseRootPolynomial.Gaussian
  | _, _, _, .nil => []
  | _, _, _, .cons head tail => head.increment :: tail.increments

-- Preserve the original RegularCells.RegularCells nominal path.
/-- The original complete signed-cap path total is the sum of its retained cell increments. -/
theorem cap_total {edges : List ClearSheetContinuation.Subdivision.ParameterEdge} {bank : ParentBank.Bank regular data
  edges} {retained : ParentPaths.ComparedCells source capSample depth bank} (cells :
  RegularCells retained) :
    cells.capSummary.total = Data.Gaussian.Norm.Sum.Basic.gaussianSum cells.increments := by
  induction cells with
  | nil => rfl
  | @cons edge remaining cell comparison bank originalHead originalTail head tail ih =>
      change head.capSummary.total + tail.capSummary.total = head.increment +
        Data.Gaussian.Norm.Sum.Basic.gaussianSum tail.increments
      rw [head.cap_total, ih]

-- Preserve the original RegularCells.RegularCells nominal path.
/-- There is one retained regular-cap discrepancy per original covered edge. -/
theorem errors_length {edges : List ClearSheetContinuation.Subdivision.ParameterEdge} {bank : ParentBank.Bank regular
  data edges} {retained : ParentPaths.ComparedCells source capSample depth bank} (cells :
  RegularCells retained) :
    cells.errors.length = edges.length := by
  induction cells with
  | nil => rfl
  | cons _ _ ih => exact congrArg Nat.succ ih

-- Preserve the original RegularCells.RegularCells nominal path.
/-- The original retained cell discrepancies sum to the source total minus the signed-cap total. -/
theorem errors_sum {edges : List ClearSheetContinuation.Subdivision.ParameterEdge} {bank : ParentBank.Bank regular data
  edges} {retained : ParentPaths.ComparedCells source capSample depth bank} (cells :
  RegularCells retained) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum cells.errors = cells.leftSummary.total - cells.capSummary.total := by
  induction cells with
  | nil => change (0 : InverseRootPolynomial.Gaussian) = 0 - 0; ring1
  | @cons edge remaining cell comparison bank originalHead originalTail head tail ih =>
      change (originalHead.original.left.total - head.capSummary.total) + Data.Gaussian.Norm.Sum.Basic.gaussianSum
        tail.errors =
        (originalHead.original.left.total + tail.leftSummary.total) - (head.capSummary.total + tail.capSummary.total)
      rw [ih]
      ring1

end RegularCells
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk
