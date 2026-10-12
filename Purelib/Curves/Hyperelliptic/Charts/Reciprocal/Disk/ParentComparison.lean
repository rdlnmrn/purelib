module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Nat.Order
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentPaths
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalBoundaryArea
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Integration.Path.Dyadic.DyadicBoundaryRibbon
import Purelib.Integration.Path.IncrementArea
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentEstimates
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners
import Init.Data.Nat.MinMax
import Init.Prelude
import Mathlib.Data.Nat.Basic
import Mathlib.Order.Defs.PartialOrder
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Riemann.Normalization.OwnerSeededInverseRoot

public section

open Purelib
open Purelib.Approximation.Rational
open Purelib.Approximation.Rational.Geometric
open Purelib.Approximation.Rational.Geometric.Basic
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBank
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentEstimates
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners.Owners
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentPaths
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalBoundaryArea
open Purelib.Integration.Path
open Purelib.Integration.Path.Dyadic
open Purelib.Riemann.Normalization

/-!
# Certified cap comparison for a complete retained exterior parent

Prepare the bank and both numerical budgets before selecting a shared
polynomial stage. Evaluation consumes an actual retained reciprocal area
request, preserves its complete source summary, and builds the matching cap
path once. The full integral and area bounds hold at every fine depth.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentComparison

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover (Cover)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBank (Bank Budget)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners (Owners)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentPaths (ComparedCells)
open Purelib.Data.Gaussian.Basic.Canonical
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Integration.Path.IncrementArea (Summary)
open Purelib.Integration.Path.Dyadic.DyadicBoundaryRibbon (dyadicArea)
open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius)
open Purelib.Approximation.Rational.Geometric.Search (firstQuarterBelow)

variable {genus count : Nat} {curve : HyperellipticCurve genus} {differential :
  Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {parent : Purelib.Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent} {data :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {cover :
    Cover data}

set_option genInjectivity false in
/-- Cached original comparison cells, endpoint owners and joins for one complete exterior parent.

The retained numerical budget uses the actual cell-bank maximum, and the boundary views refer to the exact original
owner spine. -/
structure Preparation (regular : RegularBounds.Data cap) (cover : UniformReciprocalCover.Cover data) where
  /-- The original comparison bank indexed by the complete retained cover mesh. -/ bank : ParentBank.Bank regular data
    cover.mesh.edges
  /-- The cached endpoint owners of these exact original comparison cells. -/ owners : ParentOwners.Owners bank
  /-- The cached operational coordinate joins between the original adjacent endpoint owners. -/ links : Owners.Links
    owners
  /-- The exact first and last endpoint views of the original retained owner bank. -/ boundary : Owners.Boundary
    cover.mesh owners
  /-- The cached numerical comparison budget for the original full parent. -/ budget : ParentBank.Budget data
  /-- The retained budget scale is exactly the original comparison bank's maximum. -/ scale_eq : budget.scale =
    bank.maximum

constructive_injectivity Preparation

namespace Preparation

/-- Prepare the original comparison bank and select a shared polynomial stage paying its separate total and area
targets. -/
@[expose] def build (regular : RegularBounds.Data cap) (cover : UniformReciprocalCover.Cover data) :
  Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentComparison.Preparation regular cover :=
  let bank := Bank.build regular cover.cells
  let owners := Owners.build bank
  ⟨bank, owners, Links.build cover.mesh owners, Boundary.build cover.mesh owners,
    Budget.build data bank.maximum bank.maximum_nonnegative, rfl⟩

/-- The retained parent budget bounds every actual original cell comparison scale. -/
theorem bounded (prepared : Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentComparison.Preparation regular cover) :
  prepared.bank.Bounded prepared.budget.scale := by
  rw [prepared.scale_eq]
  exact prepared.bank.maximum_bounded

end Preparation

set_option genInjectivity false in
/-- A cached shared-stage request paying the original complete parent's total and area discrepancies. -/
structure Request (prepared : Preparation regular cover)
  (totalTarget areaTarget : InverseRootPolynomial.Coordinate) (floor : Nat) where
  /-- The cached common polynomial stage paying both original discrepancy targets. -/ index : Nat
  /-- The stage is the maximum of the original total and full-area quarter-radius searches. -/ index_eq : index = max
    (Search.firstQuarterBelow prepared.budget.scale floor totalTarget)
    (Search.firstQuarterBelow prepared.budget.boundaryAreaScale floor areaTarget)
  /-- The retained common stage respects the caller's original floor. -/ floor_le : floor ≤ index
  /-- The cached original whole-total discrepancy at the selected stage. -/ totalError :
    InverseRootPolynomial.Coordinate
  /-- The total discrepancy is exactly the retained comparison scale's quarter-radius. -/ totalError_eq : totalError =
    Geometric.Basic.quarterRadius prepared.budget.scale index
  /-- The retained whole-total discrepancy is strictly below the original total target. -/ total_lt : totalError <
    totalTarget
  /-- The cached original whole-area discrepancy at the selected stage. -/ areaError : InverseRootPolynomial.Coordinate
  /-- The area discrepancy is exactly the retained full-boundary area scale's quarter-radius. -/ areaError_eq :
    areaError = Geometric.Basic.quarterRadius prepared.budget.boundaryAreaScale index
  /-- The retained whole-area discrepancy is strictly below the original area target. -/ area_lt : areaError <
    areaTarget

constructive_injectivity Request

namespace Request

/-- Prepare the original comparison bank and select a shared polynomial stage paying its separate total and area
targets. -/
@[expose] def build (prepared : Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentComparison.Preparation regular cover)
  (totalTarget areaTarget : InverseRootPolynomial.Coordinate)
    (totalPositive : 0 < totalTarget) (areaPositive : 0 < areaTarget) (floor : Nat) :
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentComparison.Request prepared totalTarget areaTarget floor :=
  let totalIndex := Search.firstQuarterBelow prepared.budget.scale floor totalTarget
  let areaIndex := Search.firstQuarterBelow prepared.budget.boundaryAreaScale floor areaTarget
  let index := max totalIndex areaIndex
  ⟨index, rfl, (Search.firstQuarterBelow_ge _ _ _).trans (Data.Nat.Order.le_max_left _ _),
    Geometric.Basic.quarterRadius prepared.budget.scale index, rfl,
    (quarterRadius_antitone prepared.budget.nonnegative (Data.Nat.Order.le_max_left totalIndex
      areaIndex)).trans_lt
      (Search.firstQuarterBelow_accurate _ prepared.budget.nonnegative _ _ totalPositive),
    Geometric.Basic.quarterRadius prepared.budget.boundaryAreaScale index, rfl,
    (quarterRadius_antitone prepared.budget.boundaryAreaScale_nonnegative (Data.Nat.Order.le_max_right
      totalIndex areaIndex)).trans_lt
      (Search.firstQuarterBelow_accurate _ prepared.budget.boundaryAreaScale_nonnegative _ _ areaPositive)⟩

variable {prepared : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentComparison.Preparation regular cover}
  {totalTarget areaTarget : Coordinate} {floor depth : Nat}
  {originalTarget : Coordinate} {original :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalBoundaryArea.Cover.AreaRequest cover depth originalTarget}
  {box : Purelib.Geometry.Rational.Box} {capSample :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential original.index box}

set_option genInjectivity false in
/-- The actual original reciprocal area request with its cached cap comparison path.

The original source cell spine and summary are retained exactly, and both complete path discrepancies satisfy their
requested targets. -/
structure Evaluation (request : Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentComparison.Request prepared
  totalTarget areaTarget floor)
    (original : Cover.AreaRequest cover depth originalTarget)
    (capSample : Primitives.Sample cap differential original.index box) where
  /-- The actual original source cells with their retained cap comparison paths. -/ cells : ParentPaths.ComparedCells
    original.source capSample depth prepared.bank
  /-- The comparison bank retains exactly the original reciprocal area-cell spine. -/ original_eq : cells.original =
    original.cells
  /-- The cached original source path summary. -/ left : IncrementArea.Summary (original.cells.pairs.map
    Prod.fst).flatten
  /-- The source summary is exactly the original area request's retained left summary. -/ left_eq : left = original.left
  /-- The cached complete cap path summary for these exact original compared cells. -/ cap : IncrementArea.Summary
    (cells.pairs.map Prod.snd).flatten
  /-- The actual retained source and cap totals satisfy the original requested target. -/ total_close :
    Data.Gaussian.Norm.Basic.normSq (left.total - cap.total) < totalTarget
  /-- The actual retained source and cap areas satisfy the original requested target. -/ area_close :
    Data.Gaussian.Norm.Basic.normSq (left.area - cap.area) < areaTarget

constructive_injectivity Evaluation

/-- Preserve the original paths and inverse caches. The caller's shared stage need only be at least the stage certified
by this request. -/
@[expose] def evaluate (request : Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentComparison.Request prepared
  totalTarget areaTarget floor)
    (original : Cover.AreaRequest cover depth originalTarget)
    (capSample : Primitives.Sample cap differential original.index box)
    (later : request.index ≤ original.index) :
      Evaluation request original capSample := by
  let cells := ComparedCells.build capSample prepared.bank original.cells
  have originals : cells.original = original.cells := ComparedCells.build_original _ _
  have totals : original.left.total = cells.leftSummary.total := by
    rw [original.left.total_eq, cells.leftSummary.total_eq, cells.left_paths, originals]
  have areas : original.left.area = cells.leftSummary.area := by
    rw [original.left.area_eq, cells.leftSummary.area_eq, cells.left_paths, originals]
  refine ⟨cells, originals, original.left, rfl, cells.capSummary, ?_, ?_⟩
  · rw [totals]
    exact ((ComparedCells.whole_total_error cover.mesh prepared.budget cells prepared.bounded).trans
      ((quarterRadius_antitone prepared.budget.nonnegative later).trans_eq
        request.totalError_eq.symm)).trans_lt
        request.total_lt
  · rw [areas]
    exact ((ComparedCells.whole_area_error cover.mesh prepared.budget cells prepared.bounded).trans
      ((quarterRadius_antitone prepared.budget.boundaryAreaScale_nonnegative later).trans_eq
        request.areaError_eq.symm)).trans_lt
        request.area_lt

namespace Evaluation

variable {request : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentComparison.Request prepared totalTarget
  areaTarget floor}

/-- The retained original source total is its actual endpoint primitive difference. -/
theorem source_total (evaluated : Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentComparison.Request.Evaluation
  request original capSample) :
    evaluated.left.total = original.source.primitive.value.eval (parent.edge.point 1) -
      original.source.primitive.value.eval (parent.edge.point 0) := by
  rw [evaluated.left_eq]
  exact original.source_total

/-- The retained original source area is the exact finite dyadic area at the combined cover and cell depth. -/
theorem source_area (evaluated : Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentComparison.Request.Evaluation request
  original capSample) :
    evaluated.left.area = DyadicBoundaryRibbon.dyadicArea
      (fun parameter => original.source.primitive.value.eval (parent.edge.point parameter) -
        original.source.primitive.value.eval (parent.edge.point 0))
      (cover.mesh.depth + depth) 0 1 := by
  rw [evaluated.left_eq]
  exact original.source_area

/-- The area path has precisely the sum of the retained cap-polynomial increments. Reading this total does not
reevaluate a primitive endpoint. -/
theorem cap_total (evaluated : Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentComparison.Request.Evaluation request
  original capSample) :
    evaluated.cap.total = Data.Gaussian.Norm.Sum.Basic.gaussianSum evaluated.cells.increments := by
  rw [evaluated.cap.total_eq, ← evaluated.cells.capSummary.total_eq]
  exact evaluated.cells.cap_total

end Evaluation
end Request
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentComparison
