module
meta import Purelib.Elab.ConstructiveInjectivity
public import Purelib.Data.Nat.Addition
import Purelib.Data.Nat.Order
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBank
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentComparison
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentPaths
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularCells
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularEstimates
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularParent
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalBoundaryArea
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives
import Purelib.Integration.Path.Dyadic.DyadicBoundaryRibbon
import Purelib.Integration.Path.IncrementArea
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularEndpoints
import Init.Data.Nat.Basic
import Init.Data.Nat.MinMax
import Init.Prelude
import Mathlib.Data.Nat.Basic
import Mathlib.Order.Defs.PartialOrder
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic
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
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBank
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularCells
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularEndpoints
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularEstimates
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularParent
open Purelib.Integration.Path
open Purelib.Integration.Path.Dyadic
open Purelib.Riemann.Normalization

/-!
# Requested regular-cap comparison consuming a prepared exterior parent

The finite maximum is cached before the shared stage is selected. Evaluation
consumes the existing compared cells, their source paths and retained root
joins. It returns the full shared-polynomial path with both requested errors.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularRequests

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate Polynomial)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover (Cover)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives (SourcePrimitive)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBank (Budget)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentPaths (ComparedCells)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularEndpoints (RegularEndpoint)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentComparison (Preparation Request)
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Integration.Path.IncrementArea (Summary)
open Purelib.Integration.Path.Dyadic.DyadicBoundaryRibbon (dyadicArea)
open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius)
open Purelib.Approximation.Rational.Geometric.Search (firstQuarterBelow)

variable {genus count : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {parent : Purelib.Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent} {data :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {cover :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Cover data}

set_option genInjectivity false in
/-- A cached shared-stage request for the complete regular cap-parent comparison.

The exact retained cell maximum pays separate total and area targets, with a stage of at least two to identify the
common signed cap primitive. -/
structure RegularRequest (prepared : ParentComparison.Preparation regular cover) (totalTarget areaTarget :
  InverseRootPolynomial.Coordinate) (floor : Nat) where
  /-- The reciprocal chart is regular at the origin. -/ regular_chart : HyperellipticReciprocal.originOrder curve = 0
  /-- The cached comparison budget on the exact original exterior parent. -/ budget : ParentBank.Budget data
  /-- The budget scale is the actual retained regular-cell maximum. -/ scale_eq : budget.scale = Bank.regularMaximum
    prepared.bank
  /-- The cached common polynomial stage for both error targets. -/ index : Nat
  /-- The stage is the maximum of the two finite quarter-radius searches above the caller floor and stage two. -/
    index_eq : index = max (Search.firstQuarterBelow budget.scale (max floor 2) totalTarget)
    (Search.firstQuarterBelow budget.boundaryAreaScale (max floor 2) areaTarget)
  /-- The common stage respects the original supplied floor. -/ floor_le : floor ≤ index
  /-- The common stage is at least two, as required by retained sign comparisons. -/ ready : 2 ≤ index
  /-- The cached whole-parent total-error bound. -/ totalError : InverseRootPolynomial.Coordinate
  /-- The total-error bound is exactly the retained scale's quarter radius. -/ totalError_eq : totalError =
    Geometric.Basic.quarterRadius budget.scale index
  /-- The retained total-error bound is below its requested target. -/ total_lt : totalError < totalTarget
  /-- The cached complete boundary-area error bound. -/ areaError : InverseRootPolynomial.Coordinate
  /-- The area-error bound is exactly the retained boundary scale's quarter radius. -/ areaError_eq : areaError =
    Geometric.Basic.quarterRadius budget.boundaryAreaScale index
  /-- The retained area-error bound is below its requested target. -/ area_lt : areaError < areaTarget

constructive_injectivity RegularRequest

namespace RegularRequest

/-- Cache the actual regular-cell budget and select one finite stage paying both complete-parent targets. -/
@[expose] def build (prepared : ParentComparison.Preparation regular cover) (regularChart :
  HyperellipticReciprocal.originOrder curve = 0)
    (totalTarget areaTarget : InverseRootPolynomial.Coordinate) (totalPositive : 0 < totalTarget) (areaPositive : 0 <
      areaTarget)
    (floor : Nat) : Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularRequests.RegularRequest prepared totalTarget
      areaTarget floor := by
  let budget := Budget.build data (Bank.regularMaximum prepared.bank)
    (Bank.regularMaximum_nonnegative prepared.bank)
  let totalIndex := Search.firstQuarterBelow budget.scale (max floor 2) totalTarget
  let areaIndex := Search.firstQuarterBelow budget.boundaryAreaScale (max floor 2) areaTarget
  let index := max totalIndex areaIndex
  have later : max floor 2 ≤ index :=
    (Search.firstQuarterBelow_ge budget.scale (max floor 2) totalTarget).trans (Data.Nat.Order.le_max_left _ _)
  exact ⟨regularChart, budget, rfl, index, rfl, (Data.Nat.Order.le_max_left _ _).trans later,
    (Data.Nat.Order.le_max_right _ _).trans later,
    Geometric.Basic.quarterRadius budget.scale index, rfl,
    (quarterRadius_antitone budget.nonnegative (Data.Nat.Order.le_max_left totalIndex areaIndex)).trans_lt
      (Search.firstQuarterBelow_accurate _ budget.nonnegative _ _ totalPositive),
    Geometric.Basic.quarterRadius budget.boundaryAreaScale index, rfl,
    (quarterRadius_antitone budget.boundaryAreaScale_nonnegative (Data.Nat.Order.le_max_right totalIndex
      areaIndex)).trans_lt
      (Search.firstQuarterBelow_accurate _ budget.boundaryAreaScale_nonnegative _ _ areaPositive)⟩

/-- Derive the regular reciprocal chart from the original even degree and construct its shared-stage comparison request.
-/
@[expose] def ofEvenDegree (prepared : ParentComparison.Preparation regular cover) (degree : curve.polynomial.natDegree
  = 2 * genus + 2)
    (totalTarget areaTarget : InverseRootPolynomial.Coordinate) (totalPositive : 0 < totalTarget) (areaPositive : 0 <
      areaTarget)
    (floor : Nat) : Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularRequests.RegularRequest prepared totalTarget
      areaTarget floor := by
  have balance := HyperellipticReciprocal.degree_balance curve
  rw [degree] at balance
  have chart : HyperellipticReciprocal.originOrder curve = 0 := Data.Nat.Addition.add_left_cancel (balance :
    (2 * genus + 2) + HyperellipticReciprocal.originOrder curve = (2 * genus + 2) + 0)
  exact Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularRequests.RegularRequest.build prepared chart totalTarget
    areaTarget totalPositive areaPositive floor

variable {prepared : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentComparison.Preparation regular cover}
  {totalTarget areaTarget : Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate} {floor index depth : Nat}
  {source : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives.SourcePrimitive data index} {box
    : Purelib.Geometry.Rational.Box}
  {capSample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}

set_option genInjectivity false in
/-- The retained regular-cell bank and complete source/cap summaries with a single shared signed polynomial. -/
structure Evaluation (request : Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularRequests.RegularRequest prepared
  totalTarget areaTarget floor)
    (retained : ParentPaths.ComparedCells source capSample depth prepared.bank) where
  /-- The cached regular alignments of the exact original comparison-cell spine. -/ cells : RegularCells
    retained
  /-- The original shared sample stage meets the retained request. -/ stage_later : request.index ≤ index
  /-- The cached complete original source-path summary. -/ left : IncrementArea.Summary (retained.pairs.map
    Prod.fst).flatten
  /-- The cached complete regular cap-path summary. -/ cap : IncrementArea.Summary (cells.pairs.map Prod.snd).flatten
  /-- The retained common signed cap polynomial. -/ primitive : InverseRootPolynomial.Polynomial
  /-- The common polynomial is exactly the primitive selected by the retained regular-cell bank. -/ primitive_eq :
    primitive = RegularCells.primitive cells
  /-- The original first endpoint view carries this exact shared polynomial. -/ first : RegularEndpoints.RegularEndpoint
    regular capSample prepared.boundary.first.point primitive
  /-- The original last endpoint view carries this exact shared polynomial. -/ last : RegularEndpoints.RegularEndpoint
    regular capSample prepared.boundary.last.point primitive
  /-- The actual complete source and cap totals meet the requested target. -/ total_close :
    Data.Gaussian.Norm.Basic.normSq (left.total - cap.total) < totalTarget
  /-- The actual complete source and cap areas meet the requested target. -/ area_close :
    Data.Gaussian.Norm.Basic.normSq (left.area - cap.area) < areaTarget
  /-- The cap total is exactly the shared polynomial's reciprocal-arc endpoint difference. -/ cap_total : cap.total =
    primitive.eval (parent.edge.point 1)⁻¹ - primitive.eval (parent.edge.point 0)⁻¹
  /-- The cap area is exactly the anchored dyadic area of the shared signed polynomial. -/ cap_area : cap.area =
    DyadicBoundaryRibbon.dyadicArea
    (fun parameter => primitive.eval (parent.edge.point parameter)⁻¹ - primitive.eval (parent.edge.point 0)⁻¹)
    (cover.mesh.depth + depth) 0 1
  /-- The cap area equals the original unsigned cap polynomial's anchored dyadic area. -/ cap_area_unsigned : cap.area =
    DyadicBoundaryRibbon.dyadicArea
    (fun parameter => capSample.primitive.value.eval (parent.edge.point parameter)⁻¹ -
      capSample.primitive.value.eval (parent.edge.point 0)⁻¹) (cover.mesh.depth + depth) 0 1

constructive_injectivity Evaluation

/-- The existing source and reciprocal cell records are the input. No root or primitive preparation is repeated to
explain the certified outcome. -/
@[expose] def evaluate (request : Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularRequests.RegularRequest prepared
  totalTarget areaTarget floor)
    (retained : ParentPaths.ComparedCells source capSample depth prepared.bank) (later : request.index ≤ index) :
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularRequests.RegularRequest.Evaluation request retained := by
  let cells := RegularCells.build request.regular_chart retained
  have bounded : Bank.RegularBounded prepared.bank request.budget.scale := by
    rw [request.scale_eq]
    exact Bank.regularMaximum_bounded prepared.bank
  have totalEq : retained.leftSummary.total = cells.leftSummary.total := by
    rw [retained.leftSummary.total_eq, cells.leftSummary.total_eq, cells.left_paths]
  have areaEq : retained.leftSummary.area = cells.leftSummary.area := by
    rw [retained.leftSummary.area_eq, cells.leftSummary.area_eq, cells.left_paths]
  have ready := request.ready.trans later
  refine ⟨cells, later, retained.leftSummary, cells.capSummary, RegularCells.primitive cells, rfl,
    RegularCells.boundaryFirst cover.mesh cells prepared.owners prepared.links prepared.boundary ready,
    RegularCells.boundaryLast cover.mesh cells prepared.owners prepared.links prepared.boundary ready, ?_, ?_,
    RegularCells.cap_total_eq cover.mesh cells prepared.owners prepared.links ready,
    RegularCells.cap_area_eq cover.mesh cells prepared.owners prepared.links ready,
    RegularCells.cap_area_unsigned cover.mesh cells prepared.owners prepared.links ready⟩
  · rw [totalEq]
    exact ((RegularCells.whole_total_error cover.mesh request.budget cells bounded).trans
      ((quarterRadius_antitone request.budget.nonnegative later).trans_eq
        request.totalError_eq.symm)).trans_lt
      request.total_lt
  · rw [areaEq]
    exact ((RegularCells.whole_area_error cover.mesh request.budget cells bounded).trans
      ((quarterRadius_antitone request.budget.boundaryAreaScale_nonnegative later).trans_eq
        request.areaError_eq.symm)).trans_lt
      request.area_lt

namespace Evaluation

variable {request : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularRequests.RegularRequest prepared
  totalTarget areaTarget floor}
  {retained : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentPaths.ComparedCells source capSample depth
    prepared.bank}

/-- The retained evaluation's actual sample stage is at least two. -/
theorem ready (evaluated : Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularRequests.RegularRequest.Evaluation request
  retained) : 2 ≤ index := request.ready.trans evaluated.stage_later

/-- The retained source total is the exact original polynomial endpoint difference. -/
theorem source_total (evaluated : Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularRequests.RegularRequest.Evaluation
  request retained) :
    evaluated.left.total = source.primitive.value.eval (parent.edge.point 1) - source.primitive.value.eval
      (parent.edge.point 0) := by
  rw [evaluated.left.total_eq, ← retained.leftSummary.total_eq]
  exact retained.source_total cover.mesh

/-- The retained source area is the original polynomial's anchored dyadic area at the combined depth. -/
theorem source_area (evaluated : Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularRequests.RegularRequest.Evaluation
  request retained) :
    evaluated.left.area = DyadicBoundaryRibbon.dyadicArea
      (fun parameter => source.primitive.value.eval (parent.edge.point parameter) - source.primitive.value.eval
        (parent.edge.point 0))
      (cover.mesh.depth + depth) 0 1 := by
  rw [evaluated.left.area_eq, ← retained.leftSummary.area_eq]
  exact retained.source_area cover.mesh

end Evaluation
end RegularRequest

namespace Request.Evaluation

variable {prepared : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentComparison.Preparation regular cover}
  {totalTarget areaTarget : Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate} {floor depth : Nat}
  {originalTarget : Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate} {original :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalBoundaryArea.Cover.AreaRequest cover depth originalTarget}
  {box : Purelib.Geometry.Rational.Box} {capSample :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential original.index box}
  {request : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentComparison.Request prepared totalTarget
    areaTarget floor}

/-- Consume the cell bank already retained by the existing parent request. The regular request chooses its sufficient
shared stage before evaluation. -/
@[expose] def withRegularCap (evaluated : ParentComparison.Request.Evaluation request original capSample)
    {regularTotal regularArea : InverseRootPolynomial.Coordinate} {regularFloor : Nat}
    (requested : Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularRequests.RegularRequest prepared regularTotal
      regularArea regularFloor)
    (later : requested.index ≤ original.index) :
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularRequests.RegularRequest.Evaluation requested evaluated.cells :=
  requested.evaluate evaluated.cells later

end Request.Evaluation
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularRequests
