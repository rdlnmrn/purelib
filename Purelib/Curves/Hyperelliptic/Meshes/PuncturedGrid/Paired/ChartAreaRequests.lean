module
import Purelib.Data.Nat.Order
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Rational.Budget.Weighted
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.EdgeMagnitude
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Decide
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts
public import Purelib.Integration.Path.PairedAreaComparison

import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.WordObservations

import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SourceChartRequests
import Purelib.Integration.Path.PairedIncrementComparison
import Init.Data.List.Basic
import Init.Data.List.Lemmas
import Init.Data.Nat.MinMax
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OwnedPuncturedMesh
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.SourceChartComparison
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.PrimitiveAreaBounds
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.PrimitiveJumps
import Purelib.Tactic.Ring

public section

/-! Requested comparison of paired source increments with the actual
projected edge increments, for the original-region sewing comparison. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.ChartAreaRequests

open Purelib
open Purelib.Approximation.Rational.Budget
open Purelib.Curves.Hyperelliptic
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.EdgeMagnitude
open Purelib.Data.List
open Purelib.Data.Rat
open Purelib.Integration.Path
open Purelib.Integration.Path.PairedAreaComparison
open Purelib.Topology.Surface.Sewing

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Topology.Polygon.Stokes (PrimitivePoint)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Riemann.Meshes (FramedPuncturedGrid)
open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedMesh)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank (FaceMagnitudeBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (FacePrimitiveBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid (SourceChartRequests)
open Purelib.Topology.Surface.Sewing.PrimitiveSewing (PrimitiveValues)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts (SourceEdge)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues (edgeValuation)
open Purelib.Riemann.Readings.PrimitiveAreaBounds.PrimitivePoint (Bounded)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Rat.Fraction.Compatibility

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames base.bank.grid} {vertices :
    Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank base.bank.grid}
  {edges : Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank frames} {mesh : LiftedMesh vertices edges
    base.faces}
  {domains : FaceDomainBank frames
    base.faces.regulars} {leftDifferential rightDifferential :
    Differential genus}

set_option genInjectivity false in
/-- The complete paired source/chart area request on one retained source occurrence list.

Both original differential magnitude banks pay a shared positive allowance while preserving the paired or conjugate
reading view. -/
structure PairedChartAreaRequest
    (leftFixed : FaceMagnitudeBank domains leftDifferential) (rightFixed : FaceMagnitudeBank domains rightDifferential)
    (sources : List (SewnPrimitiveContacts.SourceEdge mesh.triangles.length)) (target : Fraction.Rational) where
  /-- The original complete paired area target is strictly positive. -/ positive : 0 < target
  /-- The cached complete fourth-power occurrence and magnitude weight. -/ weight : Fraction.Rational
  /-- The weight is exactly the original occurrence-count expression with the maximum of both retained magnitudes. -/
    weight_eq : weight = 16 * (sources.length : Fraction.Rational)^4 * (8 * max leftFixed.bound rightFixed.bound + 2)
  /-- The cached common allowance used by both original differential requests. -/ allowance : Fraction.Rational
  /-- The allowance is the minimum of one and the original weighted target budget. -/ allowance_eq : allowance = min 1
    (Weighted.allowance target weight)
  /-- The original left-differential requests on the exact retained source list. -/ left : SourceChartRequests
    leftDifferential domains allowance sources
  /-- The original right-differential requests on the same retained source list. -/ right : SourceChartRequests
    rightDifferential domains allowance sources

constructive_injectivity PairedChartAreaRequest

namespace PairedChartAreaRequest

variable {leftFixed : FaceMagnitudeBank domains leftDifferential} {rightFixed : FaceMagnitudeBank domains
  rightDifferential}
  {sources : List (SourceEdge mesh.triangles.length)} {target :
    Rational}

/-- The complete original paired chart weight is nonnegative. -/
theorem weight_nonnegative (leftFixed : FaceMagnitudeBank domains leftDifferential)
    (rightFixed : FaceMagnitudeBank domains rightDifferential) (sources : List (SewnPrimitiveContacts.SourceEdge
      mesh.triangles.length)) :
    0 ≤ 16 * (sources.length : Fraction.Rational)^4 * (8 * max leftFixed.bound rightFixed.bound + 2) :=
  Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
    (Fraction.Order.Arithmetic.pow_nonneg_direct (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _)) 4))
    (add_nonneg (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) (leftFixed.nonnegative.trans
      (Fraction.Order.Basic.le_max_left _ _))) (by decide))

/-- Prepare both actual original differential request banks at one common paid allowance. -/
@[expose] def build (leftFixed : FaceMagnitudeBank domains leftDifferential) (rightFixed : FaceMagnitudeBank domains
  rightDifferential)
    (sources : List (SewnPrimitiveContacts.SourceEdge mesh.triangles.length)) (nonloop : ∀ source ∈ sources,
      source.first ≠ source.last)
    (target : Fraction.Rational) (positive : 0 < target) : PairedChartAreaRequest leftFixed rightFixed sources target :=
  let weight := 16 * (sources.length : Fraction.Rational)^4 * (8 * max leftFixed.bound rightFixed.bound + 2)
  let allowance := min 1 (Weighted.allowance target weight)
  have allowancePositive : 0 < allowance := Fraction.Order.Basic.lt_min (by decide)
    (Weighted.allowance_positive positive (weight_nonnegative leftFixed rightFixed sources))
  ⟨positive, weight, rfl, allowance, rfl,
    SourceChartRequests.build leftDifferential domains allowance allowancePositive sources nonloop,
    SourceChartRequests.build rightDifferential domains allowance allowancePositive sources nonloop⟩

/-- The maximum stage paying both original magnitude banks and both retained differential requests. -/
@[expose] def index (request : PairedChartAreaRequest leftFixed rightFixed sources target) : Nat :=
  max (max leftFixed.index rightFixed.index) (max request.left.index request.right.index)

/-- Both components use the same source list and the same later numerical stage. Full paired areas, including internal
excursions, are compared. -/
@[reducible, expose] def BankAt (differential : Differentials.Basic.Differential genus) (stage : Nat) :=
  PrimitiveData.FacePrimitiveBank differential stage domains

/-- The exact original mesh's magnitude certificate on the supplied triangle readings. -/
@[reducible, expose] def RetainedMagnitude (values : Fin mesh.triangles.length → PrimitiveSewing.PrimitiveValues 3) :=
  Readings.EdgeMagnitude
    (owner := SourceChartComparison.ownerFromMesh mesh) values

/-- The actual triangle readings of the original retained primitive bank. -/
@[reducible, expose] def ParentReadings {differential : Differentials.Basic.Differential genus} {stage : Nat}
    (bank : PrimitiveData.FacePrimitiveBank differential stage domains) := TrianglePrimitiveReadings.TriangleReadings
      bank mesh

/-- The paired or conjugate pair of actual original source increments selected by the retained view. -/
@[reducible, expose] def SourceValue (view : PairedAreaComparison.View)
    (leftValues rightValues : Fin mesh.triangles.length → PrimitiveSewing.PrimitiveValues 3)
    (source : SewnPrimitiveContacts.SourceEdge mesh.triangles.length) :=
  PairedAreaComparison.point view (source.increment leftValues) (source.increment rightValues)

/-- The corresponding paired or conjugate canonical projected-edge readings on the same original source occurrence. -/
@[reducible, expose] def ChartValue (view : PairedAreaComparison.View)
    (leftValues rightValues : Fin mesh.triangles.length → PrimitiveSewing.PrimitiveValues 3)
    (source : SewnPrimitiveContacts.SourceEdge mesh.triangles.length) :=
  PairedAreaComparison.point view
    (CanonicalEdgeValues.edgeValuation mesh leftValues (source.project mesh.triangulation.faces))
    (CanonicalEdgeValues.edgeValuation mesh rightValues (source.project mesh.triangulation.faces))

/-- The original source increment pairs in retained occurrence order and the selected reading view. -/
@[reducible, expose] def SourceEntries (view : PairedAreaComparison.View)
    (leftValues rightValues : Fin mesh.triangles.length → PrimitiveSewing.PrimitiveValues 3)
    (sources : List (SewnPrimitiveContacts.SourceEdge mesh.triangles.length)) := sources.map (SourceValue view
      leftValues rightValues)

/-- The canonical projected-edge increment pairs in that same original order and reading view. -/
@[reducible, expose] def ChartEntries (view : PairedAreaComparison.View)
    (leftValues rightValues : Fin mesh.triangles.length → PrimitiveSewing.PrimitiveValues 3)
    (sources : List (SewnPrimitiveContacts.SourceEdge mesh.triangles.length)) := sources.map (ChartValue view leftValues
      rightValues)

/-- The cached executable summary of the exact original source pair list. -/
@[reducible, expose] def SourceObservation (view : PairedAreaComparison.View)
    (leftValues rightValues : Fin mesh.triangles.length → PrimitiveSewing.PrimitiveValues 3)
    (sources : List (SewnPrimitiveContacts.SourceEdge mesh.triangles.length)) :=
  PairedAreaComparison.Observation (SourceEntries view leftValues rightValues sources)

/-- The common enlarged magnitude bound from the maximum of the two original magnitude banks. -/
@[reducible, expose] def NumericBound (leftFixed : FaceMagnitudeBank domains leftDifferential)
    (rightFixed : FaceMagnitudeBank domains rightDifferential) : Fraction.Rational :=
  8 * max leftFixed.bound rightFixed.bound + 2

/-- The original ordered source/chart pairs with their retained paired or conjugate view. -/
@[reducible, expose] def PointSpecification (view : PairedAreaComparison.View)
    (leftValues rightValues : Fin mesh.triangles.length → PrimitiveSewing.PrimitiveValues 3)
    (sources : List (SewnPrimitiveContacts.SourceEdge mesh.triangles.length)) :=
  sources.map (fun occurrence => (SourceValue view leftValues rightValues occurrence, ChartValue view leftValues
    rightValues occurrence))

/-- The numerical comparison on the supplied original source observations zipped with the actual chart entries. -/
@[reducible, expose] def NumericComparison (view : PairedAreaComparison.View)
    (request : PairedChartAreaRequest leftFixed rightFixed sources target)
    (leftValues rightValues : Fin mesh.triangles.length → PrimitiveSewing.PrimitiveValues 3)
    (source : SourceObservation view leftValues rightValues sources) (chart : List PrimitivePoint) :=
  PairedAreaComparison.Cached (List.zip source.entries chart)
    request.allowance (NumericBound leftFixed rightFixed)

set_option genInjectivity false in
/-- The original request, reading parents and cached paired source/chart comparison.

Exact identities retain both magnitude banks, primitive banks, source observations, occurrence order and acquired chart
summary. -/
structure Realization (view : PairedAreaComparison.View)
    (request : PairedChartAreaRequest leftFixed rightFixed sources target)
    {stage : Nat} {leftBank : PrimitiveData.FacePrimitiveBank leftDifferential stage domains}
    {rightBank : PrimitiveData.FacePrimitiveBank rightDifferential stage domains}
    (leftReadings : ParentReadings leftBank) (rightReadings : ParentReadings rightBank)
    (source : SourceObservation view leftReadings.values rightReadings.values sources) where
  /-- The actual retained paired or conjugate reading view. -/ viewParent : PairedAreaComparison.View
  /-- The retained view is exactly the originally supplied view. -/ viewParent_eq : viewParent = view
  /-- The original paired chart request retained by the comparison. -/ requestParent : PairedChartAreaRequest leftFixed
    rightFixed sources target
  /-- The retained request is exactly the supplied original request. -/ requestParent_eq : requestParent = request
  /-- The actual shared numerical stage of both original reading banks. -/ sampleStage : Nat
  /-- The retained numerical stage equals the original bank stage. -/ sampleStage_eq : sampleStage = stage
  /-- The actual shared stage pays the complete original request schedule. -/ validity : request.index ≤ sampleStage
  /-- The original left-differential magnitude bank retained by the realization. -/ leftFixedParent : FaceMagnitudeBank
    domains leftDifferential
  /-- The retained left magnitude bank is exactly the supplied original bank. -/ leftFixedParent_eq : leftFixedParent =
    leftFixed
  /-- The original right-differential magnitude bank retained by the realization. -/ rightFixedParent :
    FaceMagnitudeBank domains rightDifferential
  /-- The retained right magnitude bank is exactly the supplied original bank. -/ rightFixedParent_eq : rightFixedParent
    = rightFixed
  /-- The actual original left-differential primitive bank at the shared stage. -/ leftBankParent : BankAt
    leftDifferential stage
  /-- The retained left primitive bank equals the supplied original bank. -/ leftBankParent_eq : leftBankParent =
    leftBank
  /-- The actual original right-differential primitive bank at the shared stage. -/ rightBankParent : BankAt
    rightDifferential stage
  /-- The retained right primitive bank equals the supplied original bank. -/ rightBankParent_eq : rightBankParent =
    rightBank
  /-- The magnitude certificate on the actual original left triangle readings. -/ leftMagnitude : RetainedMagnitude
    leftReadings.values
  /-- The retained left reading bound equals the original magnitude bank's bound. -/ leftMagnitude_bound :
    leftMagnitude.bound = leftFixed.bound
  /-- The retained left magnitude floor equals the original bank's floor. -/ leftMagnitude_index : leftMagnitude.index =
    leftFixed.index
  /-- The magnitude certificate on the actual original right triangle readings. -/ rightMagnitude : RetainedMagnitude
    rightReadings.values
  /-- The retained right reading bound equals the original magnitude bank's bound. -/ rightMagnitude_bound :
    rightMagnitude.bound = rightFixed.bound
  /-- The retained right magnitude floor equals the original bank's floor. -/ rightMagnitude_index :
    rightMagnitude.index = rightFixed.index
  /-- The actual original left-differential triangle readings. -/ leftParent : ParentReadings leftBank
  /-- The retained left readings are exactly the originally supplied readings. -/ leftParent_eq : leftParent =
    leftReadings
  /-- The actual original right-differential triangle readings. -/ rightParent : ParentReadings rightBank
  /-- The retained right readings are exactly the originally supplied readings. -/ rightParent_eq : rightParent =
    rightReadings
  /-- The supplied original paired source observation cache. -/ sourceParent : SourceObservation view
    leftReadings.values rightReadings.values sources
  /-- The retained source observations are exactly the originally supplied cache. -/ sourceParent_eq : sourceParent =
    source
  /-- The actual retained original source occurrences in order. -/ sourceEdges : List (SewnPrimitiveContacts.SourceEdge
    mesh.triangles.length)
  /-- The retained source occurrence list equals the original request list. -/ sourceEdges_eq : sourceEdges = sources
  /-- The acquired canonical chart increment pair list. -/ chart : List PrimitivePoint
  /-- The chart cache equals the selected view of the original canonical projected-edge readings. -/ chart_eq : chart =
    ChartEntries view leftReadings.values rightReadings.values sources
  /-- The executable summary cached from the actual acquired chart list. -/ chartSummary : PairedIncrementArea.Summary
    chart
  /-- The numerical comparison consuming the exact original source cache and acquired chart summary. -/ numeric :
    NumericComparison view request leftReadings.values rightReadings.values source chart
  /-- The retained numerical pair count equals the complete original source occurrence count. -/ pairs_count : (List.zip
    source.entries chart).length = sources.length
  /-- The original source summary area equals the numerical comparison's first cached area. -/ sourceArea_eq :
    source.summary.areaValue = numeric.firstSummary.areaValue
  /-- The actual chart summary area equals the numerical comparison's second cached area. -/ chartArea_eq :
    chartSummary.areaValue = numeric.secondSummary.areaValue

constructive_injectivity Realization

namespace Realization

variable {view : Purelib.Integration.Path.PairedAreaComparison.View}
  {request : PairedChartAreaRequest leftFixed rightFixed sources target}
  {stage : Nat} {leftBank : FacePrimitiveBank
    leftDifferential stage domains}
  {rightBank : FacePrimitiveBank rightDifferential
    stage domains}
  {leftReadings : ParentReadings leftBank} {rightReadings : ParentReadings rightBank}
  {source : SourceObservation view leftReadings.values rightReadings.values sources}

/-- The cached actual paired source-area minus chart-area residual. -/
@[expose] def residual (result : Realization view request leftReadings rightReadings source) : Gaussian :=
  result.numeric.residual
/-- The cached complete squared-norm bound on the actual paired area residual. -/
@[expose] def areaBound (result : Realization view request leftReadings rightReadings source) : Fraction.Rational :=
  result.numeric.areaBound

/-- The cached residual reads the original paired source polygon area minus the corresponding canonical chart polygon
area. -/
theorem residual_readback (result : Realization view request leftReadings rightReadings source) :
    result.residual = PairedIncrementArea.area (SourceEntries view leftReadings.values rightReadings.values sources) -
      PairedIncrementArea.area (ChartEntries view leftReadings.values rightReadings.values sources) := by
  rw [residual, result.numeric.residual_eq, ← result.sourceArea_eq, ← result.chartArea_eq,
    source.area_readback, result.chartSummary.area_eq, result.chart_eq]

/-- The cached complete area bound equals the original retained weight times its common allowance. -/
theorem budget_identity (result : Realization view request leftReadings rightReadings source) :
    result.areaBound = request.weight * request.allowance := by
  rw [areaBound, result.numeric.bound_readback, result.pairs_count,
    PairedAreaComparison.BoundSpecification, NumericBound, request.weight_eq]
  rw [Fraction.Field.mul_assoc,
    Fraction.Field.mul_comm request.allowance (8 * max leftFixed.bound rightFixed.bound + 2),
    ← Fraction.Field.mul_assoc]

/-- The retained weighted allowance pays the original complete paired area target. -/
theorem budget (result : Realization view request leftReadings rightReadings source) : result.areaBound ≤ target := by
  have nonnegative : 0 ≤ request.weight := request.weight_eq ▸ weight_nonnegative leftFixed rightFixed sources
  rw [result.budget_identity]
  exact (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (request.allowance_eq ▸
    Fraction.Order.Basic.min_le_right _ _) nonnegative).trans
    (Weighted.mul_allowance_le request.positive.le nonnegative)

/-- The actual cached paired area residual satisfies the paid original target. -/
theorem pay (result : Realization view request leftReadings rightReadings source) :
  Data.Gaussian.Norm.Basic.normSq result.residual ≤ target :=
  result.numeric.pay result.budget

end Realization

/-- Reuse the supplied original source observation cache, acquire canonical chart entries once, and retain the exact
input owners and complete numerical comparison. -/
@[expose] def realizeSupplied (view : PairedAreaComparison.View) (request : PairedChartAreaRequest leftFixed rightFixed
  sources target)
    {stage : Nat} {leftBank : PrimitiveData.FacePrimitiveBank leftDifferential stage domains}
    {rightBank : PrimitiveData.FacePrimitiveBank rightDifferential stage domains}
    (leftReadings : TrianglePrimitiveReadings.TriangleReadings leftBank mesh) (rightReadings :
      TrianglePrimitiveReadings.TriangleReadings rightBank mesh)
    (later : request.index ≤ stage)
    (source : SourceObservation view leftReadings.values rightReadings.values sources) :
    Realization view request leftReadings rightReadings source := by
  have fixedLater := (Data.Nat.Order.le_max_left _ _).trans later
  let retainedLeftMagnitude := Readings.EdgeMagnitude.ofBank
    (owner := SourceChartComparison.ownerFromMesh mesh) leftFixed ((Data.Nat.Order.le_max_left _ _).trans fixedLater)
      leftReadings
  let retainedRightMagnitude := Readings.EdgeMagnitude.ofBank
    (owner := SourceChartComparison.ownerFromMesh mesh) rightFixed ((Data.Nat.Order.le_max_right _ _).trans fixedLater)
      rightReadings
  have chartLater := (Data.Nat.Order.le_max_right _ _).trans later
  have leftLater := (Data.Nat.Order.le_max_left _ _).trans chartLater
  have rightLater := (Data.Nat.Order.le_max_right _ _).trans chartLater
  let magnitude := max leftFixed.bound rightFixed.bound
  have nonnegative : 0 ≤ magnitude := leftFixed.nonnegative.trans (Fraction.Order.Basic.le_max_left _ _)
  have weightNonnegative : 0 ≤ request.weight := request.weight_eq ▸ weight_nonnegative leftFixed rightFixed sources
  have allowancePositive : 0 < request.allowance := request.allowance_eq ▸ Fraction.Order.Basic.lt_min (by decide)
    (Weighted.allowance_positive request.positive weightNonnegative)
  have small : request.allowance ≤ 1 := request.allowance_eq ▸ Fraction.Order.Basic.min_le_left _ _
  have leftSource (source : SewnPrimitiveContacts.SourceEdge mesh.triangles.length) :
    Data.Gaussian.Norm.Basic.normSq (source.increment leftReadings.values) ≤ 4 * magnitude :=
    (retainedLeftMagnitude.source_bounded source).trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Fraction.Order.Basic.le_max_left _ _) (by decide))
  have rightSource (source : SewnPrimitiveContacts.SourceEdge mesh.triangles.length) :
    Data.Gaussian.Norm.Basic.normSq (source.increment rightReadings.values) ≤ 4 * magnitude :=
    (retainedRightMagnitude.source_bounded source).trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Fraction.Order.Basic.le_max_right _ _) (by decide))
  let chart := ChartEntries view leftReadings.values rightReadings.values sources
  let pairs := List.zip source.entries chart
  have canonical : pairs = PointSpecification view leftReadings.values rightReadings.values sources := by
    change List.zip source.entries (ChartEntries view leftReadings.values rightReadings.values sources) = _
    rw [source.entries_eq]
    exact PairedAreaComparison.zip_maps (SourceValue view leftReadings.values rightReadings.values)
      (ChartValue view leftReadings.values rightReadings.values) sources
  have first : pairs.map Prod.fst = source.entries := by
    rw [canonical, PointSpecification, Data.List.Map.map_map]
    exact source.entries_eq.symm
  have second : pairs.map Prod.snd = chart := by
    rw [canonical, PointSpecification, Data.List.Map.map_map]
    rfl
  have count : pairs.length = sources.length := by rw [canonical, PointSpecification, Data.List.Map.length_map]
  have errors : PairedAreaComparison.PairErrors pairs request.allowance := by
    intro pair member
    rw [canonical] at member
    obtain ⟨occurrence, present, equal⟩ := Map.mem_map.mp member
    rw [← equal]
    constructor
    · cases view with
      | paired =>
          change Data.Gaussian.Basic.Canonical.normSq
            (occurrence.increment leftReadings.values -
              CanonicalEdgeValues.edgeValuation mesh leftReadings.values (occurrence.project mesh.triangulation.faces))
                ≤ request.allowance
          simpa only [Data.Gaussian.Norm.Basic.normSq_eq_canonical] using
            (request.left.accurate leftReadings leftLater occurrence present).le
      | conjugate =>
          change Data.Gaussian.Basic.Canonical.normSq
            (Data.Gaussian.Basic.conj (occurrence.increment leftReadings.values) -
              Data.Gaussian.Basic.conj (CanonicalEdgeValues.edgeValuation mesh leftReadings.values
                (occurrence.project mesh.triangulation.faces))) ≤ request.allowance
          rw [← Readings.EdgeMagnitude.conj_sub,
            ← Data.Gaussian.Norm.Basic.normSq_eq_canonical,
            Data.Gaussian.Norm.Basic.normSq_conj]
          simpa only [Data.Gaussian.Norm.Basic.normSq_eq_canonical] using
            (request.left.accurate leftReadings leftLater occurrence present).le
    · cases view
      all_goals
        change Data.Gaussian.Basic.Canonical.normSq
          (occurrence.increment rightReadings.values -
            CanonicalEdgeValues.edgeValuation mesh rightReadings.values (occurrence.project mesh.triangulation.faces)) ≤
              request.allowance
        simpa only [Data.Gaussian.Norm.Basic.normSq_eq_canonical] using
          (request.right.accurate rightReadings rightLater occurrence present).le
  have originalMagnitude : 4 * magnitude ≤ 8 * magnitude + 2 := by
    calc
      4 * magnitude ≤ 8 * magnitude := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
        (by decide : (4 : Fraction.Rational) ≤ 8) nonnegative
      _ = 8 * magnitude + 0 := by ring1
      _ ≤ 8 * magnitude + 2 := Fraction.Order.Arithmetic.add_le_add_direct
        (Fraction.Order.Basic.le_refl _) (by decide : (0 : Fraction.Rational) ≤ 2)
  have originalBounds : PairedAreaComparison.FirstBounds pairs (8 * magnitude + 2) := by
    intro pair member
    rw [canonical] at member
    obtain ⟨occurrence, _, equal⟩ := Map.mem_map.mp member
    rw [← equal]
    cases view with
    | paired =>
        change Data.Gaussian.Basic.Canonical.normSq (occurrence.increment leftReadings.values) ≤ 8 * magnitude + 2 ∧
          Data.Gaussian.Basic.Canonical.normSq (occurrence.increment rightReadings.values) ≤ 8 * magnitude + 2
        constructor
        · simpa only [Data.Gaussian.Norm.Basic.normSq_eq_canonical] using
            (leftSource occurrence).trans (originalMagnitude)
        · simpa only [Data.Gaussian.Norm.Basic.normSq_eq_canonical] using
            (rightSource occurrence).trans (originalMagnitude)
    | conjugate =>
        change Data.Gaussian.Basic.Canonical.normSq
          (Data.Gaussian.Basic.conj (occurrence.increment leftReadings.values)) ≤ 8 * magnitude + 2 ∧
          Data.Gaussian.Basic.Canonical.normSq (occurrence.increment rightReadings.values) ≤ 8 * magnitude + 2
        constructor
        · rw [← Data.Gaussian.Norm.Basic.normSq_eq_canonical,
            Data.Gaussian.Norm.Basic.normSq_conj]
          exact (leftSource occurrence).trans (originalMagnitude)
        · simpa only [Data.Gaussian.Norm.Basic.normSq_eq_canonical] using
            (rightSource occurrence).trans (originalMagnitude)
  have changedBounds : PairedAreaComparison.SecondBounds pairs (8 * magnitude + 2) := by
    intro pair member
    rw [canonical] at member
    obtain ⟨occurrence, present, equal⟩ := Map.mem_map.mp member
    rw [← equal]
    have leftAccurate : Data.Gaussian.Norm.Basic.normSq
        (occurrence.increment leftReadings.values -
          CanonicalEdgeValues.edgeValuation mesh leftReadings.values (occurrence.project mesh.triangulation.faces)) ≤
            request.allowance := by
      simpa only [Data.Gaussian.Norm.Basic.normSq_eq_canonical] using
        (request.left.accurate leftReadings leftLater occurrence present).le
    have rightAccurate : Data.Gaussian.Norm.Basic.normSq
        (occurrence.increment rightReadings.values -
          CanonicalEdgeValues.edgeValuation mesh rightReadings.values (occurrence.project mesh.triangulation.faces)) ≤
            request.allowance := by
      simpa only [Data.Gaussian.Norm.Basic.normSq_eq_canonical] using
        (request.right.accurate rightReadings rightLater occurrence present).le
    have firstOffset : Data.Gaussian.Norm.Basic.normSq
        (CanonicalEdgeValues.edgeValuation mesh leftReadings.values (occurrence.project mesh.triangulation.faces) -
          occurrence.increment leftReadings.values) ≤ 1 := by
      rewrite [show CanonicalEdgeValues.edgeValuation mesh leftReadings.values (occurrence.project
        mesh.triangulation.faces) - occurrence.increment leftReadings.values =
        -(occurrence.increment leftReadings.values - CanonicalEdgeValues.edgeValuation mesh leftReadings.values
          (occurrence.project mesh.triangulation.faces)) by ring1, Data.Gaussian.Norm.Basic.normSq_neg]
      exact leftAccurate.trans small
    have firstEstimate := Data.Gaussian.Norm.Bounds.value_normSq_le_of_offset firstOffset
    have firstBound := (firstEstimate.trans
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Fraction.Order.Arithmetic.add_le_add_right_direct (leftSource occurrence) 1)
        (by decide : (0 : Fraction.Rational) ≤ 2))).trans_eq
      (show (2 : Fraction.Rational) * (4 * magnitude + 1) = 8 * magnitude + 2 by ring1)
    have secondOffset : Data.Gaussian.Norm.Basic.normSq
        (CanonicalEdgeValues.edgeValuation mesh rightReadings.values (occurrence.project mesh.triangulation.faces) -
          occurrence.increment rightReadings.values) ≤ 1 := by
      rewrite [show CanonicalEdgeValues.edgeValuation mesh rightReadings.values (occurrence.project
        mesh.triangulation.faces) - occurrence.increment rightReadings.values =
        -(occurrence.increment rightReadings.values - CanonicalEdgeValues.edgeValuation mesh rightReadings.values
          (occurrence.project mesh.triangulation.faces)) by ring1, Data.Gaussian.Norm.Basic.normSq_neg]
      exact rightAccurate.trans small
    have secondEstimate := Data.Gaussian.Norm.Bounds.value_normSq_le_of_offset secondOffset
    have secondBound := (secondEstimate.trans
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Fraction.Order.Arithmetic.add_le_add_right_direct (rightSource occurrence) 1)
        (by decide : (0 : Fraction.Rational) ≤ 2))).trans_eq
      (show (2 : Fraction.Rational) * (4 * magnitude + 1) = 8 * magnitude + 2 by ring1)
    cases view with
    | paired =>
        change Data.Gaussian.Basic.Canonical.normSq
          (CanonicalEdgeValues.edgeValuation mesh leftReadings.values (occurrence.project mesh.triangulation.faces)) ≤ 8
            * magnitude + 2 ∧
          Data.Gaussian.Basic.Canonical.normSq
            (CanonicalEdgeValues.edgeValuation mesh rightReadings.values (occurrence.project mesh.triangulation.faces))
              ≤ 8 * magnitude + 2
        constructor
        · simpa only [Data.Gaussian.Norm.Basic.normSq_eq_canonical] using firstBound
        · simpa only [Data.Gaussian.Norm.Basic.normSq_eq_canonical] using secondBound
    | conjugate =>
        change Data.Gaussian.Basic.Canonical.normSq
          (Data.Gaussian.Basic.conj
            (CanonicalEdgeValues.edgeValuation mesh leftReadings.values (occurrence.project mesh.triangulation.faces)))
              ≤ 8 * magnitude + 2 ∧
          Data.Gaussian.Basic.Canonical.normSq
            (CanonicalEdgeValues.edgeValuation mesh rightReadings.values (occurrence.project mesh.triangulation.faces))
              ≤ 8 * magnitude + 2
        constructor
        · rw [← Data.Gaussian.Norm.Basic.normSq_eq_canonical,
            Data.Gaussian.Norm.Basic.normSq_conj]
          exact firstBound
        · simpa only [Data.Gaussian.Norm.Basic.normSq_eq_canonical] using secondBound
  let chartSummary := PairedIncrementArea.Summary.build chart
  let firstSummary := PairedAreaComparison.reindexSummary first.symm source.summary
  let secondSummary := PairedAreaComparison.reindexSummary second.symm chartSummary
  let numeric := Cached.realizeSupplied pairs request.allowance (8 * magnitude + 2)
    firstSummary secondSummary allowancePositive.le
    (add_nonneg (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) nonnegative) (by decide)) errors originalBounds
      changedBounds
  exact { viewParent := view
          viewParent_eq := rfl
          requestParent := request
          requestParent_eq := rfl
          sampleStage := stage
          sampleStage_eq := rfl
          validity := later
          leftFixedParent := leftFixed
          leftFixedParent_eq := rfl
          rightFixedParent := rightFixed
          rightFixedParent_eq := rfl
          leftBankParent := leftBank
          leftBankParent_eq := rfl
          rightBankParent := rightBank
          rightBankParent_eq := rfl
          leftMagnitude := retainedLeftMagnitude
          leftMagnitude_bound := rfl
          leftMagnitude_index := rfl
          rightMagnitude := retainedRightMagnitude
          rightMagnitude_bound := rfl
          rightMagnitude_index := rfl
          leftParent := leftReadings
          leftParent_eq := rfl
          rightParent := rightReadings
          rightParent_eq := rfl
          sourceParent := source
          sourceParent_eq := rfl
          sourceEdges := sources
          sourceEdges_eq := rfl
          chart := chart
          chart_eq := rfl
          chartSummary := chartSummary
          numeric := numeric
          pairs_count := count
          sourceArea_eq := (PairedAreaComparison.reindexSummary_area first.symm source.summary).symm
          chartArea_eq := (PairedAreaComparison.reindexSummary_area second.symm chartSummary).symm }

/-- Acquire the original paired source observation once and realize its chart comparison at the paid shared stage. -/
@[expose] def realize (view : PairedAreaComparison.View) (request : PairedChartAreaRequest leftFixed rightFixed sources
  target)
    {stage : Nat} {leftBank : PrimitiveData.FacePrimitiveBank leftDifferential stage domains}
    {rightBank : PrimitiveData.FacePrimitiveBank rightDifferential stage domains}
    (leftReadings : TrianglePrimitiveReadings.TriangleReadings leftBank mesh) (rightReadings :
      TrianglePrimitiveReadings.TriangleReadings rightBank mesh)
    (later : request.index ≤ stage) :
    Realization view request leftReadings rightReadings
      (Observation.realize (SourceEntries view leftReadings.values rightReadings.values sources)) :=
  realizeSupplied view request leftReadings rightReadings later
    (Observation.realize (SourceEntries view leftReadings.values rightReadings.values sources))

/-- The full paired source and canonical chart polygon areas satisfy the original requested bound, including internal
excursions. -/
theorem accurate (request : PairedChartAreaRequest leftFixed rightFixed sources target)
    {stage : Nat} {leftBank : PrimitiveData.FacePrimitiveBank leftDifferential stage domains}
    {rightBank : PrimitiveData.FacePrimitiveBank rightDifferential stage domains}
    (leftReadings : TrianglePrimitiveReadings.TriangleReadings leftBank mesh) (rightReadings :
      TrianglePrimitiveReadings.TriangleReadings rightBank mesh)
    (later : request.index ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq (PairedIncrementArea.area (sources.map (fun source =>
      (⟨source.increment leftReadings.values, source.increment rightReadings.values⟩ : PrimitivePoint))) -
      PairedIncrementArea.area (sources.map (fun source =>
        (⟨edgeValuation mesh leftReadings.values (source.project mesh.triangulation.faces),
          CanonicalEdgeValues.edgeValuation mesh rightReadings.values (source.project mesh.triangulation.faces)⟩ :
            PrimitivePoint)))) ≤ target := by
  let comparison := request.realize .paired leftReadings rightReadings later
  have paid := comparison.pay
  rw [comparison.residual_readback] at paid
  exact paid

end PairedChartAreaRequest
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.ChartAreaRequests

end
