module
import Purelib.Data.List.Membership
import Purelib.Data.Nat.Order
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Budget.Aggregate
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Approximation.Rational.Budget.Weighted
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Decide
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field

import Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SignedSourceChartRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SkeletonFaceAssignments
import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Integration.Path.IncrementArea
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Topology.Mesh.RetracingWords
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewingRetraction
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.Families

import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OwnedPuncturedMesh

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.ValueWalkAreaRequests
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.MixedChartAreaRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.StemRequests
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.StemAggregate
import Init.Data.Nat.MinMax
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Basic
import Mathlib.Order.Defs.PartialOrder
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BranchArea
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BranchRemainders
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.EdgeMagnitude
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.SourceChartComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Data.Gaussian.Components.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Integration.Path.AreaComparison
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.WindowCircuitOrder
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedBoundaryLoops
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.PuncturedFaceLookup
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.RootIsolation.SquareRoot.Grid.Walk.ChainComparison
import Purelib.RootIsolation.SquareRoot.Grid.Walk.Vertex
import Purelib.Topology.Polygon.Stokes
import Purelib.Tactic.Ring
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.StemCancellation

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Rational.Budget

open Purelib.Curves.Hyperelliptic

open Purelib.Curves.Hyperelliptic.Branches

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkOccurrences

open Purelib.Data.List

open Purelib.Data.Rat

open Purelib.Integration.Path

open Purelib.Polynomial.Geometry.Grid

open Purelib.Topology.Mesh

open Purelib.Topology.Mesh.RetracingWords

open Purelib.Topology.Surface.Sewing

public section

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.Families (Domains MagnitudeBank PrimitiveBank
  TriangleCache Source Sources Nonloop)

/-!
# Value-parameterized corrected stem requests

`StemAreaRequest` and `StemRequest` pay the corrected branch excursion's
opposite-sheet area and endpoint defects for one differential. A mixed value
has no differential, but the same finite requests run on it once the chart
and area comparisons are the mixed ones. This module replays the stem layer
on a mixed value and exposes the aggregate stem bound and the reduced
`surfaceResidual` statement.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid (OwnedPuncturedMesh)

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Topology.Polygon.Stokes
open Purelib.LinearAlgebra.Gaussian.QuadraticForm (GaussianMatrix)
open Purelib.Topology.Surface.Sewing.SewingRetraction (wordValue wordValue_append wordValue_reverse)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid (BasedBranchBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (FacePrimitiveBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank (FaceMagnitudeBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkOccurrences (PairedWalk)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SignedSourceChartRequests (paired_sources_nonloop)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkOccurrences.PairedWalk (build)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues (edgeValuation edgeValuation_reverse
  orderedRoute orderedRoute_value)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.MixedChartAreaRequest
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.ValueWalkAreaRequests (ValueAreaRequest
  ValueIncrementRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.EdgeMagnitude
open Purelib.Topology.Mesh.RetracingWords (wordArea wordArea_reverse)
open Purelib.Topology.Surface.Sewing.PrimitiveSewing (PrimitiveValues)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.StemRequests (walk_magnitude)
open Purelib.Data.Gaussian.Basic.Canonical
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Data.Rat.Fraction.Order.Arithmetic (mul_nonneg_direct mul_le_mul_direct
  mul_le_mul_of_nonneg_left_direct add_le_add_direct)

variable {genus : Nat} {curve : HyperellipticCurve genus}
  {owner : OwnedPuncturedMesh curve} {bank :
    BasedBranchBank owner.lifted}
  {domains : Domains owner}

set_option genInjectivity false in
/-- The mixed stem area request: the opposite-sheet area comparison and both chart transfers run on the conjugate-linear
value. -/
structure ValueStemAreaRequest (bank : LiftedPuncturedGrid.BasedBranchBank owner.lifted)
    {leftDifferential rightDifferential : Differentials.Basic.Differential genus}
    (leftFixed : MagnitudeBank owner domains leftDifferential)
    (rightFixed : MagnitudeBank owner domains rightDifferential) (coefficient : Data.Gaussian.Basic.Canonical)
    (branch : BranchIsolation.Data.Index owner.branches) (sheet : Fin 2) (target : Fraction.Rational) where
  /-- The requested squared-norm target is strictly positive. -/ positive : 0 < target
  /-- The shared allowance for each retained area-comparison component. -/ partTarget : Fraction.Rational
  /-- The component allowance is one tenth of the stem-area target. -/ partTarget_eq : partTarget = target / 10
  /-- The actual paired source placement on the retained branch stem. -/ paired : WalkOccurrences.PairedWalk
    owner.lifted.mesh (bank.rows.get branch).stem
  /-- The retained mixed opposite-sheet source-area request. -/ opposite : ValueAreaRequest (owner := owner) leftFixed
    rightFixed coefficient paired partTarget
  /-- The outward mixed source-to-chart request. -/ outward : MixedChartAreaRequest (owner := owner) leftDifferential
    rightDifferential domains
    leftFixed rightFixed coefficient (paired.sources sheet) partTarget
  /-- The opposite-sheet mixed source-to-chart request. -/ other : MixedChartAreaRequest (owner := owner)
    leftDifferential rightDifferential domains
    leftFixed rightFixed coefficient (paired.sources (BranchCutLifts.otherSheet sheet)) partTarget
  /-- The cached common stage paying the retained component requests. -/ index : Nat
  /-- The cached stage is the maximum of the opposite comparison and both chart transfers. -/ index_eq : index = max
    opposite.index (max outward.index other.index)

constructive_injectivity ValueStemAreaRequest

namespace ValueStemAreaRequest

variable {leftDifferential rightDifferential : Differential genus}
  {coefficient : Purelib.Data.Gaussian.Basic.Canonical}
  {leftFixed : MagnitudeBank owner domains leftDifferential}
  {rightFixed : MagnitudeBank owner domains rightDifferential}
  {branch : Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data.Index owner.branches} {sheet : Fin 2} {target :
    Rational}

/-- Prepare the mixed opposite-sheet comparison and both chart transfers on the same retained branch stem. -/
@[expose] def build (bank : LiftedPuncturedGrid.BasedBranchBank owner.lifted) (leftFixed : MagnitudeBank owner domains
  leftDifferential)
    (rightFixed : MagnitudeBank owner domains rightDifferential) (coefficient : Data.Gaussian.Basic.Canonical)
    (branch : BranchIsolation.Data.Index owner.branches) (sheet : Fin 2) (target : Fraction.Rational)
    (positive : 0 < target) :
    ValueStemAreaRequest (owner := owner) bank leftFixed rightFixed coefficient branch sheet target :=
  let partTarget := target / 10
  have partPositive : 0 < partTarget := Fraction.Order.Field.div_pos_direct positive (by decide)
  let paired := PairedWalk.build owner.lifted.mesh (bank.rows.get branch).stem
  let opposite := ValueAreaRequest.build (owner := owner) leftFixed rightFixed coefficient
    paired partTarget partPositive
  let outward := MixedChartAreaRequest.build (owner := owner) leftDifferential rightDifferential domains leftFixed
    rightFixed
    coefficient (paired.sources sheet) (SignedSourceChartRequests.paired_sources_nonloop paired sheet) partTarget
      partPositive
  let other := MixedChartAreaRequest.build (owner := owner) leftDifferential rightDifferential domains leftFixed
    rightFixed
    coefficient (paired.sources (BranchCutLifts.otherSheet sheet)) (SignedSourceChartRequests.paired_sources_nonloop
      paired _) partTarget partPositive
  ⟨positive, partTarget, rfl, paired, opposite, outward, other,
    max opposite.index (max outward.index other.index), rfl⟩

/-- The opposite sheet is distinct from the supplied sheet. -/
private theorem otherSheet_different (sheet : Fin 2) :
    sheet ≠ BranchCutLifts.otherSheet sheet := by
  have finite : ∀ sheet : Fin 2, sheet ≠ BranchCutLifts.otherSheet sheet := by decide +kernel
  exact finite sheet

/-- The mixed readings on the exact retained mesh owner, differential pair and coefficient. -/
@[expose, reducible] def StemSample (domains : Domains owner)
    (leftDifferential rightDifferential : Differentials.Basic.Differential genus) (coefficient :
      Data.Gaussian.Basic.Canonical) :=
  SourceChartComparison.MixedReadings (owner := owner) domains leftDifferential rightDifferential coefficient

/-- The complete stem-area request stage pays its opposite-sheet comparison. -/
theorem opposite_stage (request : ValueStemAreaRequest (owner := owner) bank leftFixed rightFixed coefficient branch
  sheet target)
    (sample : StemSample (owner := owner) domains leftDifferential rightDifferential coefficient)
    (later : request.index ≤ sample.stage) : request.opposite.index ≤ sample.stage :=
  (Data.Nat.Order.le_max_left _ _).trans (request.index_eq ▸ later)

/-- The actual opposite-sheet area realization on the supplied mixed readings and paid request. -/
@[expose, reducible] def OppositeComparison (request : ValueStemAreaRequest (owner := owner) bank leftFixed rightFixed
  coefficient branch sheet target)
    (sample : StemSample (owner := owner) domains leftDifferential rightDifferential coefficient)
    (later : request.index ≤ sample.stage) :=
  ValueAreaRequest.Realization request.opposite sample.leftReadings sample.rightReadings
    (opposite_stage request sample later) sheet (BranchCutLifts.otherSheet sheet)
    (by exact otherSheet_different sheet)

/-- The outward chart transfer consuming the exact left source observations retained by the opposite realization. -/
@[expose, reducible] def OutwardComparison (request : ValueStemAreaRequest (owner := owner) bank leftFixed rightFixed
  coefficient branch sheet target)
    (sample : StemSample (owner := owner) domains leftDifferential rightDifferential coefficient)
    {later : request.index ≤ sample.stage} (opposite : OppositeComparison request sample later) :=
  MixedChartAreaRequest.Realization request.outward sample opposite.leftSources

/-- The opposite-sheet chart transfer consuming the exact right source observations retained by the opposite
realization. -/
@[expose, reducible] def OtherComparison (request : ValueStemAreaRequest (owner := owner) bank leftFixed rightFixed
  coefficient branch sheet target)
    (sample : StemSample (owner := owner) domains leftDifferential rightDifferential coefficient)
    {later : request.index ≤ sample.stage} (opposite : OppositeComparison request sample later) :=
  MixedChartAreaRequest.Realization request.other sample opposite.rightSources

/-- The residual is exactly the outward chart area minus the opposite-sheet chart area. -/
@[expose, reducible] def ResidualIdentity {request : ValueStemAreaRequest (owner := owner) bank leftFixed rightFixed
  coefficient branch sheet target}
    {sample : StemSample (owner := owner) domains leftDifferential rightDifferential coefficient}
    {later : request.index ≤ sample.stage} {opposite : OppositeComparison request sample later}
    (outward : OutwardComparison request sample opposite) (other : OtherComparison request sample opposite)
    (residual : Data.Gaussian.Basic.Canonical) : Prop := residual = outward.chartArea - other.chartArea

/-- The retained bound is the weighted sum of the three actual child area bounds. -/
@[expose, reducible] def BoundIdentity {request : ValueStemAreaRequest (owner := owner) bank leftFixed rightFixed
  coefficient branch sheet target}
    {sample : StemSample (owner := owner) domains leftDifferential rightDifferential coefficient}
    {later : request.index ≤ sample.stage} (opposite : OppositeComparison request sample later)
    (outward : OutwardComparison request sample opposite) (other : OtherComparison request sample opposite)
    (bound : Fraction.Rational) : Prop :=
  bound = 2 * (outward.areaBound + 2 * (opposite.areaBound + other.areaBound))

set_option genInjectivity false in
/-- The actual stem composition retains all three child realizations. Their middle owners are the exact source
observations from one opposite realization, not arbitrary scalar observations with matching estimates. -/
structure Realization (request : ValueStemAreaRequest (owner := owner) bank leftFixed rightFixed coefficient branch
  sheet target)
    (sample : StemSample (owner := owner) domains leftDifferential rightDifferential coefficient)
    (later : request.index ≤ sample.stage) where
  /-- The retained original stem-area request. -/ selection : ValueStemAreaRequest (owner := owner) bank leftFixed
    rightFixed coefficient branch sheet target
  /-- The retained selection is the supplied request. -/ selection_eq : selection = request
  /-- The retained mixed readings on the original owner and differential pair. -/ readings : StemSample (owner := owner)
    domains leftDifferential rightDifferential coefficient
  /-- The retained readings are the supplied sample. -/ readings_eq : readings = sample
  /-- The actual retained opposite-sheet realization, owning both source observation banks. -/ opposite :
    OppositeComparison request sample later
  /-- The outward chart realization consuming the exact left source bank from the opposite realization. -/ outward :
    OutwardComparison request sample opposite
  /-- The opposite-sheet chart realization consuming the exact right source bank from the opposite realization. -/ other
    : OtherComparison request sample opposite
  /-- The cached signed difference of the two actual chart areas. -/ residual : Data.Gaussian.Basic.Canonical
  /-- The residual cache reads the retained chart-area difference. -/ residual_eq : ResidualIdentity outward other
    residual
  /-- The cached composition bound from the three child realizations. -/ areaBound : Fraction.Rational
  /-- The cached bound is the exact weighted child-bound sum. -/ areaBound_eq : BoundIdentity opposite outward other
    areaBound
  /-- The actual cached residual obeys its retained squared-norm bound. -/ bounded : normSq residual ≤ areaBound
  /-- The retained composition bound fits the requested stem-area target. -/ budget : areaBound ≤ target

constructive_injectivity Realization

/-- Compute each source polygon once in the opposite realization, then reuse its actual observations and summary for
both chart transfers. -/
@[expose] def realize (request : ValueStemAreaRequest (owner := owner) bank leftFixed rightFixed coefficient branch
  sheet target)
    (sample : StemSample (owner := owner) domains leftDifferential rightDifferential coefficient)
    (later : request.index ≤ sample.stage) : Realization request sample later :=
  let opposite := ValueAreaRequest.realize request.opposite sample.leftReadings sample.rightReadings
    (opposite_stage request sample later) sheet (BranchCutLifts.otherSheet sheet)
    (by exact otherSheet_different sheet)
  have chartLater := (Data.Nat.Order.le_max_right _ _).trans (request.index_eq ▸ later)
  let outward := MixedChartAreaRequest.realize request.outward sample opposite.leftSources
    ((Data.Nat.Order.le_max_left _ _).trans chartLater)
  let other := MixedChartAreaRequest.realize request.other sample opposite.rightSources
    ((Data.Nat.Order.le_max_right _ _).trans chartLater)
  let residual := outward.chartArea - other.chartArea
  let areaBound := 2 * (outward.areaBound + 2 * (opposite.areaBound + other.areaBound))
  have outwardBound : normSq (opposite.leftSources.summary.area - outward.chartArea) ≤ outward.areaBound := by
    rw [← outward.residual_cached]
    exact outward.bounded
  have oppositeBound : normSq (opposite.leftSources.summary.area - opposite.rightSources.summary.area) ≤
      opposite.areaBound := by
    rw [← opposite.residual_eq]
    exact opposite.bounded
  have otherBound : normSq (opposite.rightSources.summary.area - other.chartArea) ≤ other.areaBound := by
    rw [← other.residual_cached]
    exact other.bounded
  have bounded : normSq residual ≤ areaBound :=
    AreaComparison.stem_chain outward.chartArea opposite.leftSources.summary.area
      opposite.rightSources.summary.area other.chartArea outwardBound oppositeBound otherBound
  have budget : areaBound ≤ target := by
    have inner := add_le_add_direct outward.budget
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct
        opposite.budget other.budget)
        (by decide : (0 : Fraction.Rational) ≤ 2))
    have scaled := mul_le_mul_of_nonneg_left_direct inner (by decide : (0 : Fraction.Rational) ≤ 2)
    refine scaled.trans_eq ?_
    rw [request.partTarget_eq]
    exact AreaComparison.stem_tenth_payment target
  ⟨request, rfl, sample, rfl, opposite, outward, other, residual, rfl, areaBound, rfl, bounded, budget⟩

namespace Realization

variable {request : ValueStemAreaRequest (owner := owner) bank leftFixed rightFixed coefficient branch sheet target}
  {sample : StemSample (owner := owner) domains leftDifferential rightDifferential coefficient}
  {later : request.index ≤ sample.stage}

/-- The cached mixed residual reads the actual difference of the two retained stem-word areas. -/
theorem residual_readback (realization : Realization request sample later) :
    realization.residual = RetracingWords.wordArea (CanonicalEdgeValues.edgeValuation owner.mesh sample.values)
      (bank.stemWord branch sheet) -
      RetracingWords.wordArea (CanonicalEdgeValues.edgeValuation owner.mesh sample.values)
        (bank.stemWord branch (BranchCutLifts.otherSheet sheet)) := by
  have retained : realization.residual = realization.outward.chartArea - realization.other.chartArea :=
    realization.residual_eq
  rw [retained, realization.outward.chart_readback, realization.other.chart_readback,
    request.paired.sources_project sheet,
    request.paired.sources_project (BranchCutLifts.otherSheet sheet)]
  rfl

/-- The same cached residual reads the outward stem area plus its actual retained return-word area. -/
theorem return_readback (realization : Realization request sample later) :
    realization.residual = RetracingWords.wordArea (CanonicalEdgeValues.edgeValuation owner.mesh sample.values)
      (bank.stemWord branch sheet) +
      RetracingWords.wordArea (CanonicalEdgeValues.edgeValuation owner.mesh sample.values) (bank.returnWord branch
        sheet) := by
  rw [bank.returnWord_reverse, RetracingWords.wordArea_reverse _ (CanonicalEdgeValues.edgeValuation_reverse owner.mesh
    sample.values)]
  exact realization.residual_readback

/-- The cached mixed residual satisfies the requested squared-norm target. -/
theorem pay (realization : Realization request sample later) : normSq realization.residual ≤ target :=
  realization.bounded.trans realization.budget

end Realization

/-- The existing numeric contract now follows from the named cached realization and payment. All three estimates above
consume that one retained object. -/
theorem accurate (request : ValueStemAreaRequest (owner := owner) bank leftFixed rightFixed coefficient branch sheet
  target)
    {stage : Nat} {leftBank : PrimitiveBank owner leftDifferential stage domains}
    {rightBank : PrimitiveBank owner rightDifferential stage domains}
    (leftReadings : TriangleCache owner leftDifferential stage domains leftBank)
    (rightReadings : TriangleCache owner rightDifferential stage domains rightBank) (later : request.index ≤ stage) :
    let value := CanonicalEdgeValues.edgeValuation owner.lifted.mesh
      (EdgeMagnitude.mixValues (owner := owner) leftReadings.values rightReadings.values coefficient)
    normSq (RetracingWords.wordArea value (bank.stemWord branch sheet) -
      RetracingWords.wordArea value (bank.stemWord branch (BranchCutLifts.otherSheet sheet))) ≤ target := by
  intro value
  let sample := SourceChartComparison.MixedReadings.ofReadings (owner := owner) coefficient leftReadings rightReadings
  let realization := request.realize sample later
  have paid := realization.pay
  rw [realization.residual_readback] at paid
  exact paid

/-- The actual retained return-word orientation is read from the same cache. -/
theorem return_area_accurate (request : ValueStemAreaRequest (owner := owner) bank leftFixed rightFixed coefficient
  branch sheet target)
    {stage : Nat} {leftBank : PrimitiveBank owner leftDifferential stage domains}
    {rightBank : PrimitiveBank owner rightDifferential stage domains}
    (leftReadings : TriangleCache owner leftDifferential stage domains leftBank)
    (rightReadings : TriangleCache owner rightDifferential stage domains rightBank) (later : request.index ≤ stage) :
    let value := CanonicalEdgeValues.edgeValuation owner.lifted.mesh
      (EdgeMagnitude.mixValues (owner := owner) leftReadings.values rightReadings.values coefficient)
    normSq (RetracingWords.wordArea value (bank.stemWord branch sheet) +
      RetracingWords.wordArea value (bank.returnWord branch sheet)) ≤ target := by
  intro value
  let sample := SourceChartComparison.MixedReadings.ofReadings (owner := owner) coefficient leftReadings rightReadings
  let realization := request.realize sample later
  have paid := realization.pay
  rw [realization.return_readback] at paid
  exact paid

end ValueStemAreaRequest

/-- A uniform nonnegative source-increment magnitude bounds the actual indexed walk value by its squared edge count. -/
private theorem walk_magnitude (magnitude : Fraction.Rational) (nonnegative : 0 ≤ magnitude)
    {values : Fin owner.lifted.mesh.triangles.length → PrimitiveSewing.PrimitiveValues 3}
    (bounded : ∀ source : SewnPrimitiveContacts.SourceEdge owner.lifted.mesh.triangles.length,
      normSq (source.increment values) ≤ 4 * magnitude)
    {start finish : Data.Gaussian.Basic.Canonical} (walk : Walks.Walk owner.base.bank.grid start finish) (sheet : Fin 2)
      :
    normSq (SewingRetraction.wordValue (CanonicalEdgeValues.edgeValuation owner.lifted.mesh values)
      (owner.lifted.edges.indexedEdges owner.lifted.vertices walk sheet)) ≤
      (walk.edgeCount : Fraction.Rational) ^ 2 * (4 * magnitude) := by
  rw [← RetracingWords.sum_map_eq_wordValue]
  rw [← Data.Gaussian.Norm.Basic.normSq_eq_canonical]
  apply IncrementArea.sum_bound_of_length (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) nonnegative) ?_ ?_
  · intro value member
    obtain ⟨edge, inWord, equal⟩ := Map.mem_map.mp member
    rw [← equal]
    have supported := SkeletonFaceAssignments.indexedWalk_supported owner.lifted.mesh walk sheet edge inWord
    rw [← CanonicalEdgeValues.orderedRoute_value owner.lifted.mesh edge supported]
    have h := bounded (CanonicalEdgeValues.orderedRoute owner.lifted.mesh edge supported).sourceEdge
    change Fraction.Order.Basic.LessEqual _ _ at h ⊢
    simpa only [Data.Gaussian.Norm.Basic.normSq_eq_canonical] using h
  · rw [Data.List.Map.length_map, owner.lifted.edges.indexedEdges_length]

set_option genInjectivity false in
/-- A corrected branch-stem request for a retained mixed value.

The area and endpoint requests share the original mesh owner, differential pair, coefficient and stem placement. -/
structure ValueStemRequest (bank : LiftedPuncturedGrid.BasedBranchBank owner.lifted)
    {leftDifferential rightDifferential : Differentials.Basic.Differential genus}
    (leftFixed : MagnitudeBank owner domains leftDifferential)
    (rightFixed : MagnitudeBank owner domains rightDifferential) (coefficient : Data.Gaussian.Basic.Canonical)
    (branch : BranchIsolation.Data.Index owner.branches) (sheet : Fin 2) (target : Fraction.Rational) where
  /-- The requested squared-norm target is strictly positive. -/ positive : 0 < target
  /-- The cached mixed stem-plus-hole magnitude ceiling. -/ magnitude : Fraction.Rational
  /-- The magnitude retains the squared stem-plus-hole edge count and the actual mixed-value bound. -/ magnitude_eq :
    magnitude = (((bank.rows.get branch).stem.append (bank.rows.get branch).boundary).edgeCount : Fraction.Rational) ^ 2
    *
    (4 * EdgeMagnitude.mixBound leftFixed.bound rightFixed.bound coefficient)
  /-- The weighted allowance for the mixed endpoint defect. -/ incrementTarget : Fraction.Rational
  /-- The increment allowance is the weighted share of one quarter of the target. -/ incrementTarget_eq :
    incrementTarget = Weighted.allowance (target / 4) (4 * magnitude)
  /-- The mixed stem-area request at one quarter of the target. -/ area : ValueStemAreaRequest (owner := owner) bank
    leftFixed rightFixed coefficient branch sheet (target / 4)
  /-- The mixed increment request on that exact retained stem placement. -/ increment : ValueIncrementRequest (owner :=
    owner) leftDifferential rightDifferential
    domains coefficient area.paired sheet incrementTarget
  /-- The cached common stage paying the retained component requests. -/ index : Nat
  /-- The common stage is the maximum of the mixed area and increment request stages. -/ index_eq : index = max
    area.index increment.index

constructive_injectivity ValueStemRequest

namespace ValueStemRequest

variable {leftDifferential rightDifferential : Differential genus}
  {coefficient : Purelib.Data.Gaussian.Basic.Canonical}
  {leftFixed : MagnitudeBank owner domains leftDifferential}
  {rightFixed : MagnitudeBank owner domains rightDifferential}
  {branch : Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data.Index owner.branches} {sheet : Fin 2} {target :
    Rational}

/-- Prepare the mixed stem-area and increment requests with their actual stem-plus-hole magnitude budget. -/
@[expose] def build (bank : LiftedPuncturedGrid.BasedBranchBank owner.lifted) (leftFixed : MagnitudeBank owner domains
  leftDifferential)
    (rightFixed : MagnitudeBank owner domains rightDifferential) (coefficient : Data.Gaussian.Basic.Canonical)
    (branch : BranchIsolation.Data.Index owner.branches) (sheet : Fin 2) (target : Fraction.Rational)
    (positive : 0 < target) :
    ValueStemRequest (owner := owner) bank leftFixed rightFixed coefficient branch sheet target :=
  let magnitude := (((bank.rows.get branch).stem.append (bank.rows.get branch).boundary).edgeCount : Fraction.Rational)
    ^ 2 *
    (4 * EdgeMagnitude.mixBound leftFixed.bound rightFixed.bound coefficient)
  let incrementTarget := Weighted.allowance (target / 4) (4 * magnitude)
  have quarterPositive : 0 < target / 4 := Fraction.Order.Field.div_pos_direct positive (by decide)
  have magnitudeNonnegative : 0 ≤ magnitude :=
    mul_nonneg_direct (Fraction.Order.Arithmetic.pow_nonneg_direct
      (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _)) 2)
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
        (EdgeMagnitude.mixBound_nonnegative leftFixed.nonnegative rightFixed.nonnegative coefficient))
  let area := ValueStemAreaRequest.build (owner := owner) bank leftFixed rightFixed coefficient branch sheet (target /
    4) quarterPositive
  let increment := ValueIncrementRequest.build (owner := owner) leftDifferential rightDifferential
    domains coefficient area.paired sheet incrementTarget
    (Weighted.allowance_positive quarterPositive
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) magnitudeNonnegative))
  ⟨positive, magnitude, rfl, incrementTarget, rfl, area, increment, max area.index increment.index, rfl⟩

/-- At the paid common stage, the actual mixed corrected stem error obeys the requested squared-norm target. -/
theorem accurate (request : ValueStemRequest (owner := owner) bank leftFixed rightFixed coefficient branch sheet target)
    {stage : Nat} {leftBank : PrimitiveBank owner leftDifferential stage domains}
    {rightBank : PrimitiveBank owner rightDifferential stage domains}
    (leftReadings : TriangleCache owner leftDifferential stage domains leftBank)
    (rightReadings : TriangleCache owner rightDifferential stage domains rightBank) (later : request.index ≤ stage) :
    let value := CanonicalEdgeValues.edgeValuation owner.lifted.mesh
      (EdgeMagnitude.mixValues (owner := owner) leftReadings.values rightReadings.values coefficient)
    normSq (bank.stemError value branch sheet) ≤ target := by
  intro value
  have areaLater := (Data.Nat.Order.le_max_left _ _).trans (request.index_eq ▸ later)
  have incrementLater := (Data.Nat.Order.le_max_right _ _).trans (request.index_eq ▸ later)
  have oppositeLater := (Data.Nat.Order.le_max_left _ _).trans (request.area.index_eq ▸ areaLater)
  have fixedLater : leftFixed.index ≤ stage :=
    (Data.Nat.Order.le_max_left _ _).trans ((Data.Nat.Order.le_max_left _ _).trans
      (request.area.opposite.index_eq ▸ oppositeLater))
  have rightFixedLater : rightFixed.index ≤ stage :=
    (Data.Nat.Order.le_max_right _ _).trans ((Data.Nat.Order.le_max_left _ _).trans
      (request.area.opposite.index_eq ▸ oppositeLater))
  let leftMagnitude := EdgeMagnitude.ofBank (owner := owner) leftFixed fixedLater leftReadings
  let rightMagnitude := EdgeMagnitude.ofBank (owner := owner) rightFixed rightFixedLater rightReadings
  let mixedMagnitude := EdgeMagnitude.mix (owner := owner) leftMagnitude rightMagnitude coefficient
  have magnitudeBound : mixedMagnitude.bound =
      EdgeMagnitude.mixBound leftFixed.bound rightFixed.bound coefficient := rfl
  have sourceBound (source : SewnPrimitiveContacts.SourceEdge owner.lifted.mesh.triangles.length) :
      normSq (source.increment (EdgeMagnitude.mixValues (owner := owner) leftReadings.values rightReadings.values
        coefficient)) ≤
        4 * mixedMagnitude.bound := by
    have h := mixedMagnitude.source_bounded source
    change Fraction.Order.Basic.LessEqual _ _ at h ⊢
    rw [← Data.Gaussian.Norm.Basic.normSq_eq_canonical]
    exact h
  have magnitude := walk_magnitude mixedMagnitude.bound mixedMagnitude.nonnegative
    sourceBound
    ((bank.rows.get branch).stem.append (bank.rows.get branch).boundary) sheet
  rw [magnitudeBound, ← request.magnitude_eq] at magnitude
  rw [owner.lifted.edges.indexedEdges_append, SewingRetraction.wordValue_append] at magnitude
  change normSq (SewingRetraction.wordValue value (bank.stemWord branch sheet) +
    SewingRetraction.wordValue value (bank.holeWord branch sheet)) ≤ request.magnitude at magnitude
  have oldBound {point : Data.Gaussian.Basic.Canonical} {limit : Fraction.Rational}
      (h : normSq point ≤ limit) : Data.Gaussian.Norm.Basic.normSq point ≤ limit := by
    change Fraction.Order.Basic.LessEqual _ _ at h ⊢
    simpa only [Data.Gaussian.Norm.Basic.normSq_eq_canonical] using h
  have canonicalBound {point : Data.Gaussian.Basic.Canonical} {limit : Fraction.Rational}
      (h : Data.Gaussian.Norm.Basic.normSq point ≤ limit) : normSq point ≤ limit := by
    change Fraction.Order.Basic.LessEqual _ _ at h ⊢
    simpa only [Data.Gaussian.Norm.Basic.normSq_eq_canonical] using h
  have magnitudeNonnegative : 0 ≤ request.magnitude := request.magnitude_eq ▸
    mul_nonneg_direct (Fraction.Order.Arithmetic.pow_nonneg_direct
      (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _)) 2)
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
        (EdgeMagnitude.mixBound_nonnegative leftFixed.nonnegative rightFixed.nonnegative coefficient))
  have increment : normSq (SewingRetraction.wordValue value (bank.returnWord branch sheet) -
      SewingRetraction.wordValue value (bank.stemWord branch sheet)) ≤ request.incrementTarget := by
    rw [bank.returnWord_reverse, SewingRetraction.wordValue_reverse _ (CanonicalEdgeValues.edgeValuation_reverse
      owner.lifted.mesh _)]
    rw [show -SewingRetraction.wordValue value (bank.stemWord branch (BranchCutLifts.otherSheet sheet)) -
        SewingRetraction.wordValue value (bank.stemWord branch sheet) =
        -(SewingRetraction.wordValue value (bank.stemWord branch sheet) +
          SewingRetraction.wordValue value (bank.stemWord branch (BranchCutLifts.otherSheet sheet))) by ring1,
      Data.Gaussian.Basic.Canonical.normSq_neg]
    exact request.increment.accurate leftReadings rightReadings incrementLater
  have product := mul_le_mul_direct (oldBound magnitude) (oldBound increment) (Data.Gaussian.Norm.Basic.normSq_nonneg _)
    magnitudeNonnegative
  have weighted := mul_le_mul_of_nonneg_left_direct product (by decide : (0 : Fraction.Rational) ≤ 4)
  have weightedBound : 4 * request.magnitude * request.incrementTarget ≤ target / 4 := by
    rw [request.incrementTarget_eq]
    exact Weighted.mul_allowance_le
      (Fraction.Order.Field.div_nonneg_direct request.positive.le (by decide))
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) magnitudeNonnegative)
  have paid := (weighted.trans_eq (by ring1)).trans weightedBound
  have paidLeft : 4 * Data.Gaussian.Norm.Basic.normSq (SewingRetraction.wordValue value (bank.stemWord branch
    sheet) +
      SewingRetraction.wordValue value (bank.holeWord branch sheet)) *
      Data.Gaussian.Norm.Basic.normSq (SewingRetraction.wordValue value (bank.returnWord branch sheet) -
        SewingRetraction.wordValue value (bank.stemWord branch sheet)) ≤
      target / 4 := by
    rw [_root_.mul_assoc]
    exact paid
  have estimate := (bank.stemError_bound value branch sheet).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct
      (oldBound (request.area.return_area_accurate leftReadings rightReadings areaLater)) paidLeft) (by decide))
  apply canonicalBound
  exact estimate.trans_eq ((by ring1 : 2 * (target / 4 + target / 4) = target / 4 * 4).trans
    (Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)))

end ValueStemRequest
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid (OwnedPuncturedMesh)

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Topology.Polygon.Stokes
open Purelib.LinearAlgebra.Gaussian.QuadraticForm (GaussianMatrix)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid (BasedBranchBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank (Ordered)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.Ordered (Paired)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (FacePrimitiveBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank (FaceMagnitudeBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.StemAggregate (StemRequests)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BranchArea (PairedRows)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs (EndingTours)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms (Prepared)
open Purelib.Topology.Surface.Sewing.SewingRetraction (wordValue)
open Purelib.Topology.Mesh.RetracingWords.AreaTerm (total)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.EdgeMagnitude
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues (edgeValuation)
open Purelib.Data.Rat.Fraction.Order.Arithmetic (mul_nonneg_direct mul_le_mul_of_nonneg_left_direct add_le_add_direct)

variable {genus : Nat} {curve : HyperellipticCurve genus}
  {owner : OwnedPuncturedMesh curve} {bank :
    BasedBranchBank owner.lifted}
  {domains : Domains owner}

set_option genInjectivity false in
/-- Every retained branch label paired with its actual starting sheet. -/
inductive ValueStemRequests (bank : LiftedPuncturedGrid.BasedBranchBank owner.lifted)
    {leftDifferential rightDifferential : Differentials.Basic.Differential genus}
    (leftFixed : MagnitudeBank owner domains leftDifferential)
    (rightFixed : MagnitudeBank owner domains rightDifferential) (coefficient : Data.Gaussian.Basic.Canonical) (target :
      Fraction.Rational) :
    List (BranchIsolation.Data.Index owner.branches × Fin 2) → Type 3 where
  /-- The empty mixed stem request bank. -/ | nil : ValueStemRequests bank leftFixed rightFixed coefficient target []
  /-- Retain the actual mixed stem request for the first branch and sheet, followed by the remaining requests. -/ | cons
    {entry entries} (head : ValueStemRequest (owner := owner) bank leftFixed rightFixed coefficient entry.1 entry.2
    target)
      (tail : ValueStemRequests bank leftFixed rightFixed coefficient target entries) :
      ValueStemRequests bank leftFixed rightFixed coefficient target (entry :: entries)

constructive_injectivity ValueStemRequests

namespace ValueStemRequests

variable {leftDifferential rightDifferential : Differential genus}
  {coefficient : Purelib.Data.Gaussian.Basic.Canonical}
  {leftFixed : MagnitudeBank owner domains leftDifferential}
  {rightFixed : MagnitudeBank owner domains rightDifferential} {target : Rational}
  {entries : List (Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data.Index owner.branches × Fin 2)}

/-- Prepare the mixed request for each retained branch-and-sheet entry in its original order. -/
@[expose] def build (bank : LiftedPuncturedGrid.BasedBranchBank owner.lifted) (leftFixed : MagnitudeBank owner domains
  leftDifferential)
    (rightFixed : MagnitudeBank owner domains rightDifferential) (coefficient : Data.Gaussian.Basic.Canonical)
    (target : Fraction.Rational) (positive : 0 < target) :
    (entries : List (BranchIsolation.Data.Index owner.branches × Fin 2)) →
      ValueStemRequests (owner := owner) bank leftFixed rightFixed coefficient target entries
  | [] => .nil
  | entry :: entries => .cons (ValueStemRequest.build (owner := owner) bank leftFixed rightFixed coefficient entry.1
    entry.2
      target positive) (build bank leftFixed rightFixed coefficient target positive entries)

/-- The maximum stage paying the ordered mixed stem bank, or zero for an empty bank. -/
@[expose] def index : {entries : List (BranchIsolation.Data.Index owner.branches × Fin 2)} →
    ValueStemRequests (owner := owner) bank leftFixed rightFixed coefficient target entries → Nat
  | _, .nil => 0
  | _, .cons head tail => max head.index tail.index

/-- At the paid common stage, every retained mixed stem error fits the shared allowance. -/
theorem accurate (requests : ValueStemRequests (owner := owner) bank leftFixed rightFixed coefficient target entries)
    {stage : Nat} {leftBank : PrimitiveBank owner leftDifferential stage domains}
    {rightBank : PrimitiveBank owner rightDifferential stage domains}
    (leftReadings : TriangleCache owner leftDifferential stage domains leftBank)
    (rightReadings : TriangleCache owner rightDifferential stage domains rightBank) (later : requests.index ≤ stage) :
    ∀ entry ∈ entries,
      normSq (bank.stemError (CanonicalEdgeValues.edgeValuation owner.lifted.mesh
        (EdgeMagnitude.mixValues (owner := owner) leftReadings.values rightReadings.values coefficient)) entry.1
          entry.2) ≤ target := by
  induction requests with
  | nil => intro entry member; exact (List.not_mem_nil member).elim
  | cons head tail inductionHypothesis =>
      intro entry member
      rcases Data.List.Membership.mem_cons.mp member with rfl | member
      · have h := head.accurate leftReadings rightReadings ((Data.Nat.Order.le_max_left _ _).trans later)
        change Fraction.Order.Basic.LessEqual _ _ at h ⊢
        simpa only [Data.Gaussian.Norm.Basic.normSq_eq_canonical] using h
      · exact inductionHypothesis ((Data.Nat.Order.le_max_right _ _).trans later) entry member

end ValueStemRequests

namespace Ordered.Paired.Prepared

variable {sheet : Fin 2} {ordered :
  Ordered bank
  sheet} {paired : Paired ordered}

set_option genInjectivity false in
/-- The complete mixed-value corrected stem request bank.

It retains all paired-row and terminal branch labels with their actual sheets and one paid aggregate allowance. -/
structure ValueStemAggregateRequest (prepared : PeriodPrograms.Prepared paired)
    {leftDifferential rightDifferential : Differentials.Basic.Differential genus}
    (leftFixed : MagnitudeBank owner domains leftDifferential)
    (rightFixed : MagnitudeBank owner domains rightDifferential) (coefficient : Data.Gaussian.Basic.Canonical) (target :
      Fraction.Rational) where
  /-- The requested squared-norm target is strictly positive. -/ positive : 0 < target
  /-- The cached complete branch-and-sheet label list. -/ labels : List (BranchIsolation.Data.Index owner.branches × Fin
    2)
  /-- The retained labels are exactly the prepared paired rows and terminal excursions. -/ labels_eq : labels =
    prepared.stemLabels
  /-- The retained common mixed stem allowance. -/ allowance : Fraction.Rational
  /-- The mixed stem allowance is the finite-count share of the aggregate target. -/ allowance_eq : allowance =
    Aggregate.perTerm target labels.length
  /-- The actual ordered mixed stem requests at the retained allowance. -/ requests : ValueStemRequests (owner := owner)
    bank leftFixed rightFixed coefficient allowance labels
  /-- The cached common stage paying the retained component requests. -/ index : Nat
  /-- The cached aggregate stage is the actual retained mixed request bank's stage. -/ index_eq : index = requests.index

constructive_injectivity ValueStemAggregateRequest

namespace ValueStemAggregateRequest

variable {prepared : Prepared paired}
  {leftDifferential rightDifferential : Differential genus}
  {leftFixed : MagnitudeBank owner domains leftDifferential}
  {rightFixed : MagnitudeBank owner domains rightDifferential} {coefficient : Purelib.Data.Gaussian.Basic.Canonical}
    {target : Rational}

/-- Allocate the positive aggregate allowance across every retained mixed stem and cache the common paid stage. -/
@[expose] def build (prepared : PeriodPrograms.Prepared paired) (leftFixed : MagnitudeBank owner domains
  leftDifferential)
    (rightFixed : MagnitudeBank owner domains rightDifferential) (coefficient : Data.Gaussian.Basic.Canonical)
    (target : Fraction.Rational) (positive : 0 < target) :
    ValueStemAggregateRequest (owner := owner) prepared leftFixed rightFixed coefficient target :=
  let labels := prepared.stemLabels
  let allowance := Aggregate.perTerm target labels.length
  let requests := ValueStemRequests.build (owner := owner) bank leftFixed rightFixed coefficient allowance
    (Aggregate.perTerm_positive positive _) labels
  ⟨positive, labels, rfl, allowance, rfl, requests, requests.index, rfl⟩

/-- Both the paired rows and the terminal excursions are paid for the mixed value. No caller supplies a stem-area or
endpoint magnitude. -/
theorem accurate (request : ValueStemAggregateRequest (owner := owner) prepared leftFixed rightFixed coefficient target)
    {stage : Nat} {leftBank : PrimitiveBank owner leftDifferential stage domains}
    {rightBank : PrimitiveBank owner rightDifferential stage domains}
    (leftReadings : TriangleCache owner leftDifferential stage domains leftBank)
    (rightReadings : TriangleCache owner rightDifferential stage domains rightBank) (later : request.index ≤ stage) :
    let value := CanonicalEdgeValues.edgeValuation owner.lifted.mesh
      (EdgeMagnitude.mixValues (owner := owner) leftReadings.values rightReadings.values coefficient)
    normSq (paired.rows.stemErrors value + paired.ending.stemErrors value) < target := by
  intro value
  rw [paired.rows.stemErrors_eq, paired.ending.stemErrors_eq, ← IncrementArea.sum_append,
    ← Data.List.Map.map_append]
  change normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum (prepared.stemLabels.map (fun entry =>
    bank.stemError value entry.1 entry.2))) < target
  rw [← request.labels_eq]
  apply Gaussian.Budget.Aggregate.normSq_sum_lt _ request.positive
  intro error member
  obtain ⟨entry, inLabels, equal⟩ := Map.mem_map.mp member
  rw [← equal, Data.List.Map.length_map]
  have bound := request.requests.accurate leftReadings rightReadings (request.index_eq ▸ later) entry inLabels
  rw [request.allowance_eq] at bound
  exact bound

/-- The mixed corrected surface residual loses all stems at a requested cost. Physical hole areas, their cross term,
exterior terms, and regular face terms remain explicit and are not claimed small by this theorem. -/
theorem surface_accurate (request : ValueStemAggregateRequest (owner := owner) prepared leftFixed rightFixed coefficient
  target)
    {stage : Nat} {leftBank : PrimitiveBank owner leftDifferential stage domains}
    {rightBank : PrimitiveBank owner rightDifferential stage domains}
    (leftReadings : TriangleCache owner leftDifferential stage domains leftBank)
    (rightReadings : TriangleCache owner rightDifferential stage domains rightBank) (later : request.index ≤ stage) :
    let value := CanonicalEdgeValues.edgeValuation owner.lifted.mesh
      (EdgeMagnitude.mixValues (owner := owner) leftReadings.values rightReadings.values coefficient)
    normSq (BilinearIdentity.surfaceResidual prepared value -
      ((paired.rows.holeAreas value + paired.ending.holeAreas value) +
        BoundaryRibbon.area (SewingRetraction.wordValue value paired.rows.word)
          (-SewingRetraction.wordValue value (paired.reference.hole.liftedBoundary owner.lifted.vertices
            owner.lifted.edges)) +
        paired.ending.exteriorArea value (SewingRetraction.wordValue value paired.rows.word) +
        AreaTerm.total value ordered.prepared.compiled.areaTerms -
        owner.lifted.edges.chainArea owner.lifted.vertices value owner.base.bank.exterior sheet)) < target := by
  intro value
  rw [prepared.surfaceResidual_split]
  convert request.accurate leftReadings rightReadings later using 1
  congr 1
  ring1

end ValueStemAggregateRequest
end Ordered.Paired.Prepared
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings
