module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.ShiftedAcquisition.Uniform
public import Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision.Restriction
public import Purelib.Data.Vector.Dependent
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Programs
import Purelib.Data.Gaussian.Norm.Weighted
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Tactic.Ring

/-! # Actual target-child integral comparison on two retained dyadic acquisitions

Both complete globally allocated preparation families and their exact
original local-to-global occurrence maps are inputs. Their SAME retained
restriction banks and common-fine occurrence vector reassemble each actual
target word. Internally derived signed queries bound each common piece;
nonnegative widths summing to one remove every adaptive child-count factor.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent.ShiftedAcquisition

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Algebraic.Uniform.Jets (UniformObservation)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.List
open Purelib.Algebra
open Purelib.Algebra.FiniteSum.Fin (sumFin)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Interval.ConvexCombination
open Purelib.Data.Rat.Fraction
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Integration.Polynomial.Gaussian
open Purelib.Integration.Polynomial.Gaussian.Cell.Basic (CellModel)
open Purelib.Polynomial.Ascending.Gaussian
open Purelib.Riemann.Branches
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision
open Purelib.Riemann.Meshes
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Riemann.Integration.PreparedConstantModels (PreparedEdge)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels.CoveredTracedPath

variable {parameter increment : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis} {patch : PreparedPatch parent} {count : Nat}
    {covered : (patch.neighborhood count).box.Contains (parent.edge.point 1)}
    {range : Variation.Point.Range (patch.neighborhood count)} {target : Paths.Frame (parameter + increment)}
    {admitted : Norm.Basic.normSq increment ≤ range.shiftedBound}
    {strip : Norm.Basic.normSq increment ≤ range.stripBound} {firstWidth lastWidth : AccuracyRequest}
    {firstFloor lastFloor : Nat} {firstStart firstFinish lastStart lastFinish : LiftedPoint 2}
    {firstOriginal : LiftedPath 2 firstStart firstFinish} {lastOriginal : LiftedPath 2 lastStart lastFinish}
    {firstStage lastStage : Nat}
    {firstTargets : CellEndpoints.Targets firstOriginal firstStage}
    {lastTargets : CellEndpoints.Targets lastOriginal lastStage}
    (first : PreparedParent patch count firstFloor covered firstTargets)
    (last : PreparedParent patch count lastFloor covered lastTargets)
    (firstLinked : Linked first range target admitted strip firstWidth)
    (lastLinked : Linked last range target admitted strip lastWidth)
    (firstAligned : Acquisition.Segment.RootComparisons.Alignment
      firstLinked.comparison.paths firstLinked.comparison.firstReference)
    (lastAligned : Acquisition.Segment.RootComparisons.Alignment
      lastLinked.comparison.paths lastLinked.comparison.firstReference)
    {firstNewParents lastNewParents : List (CenteredEdge (Fibre.frameCurve target) basis)}
    {firstNewCover : CoveredParents count firstNewParents} {lastNewCover : CoveredParents count lastNewParents}
    {firstNewFloor lastNewFloor : Nat} {firstNewStart firstNewFinish lastNewStart lastNewFinish : LiftedPoint 2}
    {firstNewOriginal : LiftedPath 2 firstNewStart firstNewFinish}
    {lastNewOriginal : LiftedPath 2 lastNewStart lastNewFinish}
    {firstNewStage lastNewStage : Nat}
    {firstNewTargets : CellEndpoints.Targets firstNewOriginal firstNewStage}
    {lastNewTargets : CellEndpoints.Targets lastNewOriginal lastNewStage}
    (firstPrepared : PreparedParents firstNewCover firstNewFloor firstNewTargets)
    (lastPrepared : PreparedParents lastNewCover lastNewFloor lastNewTargets)
    (firstPositions : Fin firstLinked.shifted.parents.covered.parents.length → Fin firstNewParents.length)
    (lastPositions : Fin lastLinked.shifted.parents.covered.parents.length → Fin lastNewParents.length)
    (firstEntry_eq : ∀ index, firstNewParents[(firstPositions index).val]'(firstPositions index).isLt =
      firstLinked.shifted.childAt index)
    (lastEntry_eq : ∀ index, lastNewParents[(lastPositions index).val]'(lastPositions index).isLt =
      lastLinked.shifted.childAt index)

/-- The original common-fine pair vector and all six original restriction-bank pairs, before bounded-time queries.

This exact existing-container product keeps both actual global preparation
families and occurrence maps. It introduces no context, source, root or
period owner; each field is genuinely new auxiliary finite restriction data.
-/
@[expose] def CommonCaches :=
  Data.Vector.DependentVector (fun index => RefinementPair
      firstLinked.shifted.acquired.mesh.depth lastLinked.shifted.acquired.mesh.depth
        UniformPrimitiveMesh.firstEndpoint UniformPrimitiveMesh.lastEndpoint index) ×
    Data.Vector.DependentVector (fun channel : Fin 6 =>
      RefinementRestrictions firstLinked.shifted.acquired.mesh.depth lastLinked.shifted.acquired.mesh.depth
        UniformPrimitiveMesh.firstEndpoint UniformPrimitiveMesh.lastEndpoint
          (firstLinked.shifted.dyadicCells firstPrepared firstPositions channel)) ×
    Data.Vector.DependentVector (fun channel : Fin 6 =>
      RefinementRestrictions lastLinked.shifted.acquired.mesh.depth firstLinked.shifted.acquired.mesh.depth
        UniformPrimitiveMesh.firstEndpoint UniformPrimitiveMesh.lastEndpoint
          (lastLinked.shifted.dyadicCells lastPrepared lastPositions channel))

/-- Materialize the three actual common-refinement cache families once in the minimal original acquisition context. -/
def commonCaches : CommonCaches first last firstLinked lastLinked firstPrepared lastPrepared firstPositions
    lastPositions :=
  let pairs := refinementPairs firstLinked.shifted.acquired.mesh.depth lastLinked.shifted.acquired.mesh.depth
    UniformPrimitiveMesh.firstEndpoint UniformPrimitiveMesh.lastEndpoint
  let firstBanks := Data.Vector.DependentVector.ofFn (fun channel : Fin 6 =>
    RefinementRestrictions.build firstLinked.shifted.acquired.mesh.depth lastLinked.shifted.acquired.mesh.depth
      UniformPrimitiveMesh.firstEndpoint UniformPrimitiveMesh.lastEndpoint
        (firstLinked.shifted.dyadicCells firstPrepared firstPositions channel))
  let lastBanks := Data.Vector.DependentVector.ofFn (fun channel : Fin 6 =>
    RefinementRestrictions.build lastLinked.shifted.acquired.mesh.depth firstLinked.shifted.acquired.mesh.depth
      UniformPrimitiveMesh.firstEndpoint UniformPrimitiveMesh.lastEndpoint
        (lastLinked.shifted.dyadicCells lastPrepared lastPositions channel))
  ⟨pairs, firstBanks, lastBanks⟩

include first last firstLinked lastLinked firstAligned lastAligned firstEntry_eq lastEntry_eq in
/-- Both SAME globally allocated target-child words obey a fixed-original-parent integral comparison.

The exact original occurrence maps can be the projections of the two
stored ValueBlock.position tables. Neither source family is locally
reallocated. All new polynomial restrictions and both occurrence outcomes
are already materialized before this theorem. Every actual common-piece
endpoint and signed query comparison is derived internally; the original
nonnegative dyadic widths sum to one, so the resulting factor contains no
adaptive depth or child-count multiplier.
-/
theorem commonIntegral_difference_le (channel : Fin 6)
    (pairs : Data.Vector.DependentVector (fun index => RefinementPair
      firstLinked.shifted.acquired.mesh.depth lastLinked.shifted.acquired.mesh.depth
        UniformPrimitiveMesh.firstEndpoint UniformPrimitiveMesh.lastEndpoint index))
    (firstRestrictions : RefinementRestrictions firstLinked.shifted.acquired.mesh.depth
      lastLinked.shifted.acquired.mesh.depth UniformPrimitiveMesh.firstEndpoint UniformPrimitiveMesh.lastEndpoint
        (firstLinked.shifted.dyadicCells firstPrepared firstPositions channel))
    (lastRestrictions : RefinementRestrictions lastLinked.shifted.acquired.mesh.depth
      firstLinked.shifted.acquired.mesh.depth UniformPrimitiveMesh.firstEndpoint UniformPrimitiveMesh.lastEndpoint
        (lastLinked.shifted.dyadicCells lastPrepared lastPositions channel)) :
    Norm.Basic.normSq
      (sumFin (fun index => ((firstPrepared.entry (firstPositions index)).preparation.cell.models.cell
        channel).integralSample) -
        sumFin (fun index => ((lastPrepared.entry (lastPositions index)).preparation.cell.models.cell
          channel).integralSample)) ≤
      16 * (firstNewTargets.localBound + lastNewTargets.localBound) * cost parent := by
  let firstDepth := firstLinked.shifted.acquired.mesh.depth
  let lastDepth := lastLinked.shifted.acquired.mesh.depth
  let fineEdges := dyadicEdges (firstDepth + lastDepth)
    UniformPrimitiveMesh.firstEndpoint UniformPrimitiveMesh.lastEndpoint
  let weights := fun index : Fin fineEdges.length =>
    (fineEdges[index.val]'index.isLt).right.parameter - (fineEdges[index.val]'index.isLt).left.parameter
  let firstValues := fun index : Fin fineEdges.length =>
    (firstRestrictions.fineCell (pairs.get index).1).integralSample
  let lastValues := fun index : Fin fineEdges.length =>
    (lastRestrictions.fineCell (pairs.get index).2).integralSample
  let density := 16 * (firstNewTargets.localBound + lastNewTargets.localBound) * cost parent
  have bounded (index : Fin fineEdges.length) :
      Norm.Basic.normSq (firstValues index - lastValues index) ≤ density * (weights index) ^ 2 := by
    let found := pairs.get index
    let firstCoarse := refinementOccurrence.coarseIndex found.1
    let lastCoarse := refinementOccurrence.coarseIndex found.2
    let firstLocal := firstLinked.shifted.dyadicIndex firstCoarse
    let lastLocal := lastLinked.shifted.dyadicIndex lastCoarse
    let firstActual := firstPrepared.entry (firstPositions firstLocal)
    let lastActual := lastPrepared.entry (lastPositions lastLocal)
    have actual := commonDyadic_integral_difference_le first last firstLinked lastLinked firstAligned lastAligned
      firstActual lastActual index found (firstEntry_eq firstLocal) (lastEntry_eq lastLocal) channel
      (firstRestrictions.bank firstCoarse) (lastRestrictions.bank lastCoarse)
    have allowances :
        (firstActual.preparation.cell.models.cell channel).localAllowance +
          (lastActual.preparation.cell.models.cell channel).localAllowance =
        firstNewTargets.localBound + lastNewTargets.localBound :=
      congrArg₂ (fun first last : Rational => first + last)
        (firstActual.cell_allowance channel) (lastActual.cell_allowance channel)
    have paid :
        16 * ((firstActual.preparation.cell.models.cell channel).localAllowance +
          (lastActual.preparation.cell.models.cell channel).localAllowance) *
            (weights index) ^ 2 * cost parent =
        16 * (firstNewTargets.localBound + lastNewTargets.localBound) *
          (weights index) ^ 2 * cost parent :=
      congrArg (fun allowance : Rational => 16 * allowance * (weights index) ^ 2 * cost parent) allowances
    have factor_eq :
        16 * (firstNewTargets.localBound + lastNewTargets.localBound) *
          (weights index) ^ 2 * cost parent = density * (weights index) ^ 2 :=
      (Field.mul_assoc (16 * (firstNewTargets.localBound + lastNewTargets.localBound))
        ((weights index) ^ 2) (cost parent)).trans
          ((congrArg (fun product : Rational =>
            (16 * (firstNewTargets.localBound + lastNewTargets.localBound)) * product)
            (Field.mul_comm ((weights index) ^ 2) (cost parent))).trans
              (Field.mul_assoc (16 * (firstNewTargets.localBound + lastNewTargets.localBound))
                (cost parent) ((weights index) ^ 2)).symm)
    exact actual.trans_eq (paid.trans factor_eq)
  have nonnegative (index : Fin fineEdges.length) : 0 ≤ weights index :=
    dyadicEdges_width_nonnegative (firstDepth + lastDepth) UniformPrimitiveMesh.firstEndpoint
      UniformPrimitiveMesh.lastEndpoint (show (0 : Rational) ≤ 1 by decide +kernel) index
  have widths : sumFin weights = 1 :=
    (dyadicEdges_sum_widths (firstDepth + lastDepth)
      UniformPrimitiveMesh.firstEndpoint UniformPrimitiveMesh.lastEndpoint).trans (by decide +kernel)
  have fineBound := Norm.Weighted.normSq_sumFin_weighted
    (fun index => firstValues index - lastValues index) weights nonnegative bounded
  have unitPower : (1 : Rational) ^ 2 = 1 := by decide +kernel
  have density_eq : density * (sumFin weights) ^ 2 = density :=
    (congrArg (fun width : Rational => density * width ^ 2) widths).trans
      ((congrArg (fun power : Rational => density * power) unitPower).trans
        (Field.mul_one_direct density))
  have firstSum := (firstRestrictions.sample_sum (fun index => (pairs.get index).1)
    (show (0 : Rational) < 1 by decide +kernel)).trans
      (firstLinked.shifted.dyadicCells_sum firstPrepared firstPositions channel)
  have lastCount : fineEdges.length = (dyadicEdges (lastDepth + firstDepth)
      UniformPrimitiveMesh.firstEndpoint UniformPrimitiveMesh.lastEndpoint).length :=
    congrArg (fun depth => (dyadicEdges depth
      UniformPrimitiveMesh.firstEndpoint UniformPrimitiveMesh.lastEndpoint).length) (Nat.add_comm firstDepth lastDepth)
  have lastSum := (lastRestrictions.sample_sum_cast lastCount (fun index => (pairs.get index).2)
    (show (0 : Rational) < 1 by decide +kernel)).trans
      (lastLinked.shifted.dyadicCells_sum lastPrepared lastPositions channel)
  have reassembled :
      sumFin (fun index => ((firstPrepared.entry (firstPositions index)).preparation.cell.models.cell
        channel).integralSample) -
      sumFin (fun index => ((lastPrepared.entry (lastPositions index)).preparation.cell.models.cell
        channel).integralSample) = sumFin (fun index => firstValues index - lastValues index) :=
    (congrArg₂ (fun first last : Canonical => first - last) firstSum.symm lastSum.symm).trans
      (FiniteSum.Fin.sumFin_sub firstValues lastValues).symm
  exact (congrArg Norm.Basic.normSq reassembled).trans_le (fineBound.trans_eq density_eq)

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent.ShiftedAcquisition

end
