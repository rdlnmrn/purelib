module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.ShiftedAcquisition.Comparison
public import Purelib.Integration.Polynomial.Gaussian.Cell.Restriction
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.ShiftedAcquisition.Dyadic
public import Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision.Restriction
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Programs
import Purelib.Curves.Legendre.Periods.Jets.Source.Observations.Channels
import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Uniform.Comparison
import Purelib.Integration.Polynomial.Gaussian.Cell.Primitive
import Purelib.Geometry.Rational.Affine
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring

/-! # Actual polynomial comparisons across independent shifted acquisitions

Both old source preparations, original strip Range and independently
materialized Linked acquisitions remain inputs. Each bounded-time callback
constructs its genuine old source answers/Steps and actual target bundles
once, with their actual original query factories. Three direct-edge queries
link these precise owners; neither a signed relation nor a desired integral
bound is supplied. Existing restriction caches retain both polynomials.
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
    {firstChild lastChild : CenteredEdge (Fibre.frameCurve target) basis}
    {firstNewPatch : PreparedPatch firstChild} {lastNewPatch : PreparedPatch lastChild}
    {firstNewCount lastNewCount firstNewFloor lastNewFloor : Nat}
    {firstNewCovered : (firstNewPatch.neighborhood firstNewCount).box.Contains (firstChild.edge.point 1)}
    {lastNewCovered : (lastNewPatch.neighborhood lastNewCount).box.Contains (lastChild.edge.point 1)}
    {firstNewStart firstNewFinish lastNewStart lastNewFinish : LiftedPoint 2}
    {firstNewOriginal : LiftedPath 2 firstNewStart firstNewFinish}
    {lastNewOriginal : LiftedPath 2 lastNewStart lastNewFinish}
    {firstNewStage lastNewStage : Nat}
    {firstNewTargets : CellEndpoints.Targets firstNewOriginal firstNewStage}
    {lastNewTargets : CellEndpoints.Targets lastNewOriginal lastNewStage}
    (firstNew : PreparedParent firstNewPatch firstNewCount firstNewFloor firstNewCovered firstNewTargets)
    (lastNew : PreparedParent lastNewPatch lastNewCount lastNewFloor lastNewCovered lastNewTargets)
    (firstIndex : Fin firstLinked.shifted.parents.covered.parents.length)
    (lastIndex : Fin lastLinked.shifted.parents.covered.parents.length)
    (first_eq : firstChild = firstLinked.shifted.parents.covered.parents[firstIndex.val]'firstIndex.isLt)
    (last_eq : lastChild = lastLinked.shifted.parents.covered.parents[lastIndex.val]'lastIndex.isLt)
    (firstInput lastInput : Rational)
    (firstInside : 0 ≤ firstInput ∧ firstInput ≤ 1) (lastInside : 0 ≤ lastInput ∧ lastInput ≤ 1)

include first last firstLinked lastLinked firstAligned lastAligned firstIndex lastIndex first_eq last_eq
  firstInside lastInside in
/-- Genuine original query/Step factories derive a common-point polynomial bound on both actual target models.

The original preparations, local/global Targets, Linked trace/Alignment
owners and child occurrences remain independent. Each callback retains its
actual old answer and Step, target bundle and direct-query caches once.
All six coefficient channels use the SAME internally derived signed root
comparison. This is a polynomial bound, not a period identity.
-/
theorem uniform_polynomial_difference_le
    (samePoint : firstChild.edge.point firstInput = lastChild.edge.point lastInput) (channel : Fin 6) :
    Norm.Basic.normSq
      (Evaluation.eval (firstNew.preparation.cell.models.cell channel).polynomial (Cast.Path.ofCoordinate firstInput) -
        Evaluation.eval (lastNew.preparation.cell.models.cell channel).polynomial
          (Cast.Path.ofCoordinate lastInput)) ≤
      8 * ((firstNew.preparation.cell.models.cell channel).localAllowance +
        (lastNew.preparation.cell.models.cell channel).localAllowance) := by
  let firstFraction := PreparedSheetContinuation.parameterAt firstChild.edge.left firstChild.edge.request firstInput
  let lastFraction := PreparedSheetContinuation.parameterAt lastChild.edge.left lastChild.edge.request lastInput
  let firstOldInside := PreparedSheetContinuation.parameterAt_inside firstChild.edge.left firstChild.edge.request
    firstChild.edge.ordered firstInput firstInside
  let lastOldInside := PreparedSheetContinuation.parameterAt_inside lastChild.edge.left lastChild.edge.request
    lastChild.edge.ordered lastInput lastInside
  let firstOld := first.advanceQuery range firstFraction firstOldInside.1 firstOldInside.2 increment
    (admitted.trans range.shiftedBound_le_bound)
  let lastOld := last.advanceQuery range lastFraction lastOldInside.1 lastOldInside.2 increment
    (admitted.trans range.shiftedBound_le_bound)
  let firstObserved := firstNew.preparation.query.observe target firstInput firstInside.1 firstInside.2
  let lastObserved := lastNew.preparation.query.observe target lastInput lastInside.1 lastInside.2
  let parentQuery := PreparedEdge.Query.build parent.edge firstFraction firstOldInside
  let firstDirect := PreparedEdge.Query.build firstChild.edge firstInput firstInside
  let lastDirect := PreparedEdge.Query.build lastChild.edge lastInput lastInside
  have roots := queryEquivalent first last firstLinked lastLinked firstAligned lastAligned firstNew lastNew
    firstIndex lastIndex first_eq last_eq firstInput lastInput firstInside lastInside firstOld.2 lastOld.2
    firstObserved.retained.sample lastObserved.retained.sample samePoint parentQuery firstDirect lastDirect
  have firstRoot := firstNew.preparation.query.channel_root_name target firstInput firstInside.1 firstInside.2
    firstObserved rfl channel
  have lastRoot := lastNew.preparation.query.channel_root_name target lastInput lastInside.1 lastInside.2
    lastObserved rfl channel
  have signed := NamedEquivalent.transport firstRoot.symm lastRoot.symm roots
  have firstPoint := (firstObserved.channel_point channel).trans (firstNew.queryPoint_eq firstInput)
  have lastPoint := (lastObserved.channel_point channel).trans (lastNew.queryPoint_eq lastInput)
  have points := firstPoint.trans (samePoint.trans lastPoint.symm)
  have positive : (0 : Rational) < (firstNew.preparation.cell.models.cell channel).localAllowance +
      (lastNew.preparation.cell.models.cell channel).localAllowance := by
    rewrite [firstNew.cell_allowance channel, lastNew.cell_allowance channel]
    exact Order.Arithmetic.add_pos_of_pos_of_nonneg_direct firstNewTargets.localBound_positive
      lastNewTargets.localBound_positive.le
  exact (firstObserved.channel channel).polynomial_difference_le (lastObserved.channel channel) points signed positive

include first last firstLinked lastLinked firstAligned lastAligned firstIndex lastIndex first_eq last_eq in
/-- Two actual cached polynomial restrictions on a common physical subsegment obey both original target allocations.

The endpoint equations concern the original cached child models, not a
root or integral relation. Every bounded-time callback constructs its actual
original query/Step comparison above. The original restriction laws and
finite polynomial primitive bound retain both actual polynomial tables,
unchanged allowances and actual integral samples. A common dyadic occurrence
supplies these geometric endpoints in the whole-parent consumer.
-/
theorem restricted_integral_difference_le (channel : Fin 6)
    {firstLeft firstRight lastLeft lastRight : Rational}
    (firstLeftInside : 0 ≤ firstLeft ∧ firstLeft ≤ 1)
    (firstRightInside : 0 ≤ firstRight ∧ firstRight ≤ 1)
    (lastLeftInside : 0 ≤ lastLeft ∧ lastLeft ≤ 1)
    (lastRightInside : 0 ≤ lastRight ∧ lastRight ≤ 1)
    (firstCached : Restriction.Cached (firstNew.preparation.cell.models.cell channel).polynomial
      (Cast.Path.ofCoordinate firstLeft) (Cast.Path.ofCoordinate firstRight))
    (lastCached : Restriction.Cached (lastNew.preparation.cell.models.cell channel).polynomial
      (Cast.Path.ofCoordinate lastLeft) (Cast.Path.ofCoordinate lastRight))
    (start_eq : (Cell.Restriction.model (firstNew.preparation.cell.models.cell channel) firstCached).start =
      (Cell.Restriction.model (lastNew.preparation.cell.models.cell channel) lastCached).start)
    (finish_eq : (Cell.Restriction.model (firstNew.preparation.cell.models.cell channel) firstCached).finish =
      (Cell.Restriction.model (lastNew.preparation.cell.models.cell channel) lastCached).finish) :
    Norm.Basic.normSq
      ((Cell.Restriction.model (firstNew.preparation.cell.models.cell channel) firstCached).integralSample -
        (Cell.Restriction.model (lastNew.preparation.cell.models.cell channel) lastCached).integralSample) ≤
      16 * ((firstNew.preparation.cell.models.cell channel).localAllowance +
        (lastNew.preparation.cell.models.cell channel).localAllowance) *
          Norm.Basic.normSq (Cell.Restriction.model
            (firstNew.preparation.cell.models.cell channel) firstCached).displacement := by
  let firstCell := firstNew.preparation.cell.models.cell channel
  let lastCell := lastNew.preparation.cell.models.cell channel
  have bounded (input : Rational) (inside : Cell.Primitive.unitInterval.Contains input) :
      Norm.Basic.normSq
        (Evaluation.eval (Cell.Restriction.model firstCell firstCached).polynomial (Cast.Path.ofCoordinate input) -
          Evaluation.eval (Cell.Restriction.model lastCell lastCached).polynomial (Cast.Path.ofCoordinate input)) ≤
        8 * (firstCell.localAllowance + lastCell.localAllowance) := by
    let firstTime := Cell.Restriction.parameter firstLeft firstRight input
    let lastTime := Cell.Restriction.parameter lastLeft lastRight input
    let firstInside := Cell.Restriction.parameter_inside firstLeftInside firstRightInside inside
    let lastInside := Cell.Restriction.parameter_inside lastLeftInside lastRightInside inside
    have finePoints : (Cell.Restriction.model firstCell firstCached).point input =
        (Cell.Restriction.model lastCell lastCached).point input := by
      unfold CellModel.point CellModel.displacement
      rewrite [start_eq, finish_eq]
      rfl
    have physical : firstChild.edge.point firstTime = lastChild.edge.point lastTime :=
      (firstNew.queryPoint_eq firstTime).symm.trans
        ((firstNew.preparation.cell.models.cell_point channel firstTime).symm.trans
          ((Cell.Restriction.point_eq firstCell firstCached input).symm.trans
            (finePoints.trans ((Cell.Restriction.point_eq lastCell lastCached input).trans
              ((lastNew.preparation.cell.models.cell_point channel lastTime).trans
                (lastNew.queryPoint_eq lastTime))))))
    have actual := uniform_polynomial_difference_le first last firstLinked lastLinked firstAligned lastAligned
      firstNew lastNew firstIndex lastIndex first_eq last_eq firstTime lastTime firstInside lastInside physical channel
    have values := congrArg₂ (fun first last : Canonical => first - last)
      (Cell.Restriction.eval_eq firstCell firstCached input) (Cell.Restriction.eval_eq lastCell lastCached input)
    exact (congrArg Norm.Basic.normSq values).trans_le actual
  have actual := Cell.Primitive.integral_difference_le (Cell.Restriction.model firstCell firstCached)
    (Cell.Restriction.model lastCell lastCached) start_eq finish_eq
    (8 * (firstCell.localAllowance + lastCell.localAllowance)) bounded
  exact actual.trans_eq (by ring1)

include first last firstLinked lastLinked firstAligned lastAligned in
/-- Two actual cached target restrictions at one SAME retained common-dyadic occurrence have an internally paid bound.

The pair retains both original coarse/fine occurrences, including their
full prefix offsets. Exact Mesh-to-Parents index transport locates each
unchanged globally allocated source. All four restricted physical endpoints
are derived from those occurrences and original affine-point laws, rather
than supplied as endpoint or signed-sheet equations. Both complete existing
restriction banks and all original source/target caches remain inputs.
-/
theorem commonDyadic_integral_difference_le
    (index : Fin (dyadicEdges
      (firstLinked.shifted.acquired.mesh.depth + lastLinked.shifted.acquired.mesh.depth)
        UniformPrimitiveMesh.firstEndpoint UniformPrimitiveMesh.lastEndpoint).length)
    (pair : RefinementPair firstLinked.shifted.acquired.mesh.depth lastLinked.shifted.acquired.mesh.depth
      UniformPrimitiveMesh.firstEndpoint UniformPrimitiveMesh.lastEndpoint index)
    (firstSelected : firstChild = firstLinked.shifted.childAt
      (firstLinked.shifted.dyadicIndex (refinementOccurrence.coarseIndex pair.1)))
    (lastSelected : lastChild = lastLinked.shifted.childAt
      (lastLinked.shifted.dyadicIndex (refinementOccurrence.coarseIndex pair.2)))
    (channel : Fin 6)
    (firstRestrictions : ParameterEdge.Restrictions (firstNew.preparation.cell.models.cell channel)
      (refinementOccurrence.coarseEdge pair.1) lastLinked.shifted.acquired.mesh.depth)
    (lastRestrictions : ParameterEdge.Restrictions (lastNew.preparation.cell.models.cell channel)
      (refinementOccurrence.coarseEdge pair.2) firstLinked.shifted.acquired.mesh.depth) :
    let common := (dyadicEdges
      (firstLinked.shifted.acquired.mesh.depth + lastLinked.shifted.acquired.mesh.depth)
        UniformPrimitiveMesh.firstEndpoint UniformPrimitiveMesh.lastEndpoint)[index.val]'index.isLt
    Norm.Basic.normSq
      ((Cell.Restriction.model (firstNew.preparation.cell.models.cell channel)
          (firstRestrictions.cache (refinementOccurrence.localIndex pair.1))).integralSample -
        (Cell.Restriction.model (lastNew.preparation.cell.models.cell channel)
          (lastRestrictions.cache (refinementOccurrence.localIndex pair.2))).integralSample) ≤
      16 * ((firstNew.preparation.cell.models.cell channel).localAllowance +
        (lastNew.preparation.cell.models.cell channel).localAllowance) *
          (common.right.parameter - common.left.parameter) ^ 2 * cost parent := by
  let firstCoarse := refinementOccurrence.coarseEdge pair.1
  let lastCoarse := refinementOccurrence.coarseEdge pair.2
  let firstInner := refinementOccurrence.localIndex pair.1
  let lastInner := refinementOccurrence.localIndex pair.2
  let firstFine := (dyadicEdges lastLinked.shifted.acquired.mesh.depth firstCoarse.left firstCoarse.right)[
    firstInner.val]'firstInner.isLt
  let lastFine := (dyadicEdges firstLinked.shifted.acquired.mesh.depth lastCoarse.left lastCoarse.right)[
    lastInner.val]'lastInner.isLt
  let common := (dyadicEdges
    (firstLinked.shifted.acquired.mesh.depth + lastLinked.shifted.acquired.mesh.depth)
      UniformPrimitiveMesh.firstEndpoint UniformPrimitiveMesh.lastEndpoint)[index.val]'index.isLt
  let firstCache := firstRestrictions.cache firstInner
  let lastCache := lastRestrictions.cache lastInner
  have firstCoarseBounds := dyadicEdges_bounds firstLinked.shifted.acquired.mesh.depth
    UniformPrimitiveMesh.firstEndpoint UniformPrimitiveMesh.lastEndpoint
    (show (0 : Rational) ≤ 1 by decide +kernel) _
    (List.getElem_mem (refinementOccurrence.coarseIndex pair.1).isLt)
  have lastCoarseBounds := dyadicEdges_bounds lastLinked.shifted.acquired.mesh.depth
    UniformPrimitiveMesh.firstEndpoint UniformPrimitiveMesh.lastEndpoint
    (show (0 : Rational) ≤ 1 by decide +kernel) _
    (List.getElem_mem (refinementOccurrence.coarseIndex pair.2).isLt)
  have firstBounds := dyadicEdges_bounds lastLinked.shifted.acquired.mesh.depth firstCoarse.left firstCoarse.right
    firstCoarseBounds.2.1 firstFine (List.getElem_mem firstInner.isLt)
  have lastBounds := dyadicEdges_bounds firstLinked.shifted.acquired.mesh.depth lastCoarse.left lastCoarse.right
    lastCoarseBounds.2.1 lastFine (List.getElem_mem lastInner.isLt)
  have firstFine_eq : firstFine = common := (refinementOccurrence.edge_eq pair.1).symm
  have lastFine_eq : lastFine = common := (refinementOccurrence.edge_eq pair.2).symm.trans
    (commutedIndex_edge firstLinked.shifted.acquired.mesh.depth lastLinked.shifted.acquired.mesh.depth
      UniformPrimitiveMesh.firstEndpoint UniformPrimitiveMesh.lastEndpoint index)
  have firstStart :
      (Cell.Restriction.model (firstNew.preparation.cell.models.cell channel) firstCache).start =
        parent.edge.point common.left.parameter :=
    (Cell.Restriction.model_start _ firstCache).trans
      ((firstLinked.shifted.dyadicCellPoint_eq (refinementOccurrence.coarseIndex pair.1)
        firstSelected firstNew channel firstFine.left.parameter
        ⟨firstBounds.1, firstBounds.2.1.trans firstBounds.2.2⟩).trans
          (congrArg (fun edge : ParameterEdge => parent.edge.point edge.left.parameter) firstFine_eq))
  have firstFinish :
      (Cell.Restriction.model (firstNew.preparation.cell.models.cell channel) firstCache).finish =
        parent.edge.point common.right.parameter :=
    (Cell.Restriction.model_finish _ firstCache).trans
      ((firstLinked.shifted.dyadicCellPoint_eq (refinementOccurrence.coarseIndex pair.1)
        firstSelected firstNew channel firstFine.right.parameter
        ⟨firstBounds.1.trans firstBounds.2.1, firstBounds.2.2⟩).trans
          (congrArg (fun edge : ParameterEdge => parent.edge.point edge.right.parameter) firstFine_eq))
  have lastStart :
      (Cell.Restriction.model (lastNew.preparation.cell.models.cell channel) lastCache).start =
        parent.edge.point common.left.parameter :=
    (Cell.Restriction.model_start _ lastCache).trans
      ((lastLinked.shifted.dyadicCellPoint_eq (refinementOccurrence.coarseIndex pair.2)
        lastSelected lastNew channel lastFine.left.parameter
        ⟨lastBounds.1, lastBounds.2.1.trans lastBounds.2.2⟩).trans
          (congrArg (fun edge : ParameterEdge => parent.edge.point edge.left.parameter) lastFine_eq))
  have lastFinish :
      (Cell.Restriction.model (lastNew.preparation.cell.models.cell channel) lastCache).finish =
        parent.edge.point common.right.parameter :=
    (Cell.Restriction.model_finish _ lastCache).trans
      ((lastLinked.shifted.dyadicCellPoint_eq (refinementOccurrence.coarseIndex pair.2)
        lastSelected lastNew channel lastFine.right.parameter
        ⟨lastBounds.1.trans lastBounds.2.1, lastBounds.2.2⟩).trans
          (congrArg (fun edge : ParameterEdge => parent.edge.point edge.right.parameter) lastFine_eq))
  have firstInside := ParameterEdge.Restrictions.endpoints_inside firstCoarseBounds.2.1 firstInner
  have lastInside := ParameterEdge.Restrictions.endpoints_inside lastCoarseBounds.2.1 lastInner
  have actual := restricted_integral_difference_le first last firstLinked lastLinked firstAligned lastAligned
    firstNew lastNew (firstLinked.shifted.dyadicIndex (refinementOccurrence.coarseIndex pair.1))
    (lastLinked.shifted.dyadicIndex (refinementOccurrence.coarseIndex pair.2)) firstSelected lastSelected channel
    firstInside.1 firstInside.2 lastInside.1 lastInside.2 firstCache lastCache
    (firstStart.trans lastStart.symm) (firstFinish.trans lastFinish.symm)
  have originalPoint (time : Rational) :
      (first.preparation.cell.models.cell channel).point time = parent.edge.point time :=
    (first.preparation.cell.models.cell_point channel time).trans (first.queryPoint_eq time)
  have displacement :
      Norm.Basic.normSq (Cell.Restriction.model (firstNew.preparation.cell.models.cell channel)
        firstCache).displacement =
          (common.right.parameter - common.left.parameter) ^ 2 * cost parent := by
    calc
      _ = Norm.Basic.normSq (parent.edge.point common.right.parameter -
          parent.edge.point common.left.parameter) :=
        congrArg Norm.Basic.normSq (congrArg₂ (fun finish start : Canonical => finish - start)
          firstFinish firstStart)
      _ = Norm.Basic.normSq ((first.preparation.cell.models.cell channel).point common.right.parameter -
          (first.preparation.cell.models.cell channel).point common.left.parameter) :=
        congrArg Norm.Basic.normSq (congrArg₂ (fun finish start : Canonical => finish - start)
          (originalPoint common.right.parameter).symm (originalPoint common.left.parameter).symm)
      _ = (common.right.parameter - common.left.parameter) ^ 2 *
          Norm.Basic.normSq (first.preparation.cell.models.cell channel).displacement :=
        (Geometry.Rational.Affine.normSq_line_sub
          (first.preparation.cell.models.cell channel).start
          (first.preparation.cell.models.cell channel).displacement
          common.right.parameter common.left.parameter).trans (Field.mul_comm _ _)
      _ = _ := congrArg (fun value : Rational => (common.right.parameter - common.left.parameter) ^ 2 * value)
        (first.cell_cost channel)
  exact actual.trans_eq ((congrArg (fun value : Rational =>
    16 * ((firstNew.preparation.cell.models.cell channel).localAllowance +
      (lastNew.preparation.cell.models.cell channel).localAllowance) * value) displacement).trans (by ring1))

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent.ShiftedAcquisition

end
