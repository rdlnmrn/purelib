module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.ShiftedAcquisition.RootComparison.Source
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.ShiftedAcquisition.Restriction
import Purelib.Curves.Legendre.Periods.Jets.Specification.Table.Comparison
import Purelib.Curves.Legendre.Periods.Jets.Source.Cells
import Purelib.Curves.Legendre.Periods.Jets.Source.Observations
import Purelib.Curves.Legendre.Periods.Jets.Source.Observations.Channels
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Query
import Purelib.Integration.Polynomial.Gaussian.Cell.Primitive
import Purelib.Integration.Polynomial.Gaussian.Cell.Restriction
import Purelib.Polynomial.Ascending.Gaussian.Evaluation
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Riemann.Integration.PreparedConstantModels.Query
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Tactic.Ring

/-! # One actual zero-shifted child and its original source restriction

Actual source/target queries retain their own selected model and power
caches. The given aligned zero-acquisition derives their signed generator
agreement. The original restriction table and physical child endpoints
then pay the coefficient and finite integral comparisons internally.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent.ShiftedAcquisition.RootComparison

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Integration.Polynomial.Gaussian
open Purelib.Polynomial.Ascending.Gaussian
open Purelib.Riemann.Branches
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels.CoveredTracedPath
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath)

/-- The actual zero-shifted child polynomial differs from its original source restriction by both paid allowances.

Each bounded query uses one genuine original source answer/zero-Step and
one target answer. The aligned child/Point comparison derives their signed
root relation; the two original coefficient states pay their own errors.
-/
theorem source_polynomial_difference_le
    {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis} {patch : PreparedPatch parent} {count : Nat}
    {covered : (patch.neighborhood count).box.Contains (parent.edge.point 1)}
    {range : Variation.Point.Range (patch.neighborhood count)} {target : Paths.Frame (parameter + 0)}
    {admitted : Norm.Basic.normSq (0 : Canonical) ≤ range.shiftedBound}
    {firstSample : ContinuedNeighborhood.Point (patch.neighborhood count) (startPoint parent).coordinate}
    {firstStep : Variation.Point.Step firstSample 0} {width : AccuracyRequest}
    {retained : ShiftedAcquisition (covered := covered) range target admitted firstStep width}
    {strip : Norm.Basic.normSq (0 : Canonical) ≤ range.stripBound}
    {actual : OwnerPath (Fibre.frameCurve target).polynomial (startPoint parent).coordinate firstStep.owner
      (finishPoint parent).coordinate retained.acquired.traced.finishOwner}
    {actual_eq : actual = retained.acquired.traced.trace.get}
    (comparison : RootComparison retained strip actual actual_eq)
    (aligned : Acquisition.Segment.RootComparisons.Alignment comparison.paths comparison.firstReference)
    {child : CenteredEdge (Fibre.frameCurve target) basis}
    {oldFloor : Nat} {oldStart oldFinish : LiftedPoint 2} {oldPath : LiftedPath 2 oldStart oldFinish}
    {oldStage : Nat} {oldTargets : CellEndpoints.Targets oldPath oldStage}
    (oldPrepared : PreparedParent patch count oldFloor covered oldTargets)
    {newPatch : PreparedPatch child} {newCount newFloor : Nat}
    {newCovered : (newPatch.neighborhood newCount).box.Contains (child.edge.point 1)}
    {newStart newFinish : LiftedPoint 2} {newPath : LiftedPath 2 newStart newFinish}
    {newStage : Nat} {newTargets : CellEndpoints.Targets newPath newStage}
    (newPrepared : PreparedParent newPatch newCount newFloor newCovered newTargets)
    (index : Fin retained.parents.covered.parents.length)
    (child_eq : child = retained.parents.covered.parents[index.val]'index.isLt)
    (restrictions : Restrictions (parameter := parameter) (increment := 0) (frame := frame) (basis := basis)
      (target := target) (count := count) (floor := oldFloor) (child := child) oldPrepared)
    (channel : Fin 6)
    (input : Rational) (inside : 0 ≤ input ∧ input ≤ 1) :
    Norm.Basic.normSq
      (Evaluation.eval (restrictions.model channel).polynomial (Cast.Path.ofCoordinate input) -
        Evaluation.eval (newPrepared.preparation.cell.models.cell channel).polynomial (Cast.Path.ofCoordinate input)) ≤
      8 * ((oldPrepared.preparation.cell.models.cell channel).localAllowance +
        (newPrepared.preparation.cell.models.cell channel).localAllowance) := by
  let fraction := PreparedSheetContinuation.parameterAt child.edge.left child.edge.request input
  let oldInside := PreparedSheetContinuation.parameterAt_inside child.edge.left child.edge.request
    child.edge.ordered input inside
  let paid := admitted.trans range.shiftedBound_le_bound
  let advanced := oldPrepared.advanceQuery (parameter := parameter) (frame := frame)
    (basis := basis) (parent := parent) (patch := patch) (count := count) (covered := covered)
    range fraction oldInside.1 oldInside.2 0 paid
  let observed := newPrepared.preparation.query.observe target input inside.1 inside.2
  let direct := Riemann.Integration.PreparedConstantModels.PreparedEdge.Query.build child.edge input inside
  let roots := comparison.querySourceEquivalent (parameter := parameter) (frame := frame) (basis := basis)
    (parent := parent) (patch := patch) (count := count) (covered := covered) (range := range) (target := target)
    (admitted := admitted) (firstSample := firstSample) (firstStep := firstStep) (width := width)
    (retained := retained) (strip := strip) (actual := actual) (actual_eq := actual_eq) (child := child)
    (sourceSample := advanced.1.retained.sample) aligned oldPrepared newPrepared input inside advanced.2
    observed.retained.sample index child_eq direct
  have oldFactory := oldPrepared.advanceQuery_observation (parameter := parameter) (frame := frame)
    (basis := basis) (parent := parent) (patch := patch) (count := count) (covered := covered)
    range fraction oldInside.1 oldInside.2 0 paid
  have oldRoot := oldPrepared.preparation.query.channel_root_name (parameter := parameter)
    (cell := oldPrepared.preparation.cell) frame fraction oldInside.1 oldInside.2 advanced.1 oldFactory channel
  have newRoot := newPrepared.preparation.query.channel_root_name (parameter := parameter + 0)
    (cell := newPrepared.preparation.cell) target input inside.1 inside.2 observed rfl channel
  have signed := NamedEquivalent.transport oldRoot.symm newRoot.symm roots.symm
  have oldPoint := advanced.1.channel_point (parameter := parameter) (frame := frame)
    (count := oldPrepared.preparation.cell.count) (patch := oldPrepared.preparation.cell.patch)
    (cache := oldPrepared.preparation.cell.cache) (floor := oldPrepared.preparation.cell.floor)
    (target := oldPrepared.preparation.cell.target) (allowance := oldPrepared.preparation.cell.allowance)
    (request := oldPrepared.preparation.cell.request) (uniformBounds := oldPrepared.preparation.query.bounds)
    (uniformFloor := oldPrepared.preparation.query.floor)
    (models := oldPrepared.preparation.cell.models) (requests := oldPrepared.preparation.query.requests)
    (input := fraction) channel
  have newPoint := observed.channel_point (parameter := parameter + 0) (frame := target)
    (count := newPrepared.preparation.cell.count) (patch := newPrepared.preparation.cell.patch)
    (cache := newPrepared.preparation.cell.cache) (floor := newPrepared.preparation.cell.floor)
    (target := newPrepared.preparation.cell.target) (allowance := newPrepared.preparation.cell.allowance)
    (request := newPrepared.preparation.cell.request) (uniformBounds := newPrepared.preparation.query.bounds)
    (uniformFloor := newPrepared.preparation.query.floor)
    (models := newPrepared.preparation.cell.models) (requests := newPrepared.preparation.query.requests)
    (input := input) channel
  have points := oldPoint.trans ((oldPrepared.queryPoint_eq fraction).trans
    ((retained.originalPoint_eq index child_eq input).symm.trans
      ((newPrepared.queryPoint_eq input).symm.trans newPoint.symm)))
  have allowances := congrArg₂ (fun first last : Rational => first + last)
    (oldPrepared.preparation.cell.models.cell_allowance channel)
    (newPrepared.preparation.cell.models.cell_allowance channel)
  have positive : 0 < (oldPrepared.preparation.cell.models.cell channel).localAllowance +
      (newPrepared.preparation.cell.models.cell channel).localAllowance :=
    (Order.Arithmetic.add_pos_of_pos_of_nonneg_direct oldPrepared.preparation.query.positive
      newPrepared.preparation.query.positive.le).trans_eq allowances.symm
  have bounded := Specification.Table.observation_difference_le
    (firstParameter := parameter) (lastParameter := parameter + 0) (firstFrame := frame) (lastFrame := target)
    (firstCell := oldPrepared.preparation.cell.models.cell channel)
    (lastCell := newPrepared.preparation.cell.models.cell channel) (firstInput := fraction) (lastInput := input)
    channel (advanced.1.channel channel) (observed.channel channel) (Basic.add_zero parameter).symm
    points signed positive
  have mapped : Cell.Restriction.parameter child.edge.left.parameter child.edge.request.endpoint.parameter input =
      fraction :=
    (PreparedSheetContinuation.parameterAt_eq_affine child.edge.left child.edge.request input).symm
  have value := (Cell.Restriction.eval_eq (oldPrepared.preparation.cell.models.cell channel)
    (restrictions.cache channel) input).trans
      (congrArg (fun parameter : Rational => Evaluation.eval
        (oldPrepared.preparation.cell.models.cell channel).polynomial (Cast.Path.ofCoordinate parameter)) mapped)
  exact (congrArg (fun value : Canonical => Norm.Basic.normSq
    (value - Evaluation.eval (newPrepared.preparation.cell.models.cell channel).polynomial
      (Cast.Path.ofCoordinate input))) value).trans_le bounded

/-- The same retained source restriction and actual child integral pay sixteen times the actual allowance sum.

Their original physical endpoints and restriction table remain unchanged.
The coefficient comparison above and the finite polynomial primitive
estimate supply the bound; no primitive constant or period relation is
assumed, including for stationary or repeated child occurrences.
-/
theorem source_integral_difference_le
    {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis} {patch : PreparedPatch parent} {count : Nat}
    {covered : (patch.neighborhood count).box.Contains (parent.edge.point 1)}
    {range : Variation.Point.Range (patch.neighborhood count)} {target : Paths.Frame (parameter + 0)}
    {admitted : Norm.Basic.normSq (0 : Canonical) ≤ range.shiftedBound}
    {firstSample : ContinuedNeighborhood.Point (patch.neighborhood count) (startPoint parent).coordinate}
    {firstStep : Variation.Point.Step firstSample 0} {width : AccuracyRequest}
    {retained : ShiftedAcquisition (covered := covered) range target admitted firstStep width}
    {strip : Norm.Basic.normSq (0 : Canonical) ≤ range.stripBound}
    {actual : OwnerPath (Fibre.frameCurve target).polynomial (startPoint parent).coordinate firstStep.owner
      (finishPoint parent).coordinate retained.acquired.traced.finishOwner}
    {actual_eq : actual = retained.acquired.traced.trace.get}
    (comparison : RootComparison retained strip actual actual_eq)
    (aligned : Acquisition.Segment.RootComparisons.Alignment comparison.paths comparison.firstReference)
    {child : CenteredEdge (Fibre.frameCurve target) basis}
    {oldFloor : Nat} {oldStart oldFinish : LiftedPoint 2} {oldPath : LiftedPath 2 oldStart oldFinish}
    {oldStage : Nat} {oldTargets : CellEndpoints.Targets oldPath oldStage}
    (oldPrepared : PreparedParent patch count oldFloor covered oldTargets)
    {newPatch : PreparedPatch child} {newCount newFloor : Nat}
    {newCovered : (newPatch.neighborhood newCount).box.Contains (child.edge.point 1)}
    {newStart newFinish : LiftedPoint 2} {newPath : LiftedPath 2 newStart newFinish}
    {newStage : Nat} {newTargets : CellEndpoints.Targets newPath newStage}
    (newPrepared : PreparedParent newPatch newCount newFloor newCovered newTargets)
    (index : Fin retained.parents.covered.parents.length)
    (child_eq : child = retained.parents.covered.parents[index.val]'index.isLt)
    (restrictions : Restrictions (parameter := parameter) (increment := 0) (frame := frame) (basis := basis)
      (target := target) (count := count) (floor := oldFloor) (child := child) oldPrepared)
    (channel : Fin 6) :
    Norm.Basic.normSq ((restrictions.model channel).integralSample -
      (newPrepared.preparation.cell.models.cell channel).integralSample) ≤
      16 * ((oldPrepared.preparation.cell.models.cell channel).localAllowance +
        (newPrepared.preparation.cell.models.cell channel).localAllowance) *
          Norm.Basic.normSq ((finishPoint child).coordinate - (startPoint child).coordinate) := by
  have startEq := (Restrictions.model_start (parameter := parameter) (increment := 0) (frame := frame)
    (basis := basis) (count := count) (floor := oldFloor) (target := target) (child := child)
    (retained := retained) (index := index) (child_eq := child_eq) (source := oldPrepared)
    (restrictions := restrictions) (channel := channel)).trans
      (newPrepared.preparation.cell.models.cell_start channel).symm
  have finishEq := (Restrictions.model_finish (parameter := parameter) (increment := 0) (frame := frame)
    (basis := basis) (count := count) (floor := oldFloor) (target := target) (child := child)
    (retained := retained) (index := index) (child_eq := child_eq) (source := oldPrepared)
    (restrictions := restrictions) (channel := channel)).trans
      (newPrepared.preparation.cell.models.cell_finish channel).symm
  have bounded := Cell.Primitive.integral_difference_le (restrictions.model channel)
    (newPrepared.preparation.cell.models.cell channel) startEq finishEq
    (8 * ((oldPrepared.preparation.cell.models.cell channel).localAllowance +
      (newPrepared.preparation.cell.models.cell channel).localAllowance)) (by
        intro input inside
        exact comparison.source_polynomial_difference_le (parameter := parameter) (frame := frame) (basis := basis)
          (parent := parent) (patch := patch) (count := count) (covered := covered) (range := range) (target := target)
          (admitted := admitted) (firstSample := firstSample) (firstStep := firstStep) (width := width)
          (retained := retained) (strip := strip) (actual := actual) (actual_eq := actual_eq) (child := child)
          aligned oldPrepared newPrepared index child_eq restrictions channel input inside)
  have displacement : (restrictions.model channel).displacement =
      (finishPoint child).coordinate - (startPoint child).coordinate :=
    congrArg₂ (fun finish start : Canonical => finish - start)
      (Restrictions.model_finish (parameter := parameter) (increment := 0) (frame := frame)
        (basis := basis) (count := count) (floor := oldFloor) (target := target) (child := child)
        (retained := retained) (index := index) (child_eq := child_eq) (source := oldPrepared)
        (restrictions := restrictions) (channel := channel))
      (Restrictions.model_start (parameter := parameter) (increment := 0) (frame := frame)
        (basis := basis) (count := count) (floor := oldFloor) (target := target) (child := child)
        (retained := retained) (index := index) (child_eq := child_eq) (source := oldPrepared)
        (restrictions := restrictions) (channel := channel))
  have scalar := congrArg (fun movement : Canonical =>
    2 * (8 * ((oldPrepared.preparation.cell.models.cell channel).localAllowance +
      (newPrepared.preparation.cell.models.cell channel).localAllowance)) * Norm.Basic.normSq movement) displacement
  exact bounded.trans_eq (scalar.trans (by ring1))

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent.ShiftedAcquisition.RootComparison

end
