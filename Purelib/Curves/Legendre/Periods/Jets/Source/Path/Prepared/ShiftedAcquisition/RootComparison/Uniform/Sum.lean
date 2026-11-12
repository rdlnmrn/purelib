module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.ShiftedAcquisition.RootComparison.Uniform
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Programs
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.ShiftedAcquisition.Partition
import Purelib.Integration.Polynomial.Gaussian.Cell.Restriction.Chain
import Purelib.Data.Gaussian.Norm.Weighted
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Data.List.OfFn.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Tactic.Ring

/-! # Zero-shifted child integration on the same original parent

The actual local-to-global occurrence map reads the independently prepared
zero-member models. Existing cached source restrictions reassemble the
original source cell. The retained interval widths sum to one, removing
any adaptive child-count factor from the quantitative comparison.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent.ShiftedAcquisition.RootComparison

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Integration.Polynomial.Gaussian
open Purelib.Riemann.Branches
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels.CoveredTracedPath
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath)
open Purelib.Algebra.FiniteSum.Fin (sumFin)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Integration.Partition (Interval)

/-- The ordered zero-child sum differs from its original source-parent integral by both actual allocations.

The given global preparation family, literal occurrence map and retained
restriction banks are consumed unchanged. Signed child comparisons are
derived from the original aligned root transport. Width-weighted finite
Cauchy and exact restriction additivity remove the adaptive child count;
zero widths, repeated occurrences and stationary parents remain included.
-/
theorem source_integral_sum_difference_le
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
    {oldFloor : Nat} {oldStart oldFinish : LiftedPoint 2} {oldPath : LiftedPath 2 oldStart oldFinish}
    {oldStage : Nat} {oldTargets : CellEndpoints.Targets oldPath oldStage}
    (oldPrepared : PreparedParent patch count oldFloor covered oldTargets)
    {newParents : List (CenteredEdge (Fibre.frameCurve target) basis)}
    {newCount newFloor : Nat} {newCover : CoveredParents newCount newParents}
    {newStart newFinish : LiftedPoint 2} {newPath : LiftedPath 2 newStart newFinish}
    {newStage : Nat} {newTargets : CellEndpoints.Targets newPath newStage}
    (newPrepared : PreparedParents (parameter := parameter + 0) (frame := target) (basis := basis)
      (count := newCount) newCover newFloor newTargets)
    (positions : Fin retained.parents.covered.parents.length → Fin newParents.length)
    (entry_eq : ∀ index, newParents[(positions index).val]'(positions index).isLt =
      retained.parents.covered.parents[index.val]'index.isLt)
    (restrictions : Data.Vector.DependentVector (fun index : Fin retained.parents.covered.parents.length =>
      Restrictions (parameter := parameter) (increment := 0) (frame := frame) (basis := basis)
        (target := target) (count := count) (floor := oldFloor)
        (child := newParents[(positions index).val]'(positions index).isLt) oldPrepared))
    (channel : Fin 6) :
    Norm.Basic.normSq ((oldPrepared.preparation.cell.models.cell channel).integralSample -
      sumFin (fun index => ((newPrepared.entry (positions index)).preparation.cell.models.cell
        channel).integralSample)) ≤
      16 * (oldTargets.localBound + newTargets.localBound) * cost parent := by
  let intervals : Fin retained.parents.covered.parents.length → Interval := fun index =>
    (newParents[(positions index).val]'(positions index).isLt).parameterInterval
  let weights := fun index => (intervals index).finish - (intervals index).start
  let firstValues := fun index => ((restrictions.get index).model channel).integralSample
  let lastValues := fun index =>
    ((newPrepared.entry (positions index)).preparation.cell.models.cell channel).integralSample
  let density := 16 * (oldTargets.localBound + newTargets.localBound) * cost parent
  have interval_eq (index : Fin retained.parents.covered.parents.length) :
      intervals index = retained.intervalAt index :=
    congrArg Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge.parameterInterval (entry_eq index)
  have chain : Interval.Chain 0 1 (List.ofFn intervals) :=
    Eq.mpr (congrArg (Interval.Chain 0 1) (Data.List.OfFn.Basic.ofFn_congr interval_eq))
      retained.interval_chain
  have nonnegative (index : Fin retained.parents.covered.parents.length) : 0 ≤ weights index :=
    Eq.mpr (congrArg (fun interval : Interval => 0 ≤ interval.finish - interval.start) (interval_eq index))
      (retained.interval_nonnegative index)
  have widths : sumFin weights = 1 :=
    (Interval.Chain.sum_widths intervals chain).trans (by ring1)
  have bounded (index : Fin retained.parents.covered.parents.length) :
      Norm.Basic.normSq (firstValues index - lastValues index) ≤ density * (weights index) ^ 2 := by
    let next := newPrepared.entry (parameter := parameter + 0) (frame := target) (basis := basis)
      (count := newCount) (floor := newFloor) (covered := newCover) (targets := newTargets) (positions index)
    let cached := restrictions.get index
    have actualBound := comparison.source_integral_difference_le
      (parameter := parameter) (frame := frame) (basis := basis) (parent := parent) (patch := patch)
      (count := count) (covered := covered) (range := range) (target := target) (admitted := admitted)
      (firstSample := firstSample) (firstStep := firstStep) (width := width) (retained := retained)
      (strip := strip) (actual := actual) (actual_eq := actual_eq)
      (child := newParents[(positions index).val]'(positions index).isLt)
      (oldFloor := oldFloor) (oldPath := oldPath) (oldStage := oldStage) (oldTargets := oldTargets)
      (newPatch := (newCover.entry (positions index)).1) (newCount := newCount) (newFloor := newFloor)
      (newCovered := (newCover.entry (positions index)).2) (newPath := newPath)
      (newStage := newStage) (newTargets := newTargets)
      aligned oldPrepared next index (entry_eq index) cached channel
    have displacement := congrArg₂ (fun finish start : Canonical => Norm.Basic.normSq (finish - start))
      (Restrictions.model_finish (parameter := parameter) (increment := 0) (frame := frame)
        (basis := basis) (count := count) (floor := oldFloor) (target := target)
        (child := newParents[(positions index).val]'(positions index).isLt)
        (retained := retained) (index := index) (child_eq := entry_eq index) (source := oldPrepared)
        (restrictions := cached) (channel := channel))
      (Restrictions.model_start (parameter := parameter) (increment := 0) (frame := frame)
        (basis := basis) (count := count) (floor := oldFloor) (target := target)
        (child := newParents[(positions index).val]'(positions index).isLt)
        (retained := retained) (index := index) (child_eq := entry_eq index) (source := oldPrepared)
        (restrictions := cached) (channel := channel))
    have restrictionCost := Cell.Restriction.displacement_normSq
      (oldPrepared.preparation.cell.models.cell channel) (cached.cache channel)
    have childCost := displacement.symm.trans (restrictionCost.trans
      (congrArg (fun cost : Rational => (weights index) ^ 2 * cost) (oldPrepared.cell_cost channel)))
    have allowances := congrArg₂ (fun first last : Rational => first + last)
      (oldPrepared.cell_allowance channel) (next.cell_allowance channel)
    have scalar := congrArg₂ (fun allowance cost : Rational => 16 * allowance * cost) allowances childCost
    have factor_eq : 16 * (oldTargets.localBound + newTargets.localBound) *
        ((weights index) ^ 2 * cost parent) = density * (weights index) ^ 2 := by
      dsimp [density]
      ring1
    exact actualBound.trans_eq (scalar.trans factor_eq)
  have paid := Norm.Weighted.normSq_sumFin_weighted
    (fun index => firstValues index - lastValues index) weights nonnegative bounded
  have sourceSum := Cell.Restriction.integralSample_sum_unit
    (oldPrepared.preparation.cell.models.cell channel) intervals
    (fun index => (restrictions.get index).cache channel) chain
  have reassembled : (oldPrepared.preparation.cell.models.cell channel).integralSample - sumFin lastValues =
      sumFin (fun index => firstValues index - lastValues index) :=
    (congrArg (fun source : Canonical => source - sumFin lastValues) sourceSum.symm).trans
      (Algebra.FiniteSum.Fin.sumFin_sub firstValues lastValues).symm
  have unitPower : (1 : Rational) ^ 2 = 1 := by decide +kernel
  have density_eq : density * (sumFin weights) ^ 2 = density :=
    (congrArg (fun width : Rational => density * width ^ 2) widths).trans
      ((congrArg (fun power : Rational => density * power) unitPower).trans (Field.mul_one_direct density))
  exact (congrArg Norm.Basic.normSq reassembled).trans_le (paid.trans_eq density_eq)

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent.ShiftedAcquisition.RootComparison

end
