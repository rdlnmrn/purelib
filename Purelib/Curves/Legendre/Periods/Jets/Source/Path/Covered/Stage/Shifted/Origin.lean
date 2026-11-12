module

import Purelib.Data.Nat.Order
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Shifted
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.ShiftedRequest.Accuracy.Comparison
public import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.ShiftedAcquisition.RootComparison.Uniform.Sum
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.ShiftedOccurrence.Position.Cells
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Programs
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.ShiftedAcquisition.Restriction
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.ShiftedAcquisition.Alignment
import Purelib.Data.List.DependentProduct
import Purelib.Data.Vector.Dependent
import Purelib.Data.Gaussian.Norm.Sum.Indexed
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Integration.Program.Gaussian.Approximation
import Purelib.Integration.Program.Gaussian.Cached.Basic
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

/-! # Original source agreement of one actual zero-offset member

The original source Request and the independently acquired zero member are
fixed before numerical tolerance. Literal retained block positions regroup
the actual target models. Signed child comparisons and original-parent
finite Cauchy give an original-geometry schedule and executable all-later
comparison indices, without identifying the two Frames or curve records.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.StageAttempt.Requested.Shifted

open Purelib.Data.Nat

open Purelib
open Purelib.Algebra
open Purelib.Algebra.FiniteSum.Fin (sumFin)
open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Gaussian.Equivalence (Equivalent)
open Purelib.Approximation.Rational
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.List (DependentProduct)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (RootChain Named)
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent (startPoint)

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {sourceCurrent sourceFloor sourceRootStage : Nat} {accuracy : AccuracyRequest}
    (source : Requested covered chain sourceCurrent sourceFloor sourceRootStage accuracy)
    (ranges : ParameterRange covered) (allocation : ParameterRange.StripAllocation ranges)
    {target : Paths.Frame (parameter + 0)} {admitted : Norm.Basic.normSq (0 : Canonical) ≤ allocation.bound}
    {widths : Fin (parent :: parents).length → AccuracyRequest}
    {root : Named} {roots : RootChain (parent :: parents) root root}
    {targetCurrent targetFloor targetRootStage : Nat}
    (retained : Shifted (parameter := parameter) (increment := 0) (frame := frame) (basis := basis)
      (target := target) (count := count) source ranges allocation admitted widths roots
      targetCurrent targetFloor targetRootStage)

/-- Both actual global source lists obey a comparison bound determined by the unchanged original parent geometry.

Every old and zero-member model, allowance and stage remains its own
original cache. The existing Position family supplies exact full-prefix
indices; its original regrouping law preserves every ordered occurrence.
The aligned original root comparisons derive each child estimate, while
finite Cauchy counts only the ORIGINAL parents.
-/
theorem source_integral_difference_le
    {firstStage lastStage : Nat}
    {firstTargets : CellEndpoints.Targets chain.path firstStage}
    {lastTargets : CellEndpoints.Targets retained.requested.request.chain.path lastStage}
    (firstPrepared : PreparedParents covered sourceFloor firstTargets)
    (lastPrepared : PreparedParents retained.requested.request.covered targetFloor lastTargets)
    (channel : Fin 6) :
    Norm.Basic.normSq
      ((PathModel.mk ((sources covered firstPrepared chain).cells channel)).integralSample -
        (PathModel.mk ((sources retained.requested.request.covered lastPrepared
          retained.requested.request.chain).cells channel)).integralSample) ≤
      16 * (firstTargets.localBound + lastTargets.localBound) *
        ((parent :: parents).length : Rational) * displacementCost (parent :: parents) := by
  let positions := ShiftedGeometry.Position.Family.build
    (parameter := parameter) (increment := 0) (frame := frame) (basis := basis) (target := target)
    (count := count) (firstParent := parent) (remaining := parents) (covered := covered)
    (floor := sourceFloor) (original := chain.path) (stage := source.selected.stage) (targets := source.targets)
    (prepared := source.prepared) (ranges := ranges) (allocation := allocation) (admitted := admitted)
    (widths := widths) (whole := retained.geometry) (requestIndex := retained.requested.selected.stage)
    (globalFloor := targetFloor) (rootStage := targetRootStage) (oldGeometry := chain) (oldRoots := roots)
    retained.blocks retained.requested.request retained.geometry_eq
  let firstValues := fun outer : Fin (parent :: parents).length =>
    ((firstPrepared.entry outer).preparation.cell.models.cell channel).integralSample
  let lastValues := fun outer : Fin (parent :: parents).length =>
    sumFin (fun inner => ((lastPrepared.entry (positions.entry outer inner).sourceIndex).preparation.cell.models.cell
      channel).integralSample)
  let bounds := fun outer : Fin (parent :: parents).length =>
    16 * (firstTargets.localBound + lastTargets.localBound) *
      PreparedParent.cost ((parent :: parents)[outer.val]'outer.isLt)
  have bounded (outer : Fin (parent :: parents).length) :
      Norm.Basic.normSq (firstValues outer - lastValues outer) ≤ bounds outer := by
    let block := DependentProduct.get (parent :: parents) retained.blocks outer
    let old := firstPrepared.entry outer
    let localPositions := fun inner => (positions.entry outer inner).sourceIndex
    let restrictions : Data.Vector.DependentVector (fun inner : Fin block.shifted.parents.covered.parents.length =>
        PreparedParent.ShiftedAcquisition.Restrictions (parameter := parameter) (increment := 0)
          (frame := frame) (basis := basis) (target := target) (count := count) (floor := sourceFloor)
          (child := (retained.requested.request.shape.val.1 :: retained.requested.request.shape.val.2)[
            (localPositions inner).val]'(localPositions inner).isLt) old) :=
      Data.Vector.DependentVector.ofFn (fun inner => PreparedParent.ShiftedAcquisition.Restrictions.build
        (parameter := parameter) (increment := 0) (frame := frame) (basis := basis) (target := target)
        (count := count) (floor := sourceFloor) (source := old)
        (child := (retained.requested.request.shape.val.1 :: retained.requested.request.shape.val.2)[
          (localPositions inner).val]'(localPositions inner).isLt))
    exact block.comparison.source_integral_sum_difference_le
      (parameter := parameter) (frame := frame) (basis := basis)
      (parent := (parent :: parents)[outer.val]'outer.isLt) (patch := (covered.entry outer).1)
      (count := count) (covered := (covered.entry outer).2) (range := ranges.entry outer) (target := target)
      (retained := block.shifted) (oldFloor := sourceFloor) (oldPath := chain.path)
      (oldStage := firstStage) (oldTargets := firstTargets)
      (newParents := retained.requested.request.shape.val.1 :: retained.requested.request.shape.val.2)
      (newCount := count) (newFloor := targetFloor) (newCover := retained.requested.request.covered)
      (newPath := retained.requested.request.chain.path) (newStage := lastStage) (newTargets := lastTargets)
      block.comparison.align old lastPrepared localPositions
      (fun inner => (positions.entry outer inner).property.1) restrictions channel
  have finite := Norm.Sum.Indexed.normSq_sumFin_sub_le_count_mul_sumFin firstValues lastValues bounds bounded
  have firstSample := integralSample_eq_sumFin covered firstPrepared chain channel
  have lastSample := positions.sample_eq_groups
    (parameter := parameter) (increment := 0) (frame := frame) (basis := basis) (target := target)
    (count := count) (firstParent := parent) (remaining := parents) (covered := covered)
    (floor := sourceFloor) (original := chain.path) (stage := source.selected.stage) (targets := source.targets)
    (prepared := source.prepared) (ranges := ranges) (allocation := allocation) (admitted := admitted)
    (widths := widths) (whole := retained.geometry) (requestIndex := retained.requested.selected.stage)
    (globalFloor := targetFloor) (rootStage := targetRootStage) (oldGeometry := chain) (oldRoots := roots)
    (selectedStage := lastStage) (selectedTargets := lastTargets) lastPrepared retained.geometry_eq channel
  have samples := congrArg₂ (fun first last : Canonical => first - last) firstSample lastSample
  have extracted : sumFin bounds =
      (16 * (firstTargets.localBound + lastTargets.localBound)) * displacementCost (parent :: parents) :=
    FiniteSum.Fin.sumFin_mul_left (16 * (firstTargets.localBound + lastTargets.localBound))
      (fun outer : Fin (parent :: parents).length => PreparedParent.cost ((parent :: parents)[outer.val]'outer.isLt))
  have factor := congrArg (fun total : Rational => ((parent :: parents).length : Rational) * total) extracted
  exact (congrArg Norm.Basic.normSq samples).trans_le (finite.trans_eq (factor.trans (by ring1)))

/-- Every actual later pair of original source and zero-member programme samples obeys one original-geometry radius.

Each allocation is bounded at its OWN programme stage and then at the
common earlier stage. No cross-path allocation monotonicity or shared
nominal Frame is used; both original preparation callbacks are fixed.
-/
theorem source_programmes_later_close (channel : Fin 6) (earlier firstStage lastStage : Nat)
    (firstAfter : earlier ≤ firstStage) (lastAfter : earlier ≤ lastStage) :
    Norm.Basic.normSq
      (((program covered chain source.attempt.preparationFamily channel).model firstStage).integralSample -
        ((retained.requested.request.programme channel).model lastStage).integralSample) ≤
      Geometric.Basic.quarterRadius (errorScale (parent :: parents)) earlier := by
  let firstTargets := CellEndpoints.Targets.build chain.path firstStage
  let lastTargets := CellEndpoints.Targets.build retained.requested.request.chain.path lastStage
  let firstPrepared := source.attempt.preparationFamily firstStage
  let lastPrepared := retained.requested.request.attempt.preparationFamily lastStage
  have firstSample := congrArg PathModel.integralSample
    (program_model covered chain source.attempt.preparationFamily channel firstStage)
  have lastSample := congrArg PathModel.integralSample
    (retained.requested.request.programme_model channel lastStage)
  have original := source_integral_difference_le
    (parameter := parameter) (frame := frame) (basis := basis) (count := count)
    (parent := parent) (parents := parents) (covered := covered) (chain := chain)
    (target := target) (admitted := admitted) (widths := widths) (roots := roots)
    (firstStage := firstStage) (lastStage := lastStage) (firstTargets := firstTargets) (lastTargets := lastTargets)
    source ranges allocation retained firstPrepared lastPrepared channel
  have actual := (congrArg Norm.Basic.normSq
    (congrArg₂ (fun first last : Canonical => first - last) firstSample lastSample)).trans_le original
  have unitNonnegative : (0 : Rational) ≤ 1 := by decide +kernel
  have firstPaid : firstTargets.localBound ≤ Geometric.Basic.quarterRadius 1 earlier :=
    firstTargets.localBound_le_quarterRadius.trans (Geometric.Basic.quarterRadius_antitone unitNonnegative firstAfter)
  have lastPaid : lastTargets.localBound ≤ Geometric.Basic.quarterRadius 1 earlier :=
    lastTargets.localBound_le_quarterRadius.trans (Geometric.Basic.quarterRadius_antitone unitNonnegative lastAfter)
  have densityNonnegative : (0 : Rational) ≤
      16 * ((parent :: parents).length : Rational) * displacementCost (parent :: parents) :=
    Order.Arithmetic.mul_nonneg_direct
      (Order.Arithmetic.mul_nonneg_direct
        (Cast.Order.natCast_le_direct (m := 0) (n := 16) (Nat.zero_le 16))
        (Cast.Order.natCast_le_direct (m := 0) (n := (parent :: parents).length)
          (Nat.zero_le (parent :: parents).length)))
      (displacementCost_nonnegative (parent :: parents))
  have paid := Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
    (Order.Arithmetic.add_le_add_direct firstPaid lastPaid) densityNonnegative
  calc
    _ ≤ (firstTargets.localBound + lastTargets.localBound) *
        (16 * ((parent :: parents).length : Rational) * displacementCost (parent :: parents)) :=
      actual.trans_eq (by ring1)
    _ ≤ (Geometric.Basic.quarterRadius 1 earlier + Geometric.Basic.quarterRadius 1 earlier) *
        (16 * ((parent :: parents).length : Rational) * displacementCost (parent :: parents)) := paid
    _ = _ := by
      rewrite [Geometric.Basic.quarterRadius_eq_mul_pow, Geometric.Basic.quarterRadius_eq_mul_pow]
      unfold errorScale
      ring1

/-- The fixed original source programme and its actual zero member have executable all-later comparison indices.

The actual retained Requests precede tolerance. One original quarter-radius
Selection at the maximum requested start pays every later pair of original
samples. The finite error proof consumes their own preparations, actual
signed child comparisons and full-prefix model readbacks, retaining both
programme owners and every selected or inconclusive checking outcome.
-/
def source_programmes_equivalent (channel : Fin 6) :
    Equivalent (program covered chain source.attempt.preparationFamily channel).approximation
      (retained.requested.request.programme channel).approximation where
  compare := by
    intro firstStart lastStart tolerance positive
    let current := Nat.max firstStart lastStart
    let selected := Geometric.Search.Selection.build (errorScale (parent :: parents))
      (errorScale_nonnegative (parent :: parents)) current tolerance positive
    exact
      { leftIndex := selected.stage
        rightIndex := selected.stage
        left_ge := (Order.le_max_left firstStart lastStart).trans selected.lower
        right_ge := (Order.le_max_right firstStart lastStart).trans selected.lower
        close := by
          intro firstLater lastLater firstAfter lastAfter
          have firstSample := (program covered chain source.attempt.preparationFamily channel).certifiedView_sample
            firstLater
          have lastSample := (retained.requested.request.programme channel).certifiedView_sample lastLater
          have actual := source_programmes_later_close
            (parameter := parameter) (frame := frame) (basis := basis) (count := count)
            (parent := parent) (parents := parents) (covered := covered) (chain := chain)
            (target := target) (admitted := admitted) (widths := widths) (roots := roots)
            source ranges allocation retained channel selected.stage firstLater lastLater firstAfter lastAfter
          exact (congrArg Norm.Basic.normSq
            (congrArg₂ (fun first last : Canonical => first - last) firstSample lastSample)).trans_lt
              (actual.trans_lt (selected.later_accurate (Nat.le_refl _))) }

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.StageAttempt.Requested.Shifted

end
