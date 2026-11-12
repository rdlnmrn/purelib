module

import Purelib.Data.Nat.Order
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.ShiftedOccurrence.Arithmetic.Global.Comparison
public import Purelib.Integration.Program.Gaussian.Name
public import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Integration.Program.Gaussian.Approximation
import Purelib.Integration.Program.Gaussian.Cached.Basic
import Purelib.Approximation.Gaussian.Equivalence.Sampling
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

/-! # Actual target programme identity on two retained shifted affine cycles

At every two actual programme stages, the original preparation families
supply their genuine whole model/query caches on the two original acquired
spines. Common dyadic restrictions derive the comparison; the original
Targets schedule and a finite quarter-radius selection return actual tail
indices. Both original progressive programmes, output names and certified
period owners remain distinct inputs throughout.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.ShiftedGeometry

open Purelib.Data
open Purelib
open Purelib.Algebra
open Purelib.Algebra.FiniteSum.Fin (sumFin)
open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Gaussian.Equivalence (Equivalent NamedEquivalent)
open Purelib.Approximation.Gaussian.Name.Basic (Named)
open Purelib.Approximation.Rational
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Algebraic.Period.Jets (CertifiedPeriodProgram)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.List (DependentProduct)
open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Integration.Polynomial.Gaussian.Cell.Basic (CellModel)
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)
open Purelib.Integration.Program.Gaussian.Basic (RefinementProgram)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision
open Purelib.Riemann.Meshes
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent (startPoint)

variable {parameter increment : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {target : Paths.Frame (parameter + increment)} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {admitted : Norm.Basic.normSq increment ≤ allocation.bound}
    {firstWidths lastWidths : Fin (parent :: parents).length → AccuracyRequest}
    {root : Named} {roots : Riemann.Topology.PreparedRefinementRootChains.RootChain (parent :: parents) root root}
    {firstSpatial lastSpatial : AccuracyRequest} {nonzero : increment ≠ 0}
    {firstSourceCurrent firstSourceFloor firstSourceRootStage firstTargetCurrent : Nat}
    {firstTargetFloor firstTargetRootStage : Nat}
    {lastSourceCurrent lastSourceFloor lastSourceRootStage lastTargetCurrent lastTargetFloor lastTargetRootStage : Nat}
    {firstSource : StageAttempt.Requested covered chain firstSourceCurrent firstSourceFloor firstSourceRootStage
      (firstSpatial.minimum (Variation.Sampling.incrementRequest increment nonzero))}
    {lastSource : StageAttempt.Requested covered chain lastSourceCurrent lastSourceFloor lastSourceRootStage
      (lastSpatial.minimum (Variation.Sampling.incrementRequest increment nonzero))}
    {firstNext : StageAttempt.Requested.Shifted (target := target) firstSource ranges allocation admitted
      firstWidths roots
      firstTargetCurrent firstTargetFloor firstTargetRootStage}
    {lastNext : StageAttempt.Requested.Shifted (target := target) lastSource ranges allocation admitted lastWidths roots
      lastTargetCurrent lastTargetFloor lastTargetRootStage}
    (firstRetained : ValueBlocks (next := firstNext)) (lastRetained : ValueBlocks (next := lastNext))

namespace ValueBlocks

/-- Both actual target programme samples have the same finite fixed-original-geometry cross-stage bound.

The two whole preparation families are evaluated once at their own original
stages. New auxiliary restriction banks are materialized before comparison
callbacks. Historical source/target requests are neither replayed nor
retagged; both programme models are their actual original stage outputs.
-/
theorem targetPrograms_difference_le (channel : Fin 6) (firstStage lastStage : Nat) :
    Norm.Basic.normSq
      (((firstRetained.targetProgram channel).model firstStage).integralSample -
        ((lastRetained.targetProgram channel).model lastStage).integralSample) ≤
      16 * ((CellEndpoints.Targets.build firstNext.requested.request.chain.path firstStage).localBound +
        (CellEndpoints.Targets.build lastNext.requested.request.chain.path lastStage).localBound) *
          ((parent :: parents).length : Rational) * displacementCost (parent :: parents) := by
  let firstPrepared := firstNext.requested.request.attempt.preparationFamily firstStage
  let lastPrepared := lastNext.requested.request.attempt.preparationFamily lastStage
  let cached := CommonRestrictions.build firstRetained lastRetained firstPrepared lastPrepared
  have actual := CommonRestrictions.integral_difference_le firstRetained lastRetained firstPrepared lastPrepared
    cached channel
  have models := congrArg₂ (fun first last : Canonical => first - last)
    (firstRetained.targetProgram_sample channel firstStage) (lastRetained.targetProgram_sample channel lastStage)
  exact (congrArg Norm.Basic.normSq models).trans_le actual

/-- A common earlier stage bounds every actual cross-programme later pair by the SAME original geometry schedule. -/
theorem targetPrograms_later_close (channel : Fin 6) (earlier firstStage lastStage : Nat)
    (firstAfter : earlier ≤ firstStage) (lastAfter : earlier ≤ lastStage) :
    Norm.Basic.normSq
      (((firstRetained.targetProgram channel).model firstStage).integralSample -
        ((lastRetained.targetProgram channel).model lastStage).integralSample) ≤
      Geometric.Basic.quarterRadius (errorScale (parent :: parents)) earlier := by
  let firstTargets := CellEndpoints.Targets.build firstNext.requested.request.chain.path firstStage
  let lastTargets := CellEndpoints.Targets.build lastNext.requested.request.chain.path lastStage
  have unitNonnegative : (0 : Rational) ≤ 1 := by decide +kernel
  have firstPaid : firstTargets.localBound ≤ Geometric.Basic.quarterRadius 1 earlier :=
    firstTargets.localBound_le_quarterRadius.trans (Geometric.Basic.quarterRadius_antitone unitNonnegative firstAfter)
  have lastPaid : lastTargets.localBound ≤ Geometric.Basic.quarterRadius 1 earlier :=
    lastTargets.localBound_le_quarterRadius.trans (Geometric.Basic.quarterRadius_antitone unitNonnegative lastAfter)
  have densityNonnegative : (0 : Rational) ≤
      16 * ((parent :: parents).length : Rational) * displacementCost (parent :: parents) :=
    Order.Arithmetic.mul_nonneg_direct
      (Order.Arithmetic.mul_nonneg_direct
        (show (0 : Rational) ≤ 16 from Fraction.Cast.Order.natCast_le_direct (Nat.zero_le 16))
        (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le (parent :: parents).length)))
      (displacementCost_nonnegative (parent :: parents))
  have paid := Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
    (Order.Arithmetic.add_le_add_direct firstPaid lastPaid) densityNonnegative
  have original := targetPrograms_difference_le firstRetained lastRetained channel firstStage lastStage
  calc
    _ ≤ (firstTargets.localBound + lastTargets.localBound) *
        (16 * ((parent :: parents).length : Rational) * displacementCost (parent :: parents)) :=
      original.trans_eq (by ring1)
    _ ≤ (Geometric.Basic.quarterRadius 1 earlier + Geometric.Basic.quarterRadius 1 earlier) *
        (16 * ((parent :: parents).length : Rational) * displacementCost (parent :: parents)) := paid
    _ = _ := by
      rewrite [Geometric.Basic.quarterRadius_eq_mul_pow, Geometric.Basic.quarterRadius_eq_mul_pow]
      unfold errorScale
      ring1

/-- The two SAME actual target approximation owners admit executable comparison indices on the original fixed cycle.

A finite quarter-radius Selection at the maximum requested start pays the
computed original-geometry scale. The comparison keeps both original
approximation owners and chosen stages, with a certificate for every actual
later pair. No desired period equality is an input.
-/
def targetPrograms_equivalent (channel : Fin 6) :
    Equivalent (firstRetained.targetProgram channel).approximation
      (lastRetained.targetProgram channel).approximation where
  compare := by
    intro firstStart lastStart tolerance positive
    let current := Nat.max firstStart lastStart
    let selected := Geometric.Search.Selection.build (errorScale (parent :: parents))
      (errorScale_nonnegative (parent :: parents)) current tolerance positive
    exact
      { leftIndex := selected.stage
        rightIndex := selected.stage
        left_ge := (Nat.Order.le_max_left firstStart lastStart).trans selected.lower
        right_ge := (Nat.Order.le_max_right firstStart lastStart).trans selected.lower
        close := by
          intro firstLater lastLater firstAfter lastAfter
          have firstSample : (firstRetained.targetProgram channel).approximation.sample firstLater =
              ((firstRetained.targetProgram channel).model firstLater).integralSample :=
            (firstRetained.targetProgram channel).certifiedView_sample firstLater
          have lastSample : (lastRetained.targetProgram channel).approximation.sample lastLater =
              ((lastRetained.targetProgram channel).model lastLater).integralSample :=
            (lastRetained.targetProgram channel).certifiedView_sample lastLater
          have actual := targetPrograms_later_close firstRetained lastRetained channel selected.stage
            firstLater lastLater firstAfter lastAfter
          exact (congrArg Norm.Basic.normSq
            (congrArg₂ (fun first last : Canonical => first - last) firstSample lastSample)).trans_lt
              (actual.trans_lt (selected.later_accurate (Nat.le_refl _))) }

/-- The original target programme output names agree operationally without replacing either programme. -/
def targetOutputs_equivalent (channel : Fin 6) :
    NamedEquivalent (firstRetained.targetProgram channel).output.name
      (lastRetained.targetProgram channel).output.name :=
  (targetPrograms_equivalent firstRetained lastRetained channel).toNamed

/-- Both original certified target-period streams retain that derived same-cycle operational agreement.

The exact retained integral readbacks identify the original programme
owners inside both certificates. The two lifted-cycle/period owners stay
separate; no canonical curved-cycle attachment is asserted here.
-/
def targetCertified_equivalent (channel : Fin 6) :
    NamedEquivalent (firstRetained.targetCertified channel).integral.output.name
      (lastRetained.targetCertified channel).integral.output.name :=
  NamedEquivalent.transport
    (congrArg (fun value : RefinementProgram => value.output.name)
      (firstRetained.targetCertified_integral channel).symm)
    (congrArg (fun value : RefinementProgram => value.output.name)
      (lastRetained.targetCertified_integral channel).symm)
    (targetOutputs_equivalent firstRetained lastRetained channel)

end ValueBlocks

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.ShiftedGeometry

end
