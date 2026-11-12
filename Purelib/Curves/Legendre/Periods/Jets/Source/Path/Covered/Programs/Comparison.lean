module

import Purelib.Data.Nat.Order
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Programs
public import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Integration.Program.Gaussian.Approximation
import Purelib.Integration.Program.Gaussian.Cached.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

/-! # Independent adaptive preparations on one retained covered cycle

Both original numerical preparation rules and both actual precision rules
remain distinct. Their own programme-floor witnesses pay an arbitrary
common earlier index, without monotonicity of either precision selector.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents

open Purelib.Data.Nat

open Purelib
open Purelib.Approximation.Gaussian.Equivalence (Equivalent)
open Purelib.Approximation.Rational
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1} {count : Nat}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)} {point : LiftedPoint 2}
    (covered : CoveredParents count parents)
    (chain : CenteredPathChain parents (start := point) (finish := point))
    {firstFloor lastFloor : Nat} (firstPrecision lastPrecision : Nat → Nat)
    (firstRequests : (index : Nat) → {value : CellEndpoints.Targets chain.path (firstPrecision index) //
      value = CellEndpoints.Targets.build chain.path (firstPrecision index)})
    (lastRequests : (index : Nat) → {value : CellEndpoints.Targets chain.path (lastPrecision index) //
      value = CellEndpoints.Targets.build chain.path (lastPrecision index)})
    (first : (index : Nat) → PreparedParents covered firstFloor (firstRequests index).val)
    (last : (index : Nat) → PreparedParents covered lastFloor (lastRequests index).val)
    (firstPaid : ∀ index, index ≤ firstPrecision index) (lastPaid : ∀ index, index ≤ lastPrecision index)

include firstPaid lastPaid in
/-- All sufficiently late original model samples compare at their own actual precision and construction floors.

The original two-preparation integral estimate retains every ordered cell.
Each actual local allocation is paid at its own stage and then at the
common earlier index; no old model or request is retagged or replaced.
-/
theorem independent_later_closeAtPrecision (channel : Fin 6) (earlier firstIndex lastIndex : Nat)
    (firstAfter : earlier ≤ firstIndex) (lastAfter : earlier ≤ lastIndex) :
    Norm.Basic.normSq
      ((modelAtPrecision covered chain firstPrecision firstRequests first channel firstIndex).integralSample -
        (modelAtPrecision covered chain lastPrecision lastRequests last channel lastIndex).integralSample) ≤
      Geometric.Basic.quarterRadius (errorScale parents) earlier := by
  let originalTargets := CellEndpoints.Targets.build chain.path earlier
  let leftTargets := (firstRequests firstIndex).val
  let rightTargets := (lastRequests lastIndex).val
  have leftOrder : leftTargets.localBound ≤ originalTargets.localBound :=
    originalTargets.localBound_antitone leftTargets (firstAfter.trans (firstPaid firstIndex))
  have rightOrder : rightTargets.localBound ≤ originalTargets.localBound :=
    originalTargets.localBound_antitone rightTargets (lastAfter.trans (lastPaid lastIndex))
  have localSum : leftTargets.localBound + rightTargets.localBound ≤ 2 * originalTargets.localBound :=
    (Order.Arithmetic.add_le_add_direct leftOrder rightOrder).trans_eq (by ring1)
  have geometryNonnegative : 0 ≤ (parents.length : Rational) * displacementCost parents :=
    Order.Arithmetic.mul_nonneg_direct
      (Cast.Order.natCast_le_direct (m := 0) (n := parents.length) (Nat.zero_le parents.length))
      (displacementCost_nonnegative parents)
  have scaled := Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
    (Order.Arithmetic.mul_le_mul_of_nonneg_left_direct localSum (by decide +kernel : (0 : Rational) ≤ 16))
    geometryNonnegative
  have originalBound := integral_difference_le covered (first firstIndex) (last lastIndex) chain channel
  calc
    _ ≤ 16 * (leftTargets.localBound + rightTargets.localBound) *
        (parents.length : Rational) * displacementCost parents := originalBound
    _ = (16 * (leftTargets.localBound + rightTargets.localBound)) *
        ((parents.length : Rational) * displacementCost parents) := by ring1
    _ ≤ (16 * (2 * originalTargets.localBound)) *
        ((parents.length : Rational) * displacementCost parents) := scaled
    _ = errorScale parents * originalTargets.localBound := by unfold errorScale; ring1
    _ ≤ _ := originalTargets.mul_localBound_le_quarterRadius
      (errorScale parents) (errorScale_nonnegative parents)

/-- Compute genuine all-later model-stream comparison indices for both independent actual preparation rules.

The two fixed programmes retain their source owners and models. A single
executable quarter-radius Selection starts above both requested floors;
its original comparison certificate concerns programme MODEL indices.
-/
def programsAtPrecision_equivalent (channel : Fin 6) :
    Equivalent
      (programAtPrecision covered chain firstPrecision firstRequests first firstPaid channel).approximation
      (programAtPrecision covered chain lastPrecision lastRequests last lastPaid channel).approximation where
  compare := by
    intro firstStart lastStart tolerance positive
    let selected := Geometric.Search.Selection.build (errorScale parents) (errorScale_nonnegative parents)
      (Nat.max firstStart lastStart) tolerance positive
    exact
      { leftIndex := selected.stage
        rightIndex := selected.stage
        left_ge := (Order.le_max_left firstStart lastStart).trans selected.lower
        right_ge := (Order.le_max_right firstStart lastStart).trans selected.lower
        close := by
          intro firstLater lastLater firstAfter lastAfter
          have leftSample :=
            ((programAtPrecision covered chain firstPrecision firstRequests first firstPaid
              channel).certifiedView_sample firstLater).trans (congrArg PathModel.integralSample
                (programAtPrecision_model covered chain firstPrecision firstRequests first firstPaid
                  channel firstLater))
          have rightSample :=
            ((programAtPrecision covered chain lastPrecision lastRequests last lastPaid channel).certifiedView_sample
              lastLater).trans (congrArg PathModel.integralSample
                (programAtPrecision_model covered chain lastPrecision lastRequests last lastPaid
                  channel lastLater))
          have actual := independent_later_closeAtPrecision
            (parameter := parameter) (frame := frame) (basis := basis) (count := count)
            covered chain firstPrecision lastPrecision firstRequests lastRequests first last firstPaid lastPaid
            channel selected.stage firstLater lastLater firstAfter lastAfter
          exact (congrArg Norm.Basic.normSq
            (congrArg₂ (fun left right : Canonical => left - right) leftSample rightSample)).trans_lt
              (actual.trans_lt (selected.later_accurate (Nat.le_refl _))) }

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents

end
