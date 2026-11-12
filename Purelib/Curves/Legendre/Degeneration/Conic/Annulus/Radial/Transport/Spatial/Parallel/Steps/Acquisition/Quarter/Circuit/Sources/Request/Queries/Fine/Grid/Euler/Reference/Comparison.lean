module

import Purelib.Data.Nat.Order
public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Steps.Acquisition.Quarter.Circuit.Sources.Request.Queries.Fine.Grid.Euler.Stream
import Purelib.Integration.Program.Comparison
import Purelib.Approximation.Gaussian.Geometric
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Tactic.Ring

/-! # Programme comparison on one retained endpoint reference

One original finite execution is stored at accuracy index zero. Its same
endpoint programme is retained once, and the geometric Euler stream keeps
that execution at index zero. Original programme comparisons derive the
named output relation without duplicating the reference execution, using
an approximate target-model replacement or accepting desired closeness.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel

open Purelib.Data
open Purelib.Curves.Legendre.Periods.Jets.Specification
namespace Steps.Acquisition.Quarter.Circuit.Execution.Cache.Sources.Requested.FineCompletion

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Gaussian.Geometric (GeometricApproximation)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Legendre.Periods
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.StageAttempt.Requested.Shifted
open Purelib.Curves.Legendre.Periods.Jets.Variation
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction
open Purelib.Approximation.Rational
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Integration.Program.Gaussian.Basic (RefinementProgram)
open Purelib.Integration
open Steps.Acquisition

/-- The closed multiplier two is nonnegative. -/
private theorem twoNonnegative : (0 : Rational) ≤ 2 := by decide +kernel

/-- The endpoint payment and actual target-programme payment have exact combined scale two plus twice scale. -/
private theorem paired_radius (scale : Rational) (index : Nat) :
    2 * (Geometric.Basic.quarterRadius 1 index + Geometric.Basic.quarterRadius scale index) =
      Geometric.Basic.quarterRadius (2 + 2 * scale) index := by
  have displayed := congrArg₂ (fun first last : Rational => 2 * (first + last))
    (Geometric.Basic.quarterRadius_eq_mul_pow 1 index)
    (Geometric.Basic.quarterRadius_eq_mul_pow scale index)
  have regrouped :
      2 * (1 * (1 / 4 : Rational) ^ index + scale * (1 / 4 : Rational) ^ index) =
        (2 + 2 * scale) * (1 / 4 : Rational) ^ index := by ring1
  exact displayed.trans (regrouped.trans
    (Geometric.Basic.quarterRadius_eq_mul_pow (2 + 2 * scale) index).symm)

section

variable
    {site : Fin 2} {parameter : Canonical} {circuit : Transport.Circuit site parameter}
    {firstFine : Input.Fine circuit.first}
    {sourceOwner : OwnerAt site parameter .first (of_decide_eq_true rfl) firstFine.numerical.initial.lowerEndpoint}
    {agreement : InitialAgreement firstFine.numerical.initial.lowerEndpoint firstFine.numerical.initial.source
      sourceOwner}
    {initial : Input.Realization (.inr firstFine) sourceOwner agreement}
    {secondFine : Input.Fine circuit.second} {thirdFine : Input.Fine circuit.third}
    {fourthFine : Input.Fine circuit.fourth}
    {circuitExecution : Execution.Cache initial (.inr secondFine) (.inr thirdFine) (.inr fourthFine)}
    {frame : Paths.Frame parameter} {basis : Differential 1}
    {modelCount floor : Nat} {sheet : Fin 2}
    {baseStart baseFinish : LiftedPoint 2} {sourcePath : LiftedPath 2 baseStart baseFinish} {stage : Nat}
    {sourceTargets : CellEndpoints.Targets sourcePath stage}
    {sources : Execution.Cache.Sources (frame := frame) (basis := basis) (modelCount := modelCount)
      (floor := floor) (sheet := sheet) (sourceTargets := sourceTargets) circuitExecution}
    {current freshFloor rootStage : Nat} {accuracy : AccuracyRequest}
    {requested : Requested sources current freshFloor rootStage accuracy}
    (completed : FineCompletion requested)
    (firstTen : 10 ≤ firstFine.numerical.depth) (secondTen : 10 ≤ secondFine.numerical.depth)
    (thirdTen : 10 ≤ thirdFine.numerical.depth) (fourthTen : 10 ≤ fourthFine.numerical.depth)
    (direction : Canonical) (moving : direction ≠ 0) (spatial : AccuracyRequest) (commonCurrent : Nat)
    (ranges : PreparedParents.ParameterRange requested.covered)
    (allocation : PreparedParents.ParameterRange.StripAllocation ranges)
    (admitted : Data.Gaussian.Norm.Basic.normSq direction ≤ allocation.bound)
    (widths : Fin (requested.shape.val.1 :: requested.shape.val.2).length → AccuracyRequest)
    (targetCurrent targetFloor targetRootStage : Nat)

namespace EulerExecution

namespace Reference

variable {completed firstTen secondTen thirdTen fourthTen direction moving spatial commonCurrent ranges allocation
    admitted widths targetCurrent targetFloor targetRootStage}
    (reference : Reference completed firstTen secondTen thirdTen fourthTen direction moving spatial commonCurrent
      ranges allocation admitted widths targetCurrent targetFloor targetRootStage)

/-- Use the existing exact-sample programme construction on that same retained-reference geometric owner. -/
def programme (coordinate : Fin 2) : RefinementProgram :=
  Program.Comparison.geometricRefinementProgram (reference.approximation coordinate)

/-- Each programme model is an exact carrier for its computed Euler coordinate. -/
theorem programme_sample (coordinate : Fin 2) (index : Nat) :
    ((reference.programme coordinate).model index).integralSample = reference.sample coordinate index :=
  (Program.Comparison.geometricRefinementProgram_integralSample _ index).trans
    (reference.approximation_sample coordinate index)

/-- Retain the SAME whole original reference target programme with its exact factory equation. -/
@[expose] def Target (coordinate : Fin 2) :=
  { value : RefinementProgram //
    value = reference.val.endpointProgrammes.targetProgram (next := reference.val.endpointShifted)
      (Table.valueIndex coordinate) }

/-- Retain the Euler programme built on this SAME cached reference, including its whole factory equation. -/
@[expose] def Computed (coordinate : Fin 2) :=
  { value : RefinementProgram // value = reference.programme coordinate }

/-- Two original payments give the finite bridge scale from Euler samples to the reference programme. -/
@[expose] def bridgeScale : Rational :=
  2 + 2 * PreparedParents.errorScale (requested.shape.val.1 :: requested.shape.val.2)

/-- That bridge scale is nonnegative, including zero-displacement original covers. -/
theorem bridgeScale_nonnegative : (0 : Rational) ≤ bridgeScale (requested := requested) := by
  have terms := Order.Arithmetic.add_le_add_direct twoNonnegative
    (Order.Arithmetic.mul_nonneg_direct twoNonnegative
      (PreparedParents.errorScale_nonnegative (requested.shape.val.1 :: requested.shape.val.2)))
  exact (Field.zero_add 0).symm.trans_le terms

/-- Actual Euler samples compare to this SAME cached original reference programme at every finite stage.

The middle comparison is derived by targetPrograms_later_close on both
actual shifted preparation families. The own selected stage lies above
the displayed index by its original max-start Selection payment. The two
programme factory equalities supply scalar readbacks only; neither model
nor preparation is rebuilt or replaced by an approximate Euler value.
-/
theorem samples_close (coordinate : Fin 2) (target : reference.Target coordinate)
    (computed : reference.Computed coordinate) (index : Nat) :
    Norm.Basic.normSq
      ((computed.val.model index).integralSample - (target.val.model index).integralSample) ≤
      Geometric.Basic.quarterRadius (bridgeScale (requested := requested)) index := by
  let own := reference.execution index
  have firstPaid : Norm.Basic.normSq (own.values coordinate - own.endpointSample coordinate) ≤
      Geometric.Basic.quarterRadius 1 index :=
    (Norm.Bounds.normSq_sub_symm (own.values coordinate) (own.endpointSample coordinate)).trans_le
      (le_of_lt (own.endpoint_coordinate_lt coordinate))
  have middle := PreparedParents.ShiftedGeometry.ValueBlocks.targetPrograms_later_close
    (firstNext := own.endpointShifted) (lastNext := reference.val.endpointShifted)
    own.endpointProgrammes reference.val.endpointProgrammes (Table.valueIndex coordinate)
    index own.endpointStage index
    ((Nat.Order.le_max_right targetCurrent index).trans own.endpoint_stage_ge) (Nat.le_refl index)
  have targetSample := congrArg
    (fun value : RefinementProgram => (value.model index).integralSample) target.property
  have middleDisplayed : Norm.Basic.normSq
      (own.endpointSample coordinate - (target.val.model index).integralSample) ≤
      Geometric.Basic.quarterRadius
        (PreparedParents.errorScale (requested.shape.val.1 :: requested.shape.val.2)) index :=
    (congrArg Norm.Basic.normSq
      (congrArg₂ (fun first last : Canonical => first - last)
        (own.endpointSample_fixed coordinate) targetSample)).trans_le middle
  have via := Norm.Bounds.normSq_sub_le_via
    (own.values coordinate) (own.endpointSample coordinate) (target.val.model index).integralSample
  have paid := Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Order.Arithmetic.add_le_add_direct firstPaid middleDisplayed) twoNonnegative
  have computedSample :=
    (congrArg (fun value : RefinementProgram => (value.model index).integralSample) computed.property).trans
      ((reference.programme_sample coordinate index).trans (reference.sample_execution coordinate index))
  exact ((congrArg Norm.Basic.normSq (congrArg
    (fun value : Canonical => value - (target.val.model index).integralSample) computedSample)).trans_le
      (via.trans paid)).trans_eq
        (paired_radius (PreparedParents.errorScale (requested.shape.val.1 :: requested.shape.val.2)) index)

/-- The original operational programme comparison consumes these two retained whole programme owners.

All finite schedules and later-sample guarantees come from the existing
Program.Comparison constructor and the internally proved scalar bridge.
No desired operational relation or sample inequality is a supplied input.
-/
def equivalent (coordinate : Fin 2) (target : reference.Target coordinate)
    (computed : reference.Computed coordinate) :
    NamedEquivalent computed.val.output.name target.val.output.name :=
  Program.Comparison.refinementProgram_output_equivalent_of_samples_close computed.val target.val
    (bridgeScale (requested := requested)) (bridgeScale_nonnegative (requested := requested))
    (reference.samples_close coordinate target computed)

end Reference

end EulerExecution

end

end Steps.Acquisition.Quarter.Circuit.Execution.Cache.Sources.Requested.FineCompletion
end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel

end
