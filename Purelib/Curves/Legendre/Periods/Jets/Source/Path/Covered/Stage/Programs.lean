module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Accuracy
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Programs
import Purelib.Curves.Legendre.Periods.Jets.Specification.Table
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

/-! # Actual requested source samples and retained fixed-cycle programmes

The sufficient-stage source request and a progressive programme retain
independent actual preparation caches on the same original covered spine.
Their original Targets pay the finite integral comparison. No new source,
query, endpoint observation or programme is constructed by the comparison.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.StageAttempt.Requested

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Curves.Hyperelliptic.Integration.Algebraic.Period.Jets (CertifiedPeriodProgram)
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
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents)
      (start := PreparedParent.startPoint parent) (finish := PreparedParent.startPoint parent)}
    {current floor rootStage : Nat} {accuracy : AccuracyRequest}
    (source : Requested covered chain current floor rootStage accuracy)
    (preparations : (index : Nat) →
      PreparedParents covered floor (CellEndpoints.Targets.build chain.path index))

/-- The actual requested source and any sufficiently late original programme sample pay a fixed-geometry bound.

Both preparation families and their actual query factories remain inputs.
The programme's exact original cell-list readback and the same-patch
integral comparison derive the bound from the two retained Targets.
Only the original finite parent count and displacement cost enter its scale.
-/
theorem program_difference_le (channel : Fin 6) (index : Nat) (after : source.selected.stage ≤ index)
    (programme : CertifiedPeriodProgram (Fibre.frameCurve frame) (Specification.Table.forms parameter channel)
      (constantCycle chain))
    (cells_eq : (programme.integral.model index).cells =
      (sources covered (preparations index) chain).cells channel) :
    Norm.Basic.normSq
      ((programme.integral.model index).integralSample -
        (PathModel.mk ((sources covered source.prepared chain).cells channel)).integralSample) ≤
      errorScale (parent :: parents) * accuracy.tolerance := by
  let originalTargets := CellEndpoints.Targets.build chain.path index
  have localOrder : originalTargets.localBound ≤ source.targets.localBound :=
    source.targets.localBound_antitone originalTargets after
  have localSum : originalTargets.localBound + source.targets.localBound ≤
      2 * source.targets.localBound :=
    (Order.Arithmetic.add_le_add_direct localOrder (Order.Basic.le_refl source.targets.localBound)).trans_eq
      (by ring1)
  have geometryNonnegative : 0 ≤ ((parent :: parents).length : Rational) *
      displacementCost (parent :: parents) :=
    Order.Arithmetic.mul_nonneg_direct
      (Cast.Order.natCast_le_direct (m := 0) (n := (parent :: parents).length)
        (Nat.zero_le (parent :: parents).length))
      (displacementCost_nonnegative (parent :: parents))
  have scaled := Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
    (Order.Arithmetic.mul_le_mul_of_nonneg_left_direct localSum (by decide +kernel : (0 : Rational) ≤ 16))
    geometryNonnegative
  have exactSample : (programme.integral.model index).integralSample =
      (PathModel.mk ((sources covered (preparations index) chain).cells channel)).integralSample :=
    congrArg (fun cells => (PathModel.mk cells).integralSample)
      cells_eq
  have originalBound := integral_difference_le covered (preparations index) source.prepared chain channel
  calc
    _ = Norm.Basic.normSq
        ((PathModel.mk ((sources covered (preparations index) chain).cells channel)).integralSample -
          (PathModel.mk ((sources covered source.prepared chain).cells channel)).integralSample) :=
      congrArg (fun sample => Norm.Basic.normSq
        (sample - (PathModel.mk ((sources covered source.prepared chain).cells channel)).integralSample)) exactSample
    _ ≤ 16 * (originalTargets.localBound + source.targets.localBound) *
        ((parent :: parents).length : Rational) * displacementCost (parent :: parents) := originalBound
    _ = (16 * (originalTargets.localBound + source.targets.localBound)) *
        (((parent :: parents).length : Rational) * displacementCost (parent :: parents)) := by ring1
    _ ≤ (16 * (2 * source.targets.localBound)) *
        (((parent :: parents).length : Rational) * displacementCost (parent :: parents)) := scaled
    _ = errorScale (parent :: parents) * source.targets.localBound := by unfold errorScale; ring1
    _ ≤ errorScale (parent :: parents) * accuracy.tolerance :=
      Order.Arithmetic.mul_le_mul_of_nonneg_left_direct source.localBound_lt.le
        (errorScale_nonnegative (parent :: parents))

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.StageAttempt.Requested

end
