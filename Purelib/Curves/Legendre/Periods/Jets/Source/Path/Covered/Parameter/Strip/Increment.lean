module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Parameter.Strip
public import Purelib.Data.Gaussian.Norm.Nonzero
import Purelib.Approximation.AccuracyRequest

/-! # Nonzero parameter increments paid by the original common strip allocation

The original cached allocation and one positive accuracy request determine
an explicit nonzero Gaussian increment. Its actual quadrance pays both
original budgets. The same allocation constructs a regular target frame
at that exact increment, without another source or continuation request.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.ParameterRange.StripAllocation

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {count : Nat} {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count parents} {ranges : ParameterRange covered}
    (allocation : StripAllocation ranges) (accuracy : AccuracyRequest)

/-- Compute one positive request retaining both the original strip budget and the requested quadrance tolerance. -/
@[expose] def incrementRequest : AccuracyRequest :=
  accuracy.minimum ⟨allocation.bound, allocation.bound_positive⟩

/-- The computed increment request pays the same retained common strip allocation. -/
theorem incrementRequest_le_bound : (allocation.incrementRequest accuracy).tolerance ≤ allocation.bound :=
  accuracy.minimum_le_right ⟨allocation.bound, allocation.bound_positive⟩

/-- The same computed request pays the independently supplied accuracy tolerance. -/
theorem incrementRequest_le_accuracy : (allocation.incrementRequest accuracy).tolerance ≤ accuracy.tolerance :=
  accuracy.minimum_le_left ⟨allocation.bound, allocation.bound_positive⟩

/-- Construct an exact Gaussian increment from the same retained joint quadrance request. -/
@[expose] def increment : Canonical :=
  Norm.Nonzero.boundedReal (allocation.incrementRequest accuracy).tolerance

/-- The computed increment is nonzero because both original budgets are strictly positive. -/
theorem increment_nonzero : allocation.increment accuracy ≠ 0 :=
  Norm.Nonzero.boundedReal_nonzero (allocation.incrementRequest accuracy).tolerance
    (allocation.incrementRequest accuracy).positive

/-- The actual computed increment pays the original geometric strip and regularity allocation. -/
theorem increment_admitted : Norm.Basic.normSq (allocation.increment accuracy) ≤ allocation.bound :=
  (Norm.Nonzero.boundedReal_normSq_le (allocation.incrementRequest accuracy).tolerance
    (allocation.incrementRequest accuracy).positive).trans (allocation.incrementRequest_le_bound accuracy)

/-- The same actual increment also pays the independent quadrance tolerance. -/
theorem increment_accurate : Norm.Basic.normSq (allocation.increment accuracy) ≤ accuracy.tolerance :=
  (Norm.Nonzero.boundedReal_normSq_le (allocation.incrementRequest accuracy).tolerance
    (allocation.incrementRequest accuracy).positive).trans (allocation.incrementRequest_le_accuracy accuracy)

/-- Construct the original regular target frame at the identical computed nonzero increment.

The same cached allocation pays its original regular bound. This operation
uses the existing target-frame factory once; it does not prepare a source
bank or supply any root, period or derivative comparison.
-/
def incrementFrame : Paths.Frame (parameter + allocation.increment accuracy) :=
  ranges.targetFrame (allocation.increment accuracy)
    ((allocation.increment_admitted accuracy).trans allocation.bound_le_regularBound)

/-- The complete frame is the original factory applied to this same actual increment and allocation payment. -/
theorem incrementFrame_eq : allocation.incrementFrame accuracy =
    ranges.targetFrame (allocation.increment accuracy)
      ((allocation.increment_admitted accuracy).trans allocation.bound_le_regularBound) := by
  rfl

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.ParameterRange.StripAllocation

end
