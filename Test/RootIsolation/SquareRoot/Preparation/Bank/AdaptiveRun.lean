module
import Purelib.Data.Rat.Fraction.Arithmetic
public import Purelib.System.IO
import Purelib.Data.String.Basic
public import Purelib.Data.List.ToString
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Polynomial.Power.Gaussian
import Purelib.Riemann.RootContinuation.SquareRootDegree
import Purelib.Data.Gaussian.Components.Basic
import Purelib.Data.Rat.Fraction.Cast
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Polynomial.Clearance.Box.Line.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Winding.Box.Basic
import Purelib.Riemann.Readings.BoundedPreparedBanks
import Purelib.Riemann.Topology.SquareRootContinuationChain

import Purelib.RootIsolation.SquareRoot.Clearance.QuadraticAxisElimination
public import Purelib.RootIsolation.SquareRoot.Preparation.Bank.Adaptive
public import Purelib.Data.Task.Parallel
import Init.Prelude
import Init.System.IO
import Init.System.IOError
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Riemann.Paths.PreparedClearPathModels

set_option backward.match.sparseCases false

open scoped Purelib.Data.String Purelib.Data.List

open Purelib.Data.Gaussian

open Purelib.Data.Rat

open Purelib.Data.Task

open Purelib.Polynomial

open Purelib.Polynomial.Clearance.Box

open Purelib.Polynomial.Dense.Basic
open _root_.Purelib.Polynomial.Dense.Basic renaming CoefficientPolynomial -> Dense

open Purelib.Polynomial.Geometry

open Purelib.Polynomial.Power.Gaussian

open Purelib.Riemann.Readings

open Purelib.Riemann.RootContinuation

open Purelib.Riemann.Topology.SquareRootContinuationChain

open Purelib.RootIsolation.SquareRoot.Clearance

open Purelib.RootIsolation.SquareRoot.Preparation.Bank

public section

/-!
Small executable bank-selection regression, independent of generated period
certificates and global root isolation.  Its nonconstant radicand is
`1 + x/256` on `[0,1]`.  All box checks are exact and construct the same
certified owner consumed by the public selector.  This is a mesh-selection
test, not acceptance evidence for a canonical period observation.
Run runtime probes under an explicit SIGKILL timeout and systemd memory bound.
-/

namespace AdaptivePreparedBanksHarness

open Purelib.RootIsolation.SquareRoot.Preparation.Bank.Adaptive
open _root_.Purelib.Polynomial.Geometry (ClearPath)
open _root_.Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Data.Gaussian.Components.Basic (point)
open Purelib.Data.Gaussian.Norm.Basic (normSq_eq_canonical)

/-- The exact rational slope one over 256. -/
@[expose] def slope : Fraction.Rational := 1 / Fraction.Cast.fromInt 256

/-- The affine Gaussian polynomial with constant term one and slope one over 256. -/
@[expose] def polynomial : GaussianPolynomial := ⟨[⟨slope, 0⟩, 1]⟩

/-- Evaluation of the affine polynomial agrees with its explicit linear expression. -/
theorem polynomial_eval (value : Adaptive.Gaussian) :
    polynomial.eval value = (⟨slope, 0⟩ : Adaptive.Gaussian) * value + 1 := by
  simp only [-eq_self, -iff_self, polynomial, DensePolynomial.eval,
    DensePolynomial.evalCoeffs, List.foldl_cons,
    List.foldl_nil, zero_mul, zero_add]
  rfl

/-- The affine polynomial is nonzero at the initial endpoint zero. -/
theorem initial_nonzero : polynomial.eval (Components.Basic.point 0 0) ≠ 0 := by
  rw [polynomial_eval]
  change (⟨slope, 0⟩ : Adaptive.Gaussian) * 0 + 1 ≠ 0
  rw [mul_zero, zero_add]
  decide

/-- The rational rectangle containing the unit real segment and imaginary interval [-1, 1]. -/
@[expose] def ambient : Adaptive.Box where
  xLower := 0
  xUpper := 1
  yLower := -1
  yUpper := 1
  x_valid := by decide
  y_valid := by decide

/-- A unit squared-norm lower bound along the real line inside the ambient rectangle. -/
@[expose] def clearance : Line.Basic.HorizontalLineClearance polynomial ambient 0 where
  bound := 1
  positive := by decide
  lower := by
    intro x lower _upper
    rw [polynomial_eval, ← normSq_eq_canonical]
    change (1 : Adaptive.Coordinate) ≤ (slope * x - 0 * 0 + 1) ^ 2 + (slope * 0 + 0 * x + 0) ^ 2
    have zeroDifference : slope * x - 0 = slope * x := by
      rewrite [Fraction.Arithmetic.sub_eq_add_neg_direct]
      change slope * x + 0 = slope * x
      exact add_zero _
    simp only [zero_mul, mul_zero, zeroDifference, add_zero, zero_pow (by decide : 2 ≠ 0)]
    have nonnegative : (0 : Adaptive.Coordinate) ≤ slope * x :=
      Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) lower
    have bound : (1 : Adaptive.Coordinate) ≤ slope * x + 1 := by
      simpa only [zero_add] using Fraction.Order.Arithmetic.add_le_add_right_direct nonnegative 1
    simpa only [one_pow] using Fraction.Order.Arithmetic.pow_le_pow_direct (by decide : (0 : Adaptive.Coordinate) ≤ 1)
      bound 2

/-- The certified clear horizontal segment from zero to one. -/
@[expose] def segment : ClearPath.ClearSegment polynomial ambient (Components.Basic.point 0 0) (Components.Basic.point 1
  0) :=
  .horizontal 0 1 0 (by decide) (by decide) (by decide) (by decide) clearance

/-- The one-segment clear path from zero to one. -/
@[expose] def path : ClearPath polynomial ambient (Components.Basic.point 0 0)
  (Components.Basic.point 1 0) :=
  .cons segment (.nil _)

/-- Every point of the retained segment lies within its ambient rectangle. -/
theorem within : path.WithinAmbient := .cons ⟨by decide, by decide⟩ (.nil _)

/-- The rational rectangle around the positive square root of one. -/
@[expose] def rootBox : Adaptive.Box where
  xLower := 7 / 8
  xUpper := 9 / 8
  yLower := -1 / 8
  yUpper := 1 / 8
  x_valid := by decide
  y_valid := by decide

/-- Check strict box shape, boundary determinants and winding before constructing the original square-root owner.

Failure returns no owner; success retains the exact box and the original nonzero parameter. -/
@[expose] def owner? : Option (Adaptive.Owner (polynomial.eval (Components.Basic.point 0 0))) :=
  let parameter := polynomial.eval (Components.Basic.point 0 0)
  if proper : rootBox.xLower < rootBox.xUpper ∧ rootBox.yLower < rootBox.yUpper then
    if left : QuadraticAxisElimination.verticalDeterminant parameter rootBox.xLower ≠ 0 then
      if right : QuadraticAxisElimination.verticalDeterminant parameter rootBox.xUpper ≠ 0 then
        if bottom : QuadraticAxisElimination.horizontalDeterminant parameter rootBox.yLower ≠ 0 then
          if top : QuadraticAxisElimination.horizontalDeterminant parameter rootBox.yUpper ≠ 0 then
            if winding : Winding.Box.Basic.quadrupledBoxWinding
                (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter SquareRootDegree.degreeTwo) rootBox = 4 then
              some (Owner.ofBox
                initial_nonzero rootBox proper left right bottom top winding)
            else none
          else none
        else none
      else none
    else none
  else none

/-- Check bounded inconclusivity, coarser bank selection and ordered parallel bank construction.

Every selected bank retains its original owner, requested diameter, minimum depth and exact dyadic cell count. -/
@[expose] def run : IO Unit := do
  let some owner := owner? | throw (IO.userError "small root box rejected")
  let task := Task.ofPath path within owner
  let positive : (0 : Adaptive.Coordinate) < 1 := by decide
  match BoundedPreparedBanks.attempt 0 1 positive path within owner with
  | .ok _ => throw (IO.userError "coarse regression unexpectedly passed its bounded source checks")
  | .error report =>
      unless report.attemptedDepth = 0 ∧ report.requestedDiameter = 1 do
        throw (IO.userError "inconclusivity report lost its actual mesh budget")
      Purelib.System.IO.println "bounded depth-zero trial: certified inconclusive; actual depth and diameter retained"
  let selected := Adaptive.select [task, task] 1 (by decide)
  unless selected.depth < selected.upperDepth do
    throw (IO.userError "small nonconstant regression did not select a strictly coarser bank")
  let first := selected.banks.head.prepared
  let second := selected.banks.tail.head.prepared
  unless first.stepCount = 2 ^ selected.depth ∧ second.stepCount = first.stepCount do
    throw (IO.userError "paired bank counts disagree with the retained common depth")
  Purelib.System.IO.println
    s!"coarser paired banks: selected={selected.depth}, sufficient={selected.upperDepth}, cells={first.stepCount}; \
      passed"
  let constrained := Adaptive.selectFrom [task] 1 (by decide) 5
  unless 5 ≤ constrained.depth ∧ constrained.depth ≤ constrained.upperDepth ∧
      constrained.banks.head.prepared.stepCount = 2 ^ constrained.depth do
    throw (IO.userError "minimum-depth selection lost its tracing constraint or exact geometry")
  Purelib.System.IO.println
    s!"constrained bank: minimum=5, selected={constrained.depth}, sufficient={constrained.upperDepth}; passed"
  -- Distinct minimum depths make an accidental result permutation observable.
  -- The generic helper's theorem additionally preserves the complete banks.
  let jobs : Adaptive.Selected [task] 1 (by decide) 4 × Adaptive.Selected [task] 1 (by decide) 5 ×
      Adaptive.Selected [task] 1 (by decide) 6 × Adaptive.Selected [task] 1 (by decide) 7 := Parallel.four
    (fun _ => Adaptive.selectFrom [task] 1 (by decide) 4)
    (fun _ => Adaptive.selectFrom [task] 1 (by decide) 5)
    (fun _ => Adaptive.selectFrom [task] 1 (by decide) 6)
    (fun _ => Adaptive.selectFrom [task] 1 (by decide) 7)
  let depths := [jobs.1.depth, jobs.2.1.depth, jobs.2.2.1.depth, jobs.2.2.2.depth]
  let cells := [jobs.1.banks.head.prepared.stepCount, jobs.2.1.banks.head.prepared.stepCount,
    jobs.2.2.1.banks.head.prepared.stepCount, jobs.2.2.2.banks.head.prepared.stepCount]
  unless depths = [4, 5, 6, 7] ∧ cells = [16, 32, 64, 128] do
    throw (IO.userError "parallel bank selection changed ordered depths or meshes")
  Purelib.System.IO.println s!"four independent banks: ordered depths={depths}; cells={cells}; passed"

end AdaptivePreparedBanksHarness

/-- Run the executable adaptive-bank regression. -/
@[expose] def main : IO Unit := AdaptivePreparedBanksHarness.run
