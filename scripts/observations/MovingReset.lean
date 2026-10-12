module
public import Purelib.System.IO
import Purelib.Data.String.Basic
public import Purelib.Data.String.Parsing
public import Purelib.Data.List.Control
public import Purelib.Data.Int.Decimal
import Purelib.Data.Rat.Fraction.Cast
import Purelib.Polynomial.Winding.Box.Basic

import Purelib.RootIsolation.SquareRoot.Clearance.ExactQuadraticOwnerClearance
import Purelib.RootIsolation.SquareRoot.Clearance.QuadraticAxisElimination
import Purelib.RootIsolation.SquareRoot.Clearance.QuadraticLineClearance
public import Purelib.RootIsolation.SquareRoot.Clearance.QuadraticCoefficientClearance
import Init.Prelude
import Init.System.IO
import Init.System.IOError
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.PartialOrder
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Polynomial.Clearance.Box.Grid.Four.Basic

set_option backward.match.sparseCases false

open scoped Purelib.Data.String Purelib.Data.Int.Decimal Purelib.Data.List

open Purelib.Data.Rat

open Purelib.Polynomial

open Purelib.RootIsolation.SquareRoot.Clearance

open Purelib.RootIsolation.SquareRoot.Clearance.QuadraticLineClearance

public section

/-!
Replay one quadratic moving-reset calculation from finite numerical inputs.
CanonicalPeriodPreparationHarness prints these inputs from its actual retained
inconclusivity report.  No branch isolation, continuation prefix, coefficient
bank or numerical observation is needed here.  The existing theorem
`movingRecenter_ownerBox_map` identifies this box-only calculation with the
full owner reset's choices; this diagnostic does not manufacture a replacement
owner or claim global non-certifiability.

Use an explicit SIGKILL timeout and systemd memory bound for runtime probes.
The sole import is the existing finite coefficient-clearance improvement,
which imports the production quadratic-reset implementation.
-/

namespace MovingResetHarness

open Purelib.RootIsolation.SquareRoot.Clearance.ExactQuadraticOwnerClearance
open Purelib.RootIsolation.SquareRoot.Clearance.QuadraticLineClearance.ExactQuadraticOwnerClearance

/-- Print and flush one moving-reset diagnostic message. -/
@[expose] def report (message : String) : IO Unit := do
  Purelib.System.IO.println message
  (← IO.getStdout).flush

/-- Evaluate a thunk through IO without inlining the timing boundary. -/
@[noinline, expose] def evaluate {α : Type} (work : Unit → α) : IO α := pure (work ())

/-- Render an exact rational as its retained numerator and denominator. -/
@[expose] def fractionText (value : ExactQuadraticOwnerClearance.Coordinate) : String := s!"{value.num}/{value.den}"

/-- Render the two exact rational coordinate intervals of a box. -/
@[expose] def boxText (box : ExactQuadraticOwnerClearance.Box) : String :=
  s!"[{fractionText box.xLower},{fractionText box.xUpper}] x [{fractionText box.yLower},{fractionText box.yUpper}]"

/-- Parse a signed numerator and strictly positive denominator as an exact rational. -/
@[expose] def parseCoordinate (label numerator denominator : String) : IO Coordinate := do
  let some numerator := Purelib.Data.String.toInt? numerator
    | throw (IO.userError s!"{label}: invalid numerator {numerator}")
  let some denominator := Purelib.Data.String.toNat? denominator
    | throw (IO.userError s!"{label}: invalid denominator {denominator}")
  unless 0 < denominator do throw (IO.userError s!"{label}: denominator must be positive")
  pure (Fraction.Cast.fromInt numerator / Fraction.Cast.fromInt denominator)

/-- Report the finite moving-reset checks for the original parameter and proper box.

Retain midpoint determinant checks, ordered winding-based child selection and exact clearance comparisons; the result
only reports this finite attempt. -/
@[expose] def explain (parameter : ExactQuadraticOwnerClearance.Gaussian) (nonzero : parameter ≠ 0)
    (box : ExactQuadraticOwnerClearance.Box) (proper : box.Proper) (variation : ExactQuadraticOwnerClearance.Coordinate)
      : IO Bool := do
  report
    s!"parameter=({fractionText parameter.re},{fractionText parameter.im}); source={boxText box}; \
      variation={fractionText variation}"
  let sourceBound ← evaluate fun _ =>
    QuadraticCoefficientClearance.boundaryBound parameter box
  report
    s!"source coefficient clearance={fractionText sourceBound}; carries recorded \
      variation={decide (variation < sourceBound)}"
  let started ← IO.monoMsNow
  let result ← evaluate fun _ => ExactQuadraticOwnerClearance.movingRecenterBox? parameter nonzero box proper
  report s!"production box-only reset: accepted={result.isSome}; elapsed={(← IO.monoMsNow) - started} ms"
  let vertical := QuadraticAxisElimination.verticalDeterminant
    parameter (ExactQuadraticOwnerClearance.midpoint box.xLower box.xUpper)
  let horizontal := QuadraticAxisElimination.horizontalDeterminant
    parameter (ExactQuadraticOwnerClearance.midpoint box.yLower box.yUpper)
  if xNonzero : vertical ≠ 0 then
    if yNonzero : horizontal ≠ 0 then
      let grid := ExactQuadraticOwnerClearance.midpointGrid parameter box proper xNonzero yNonzero
      let children := [("lower-left", grid.lowerLeft), ("upper-left", grid.upperLeft),
        ("lower-right", grid.lowerRight), ("upper-right", grid.upperRight)]
      let mut selected := false
      for (label, child) in children do
        unless selected do
          let winding ← evaluate fun _ => Winding.Box.Basic.quadrupledBoxWinding
            (ExactQuadraticOwnerClearance.rootPolynomial parameter) child
          report s!"{label}: quadrupled winding={winding}"
          if winding = 4 then
            selected := true
            let candidate ← evaluate fun _ => ExactQuadraticOwnerClearance.movingCandidateBox? parameter nonzero box
              proper child
            report s!"selected child={boxText child}; replacement candidate accepted={candidate.isSome}"
      unless selected do report "No midpoint child passed the winding-four check."
    else report "Stopped before child selection: horizontal midpoint determinant is zero."
  else report "Stopped before child selection: vertical midpoint determinant is zero."
  match result with
  | none => report "This finite moving-reset attempt returned no candidate; no global failure is asserted."
  | some moved =>
      let bound ← evaluate fun _ =>
        min (ExactQuadraticOwnerClearance.directVerticalClearanceBound parameter moved moved.xLower)
          (min (ExactQuadraticOwnerClearance.directVerticalClearanceBound parameter moved moved.xUpper)
            (min (ExactQuadraticOwnerClearance.directHorizontalClearanceBound parameter moved moved.yLower)
              (ExactQuadraticOwnerClearance.directHorizontalClearanceBound parameter moved moved.yUpper)))
      report s!"replacement={boxText moved}; diagonalSq={fractionText moved.diagonalSq}"
      report s!"direct clearance={fractionText bound}; carries recorded variation={decide (variation < bound)}"
      let coefficientBound ← evaluate fun _ =>
        QuadraticCoefficientClearance.boundaryBound parameter moved
      report
        s!"replacement coefficient clearance={fractionText coefficientBound}; carries recorded \
          variation={decide (variation < coefficientBound)}"
  pure result.isSome

/-- Check rejection at a midpoint root and acceptance of the offset winding-one fixture. -/
@[expose] def selfTest : IO Unit := do
  let centered : Box := ⟨1 / 2, 3 / 2, -1 / 2, 1 / 2, by decide, by decide⟩
  if ← explain 1 (by decide) centered ⟨by decide, by decide⟩ (1 / 1000) then
    throw (IO.userError "midpoint-through-root fixture unexpectedly accepted")
  let offset : Box := ⟨1 / 2, 7 / 4, -1 / 2, 3 / 4, by decide, by decide⟩
  unless ← explain 1 (by decide) offset ⟨by decide, by decide⟩ (1 / 1000) do
    throw (IO.userError "offset winding-one fixture unexpectedly failed")
  report "Box-only reset diagnostic self-test passed; no canonical bank was constructed."

/-- Parse and check the exact reset request before running the finite diagnostic. -/
@[expose] def run (arguments : List String) : IO Unit := do
  match arguments with
  | ["self-test"] => selfTest
  | ["reset", rn, rd, inum, iden, xln, xld, xun, xud, yln, yld, yun, yud, vn, vd] =>
      let real ← parseCoordinate "real parameter" rn rd
      let imaginary ← parseCoordinate "imaginary parameter" inum iden
      let xLower ← parseCoordinate "x lower" xln xld
      let xUpper ← parseCoordinate "x upper" xun xud
      let yLower ← parseCoordinate "y lower" yln yld
      let yUpper ← parseCoordinate "y upper" yun yud
      let variation ← parseCoordinate "variation" vn vd
      let parameter : Gaussian := ⟨real, imaginary⟩
      if nonzero : parameter ≠ 0 then
        if xProper : xLower < xUpper then
          if yProper : yLower < yUpper then
            let box : Box := ⟨xLower, xUpper, yLower, yUpper, xProper.le, yProper.le⟩
            discard <| explain parameter nonzero box ⟨xProper, yProper⟩ variation
          else throw (IO.userError "source box must have yLower < yUpper")
        else throw (IO.userError "source box must have xLower < xUpper")
      else throw (IO.userError "quadratic parameter must be nonzero")
  | _ => throw (IO.userError
    "usage: moving_reset_harness self-test | reset RE_NUM RE_DEN IM_NUM IM_DEN XLOW_NUM XLOW_DEN XUP_NUM XUP_DEN \
      YLOW_NUM YLOW_DEN YUP_NUM YUP_DEN VAR_NUM VAR_DEN")

end MovingResetHarness

/-- Run the moving-reset command-line diagnostic. -/
@[expose] def main (arguments : List String) : IO Unit := MovingResetHarness.run arguments
