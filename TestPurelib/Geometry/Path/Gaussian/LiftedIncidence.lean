module

import Purelib.System.IO
import Purelib.Geometry.Path.Gaussian.Lifted.Incidence
import Purelib.Geometry.Path.Gaussian.Lifted.Closed
import Purelib.Data.Fin.Bijection.Basic
import Purelib.Data.Gaussian.Basic

namespace TestPurelib.Geometry.Path.Gaussian.LiftedIncidence

open Purelib.Geometry.Path.Gaussian.Lifted
open Purelib.Geometry.Path.Gaussian.Lifted.Basic

/-- The original coordinate on sheet zero. -/
def zero : LiftedPoint 2 := ⟨0, ⟨0, by decide⟩⟩

/-- The same original coordinate on the other sheet. -/
def otherSheet : LiftedPoint 2 := ⟨0, ⟨1, by decide⟩⟩

/-- The next original coordinate on the first sheet. -/
def one : LiftedPoint 2 := ⟨1, ⟨0, by decide⟩⟩

/-- The second intermediate coordinate in the original closed cycle. -/
def two : LiftedPoint 2 := ⟨2, ⟨0, by decide⟩⟩

/-- The original cell transports the first sheet to itself. -/
def edge01 : LiftedCell zero one := ⟨Purelib.Data.Fin.Bijection.identity 2, rfl⟩

/-- The next original cell retains the same sheet transport. -/
def edge12 : LiftedCell one two := ⟨Purelib.Data.Fin.Bijection.identity 2, rfl⟩

/-- The last original cell closes the original finite cycle. -/
def edge20 : LiftedCell two zero := ⟨Purelib.Data.Fin.Bijection.identity 2, rfl⟩

/-- The original directed open cell path. -/
def openPath : LiftedPath 2 zero one := .cons edge01 (.nil one)

/-- The original finite directed triangular cycle, retaining all three cell occurrences. -/
def cycle : Closed.ClosedLiftedPath 2 := ⟨zero, .cons edge01 (.cons edge12 (.cons edge20 (.nil zero)))⟩

/-- Identical coordinates do not identify distinct original sheet labels. -/
theorem sheetMismatch : Incidence.vertices (LiftedPath.nil zero) ≠
    Incidence.vertices (LiftedPath.nil otherSheet) := by decide

/-- Reversal retains its actual swapped endpoints and fails the original oriented incidence comparison. -/
theorem orientationMismatch : Incidence.vertices openPath ≠ Incidence.vertices openPath.reverse := by decide

/-- Reversal of a closed cycle retains its basepoint while changing the original cell order. -/
theorem cycleOrientationMismatch : Incidence.vertices cycle.path ≠ Incidence.vertices cycle.path.reverse := by decide

/-- A different finite closed representative requires actual cycle-comparison evidence. -/
theorem cycleMismatch : Incidence.vertices cycle.path ≠ Incidence.vertices (LiftedPath.nil zero) := by decide

/-- Check the actual failed procedure's two retained ordered readings and its violated incidence condition. -/
private def checkRejected {sheets : Nat} {leftStart leftFinish rightStart rightFinish : LiftedPoint sheets}
    (label : String) (left : LiftedPath sheets leftStart leftFinish)
    (right : LiftedPath sheets rightStart rightFinish) : IO Unit := do
  match Incidence.compare left right with
  | .ok _ => throw (IO.userError s!"{label}: mismatched original incidence was accepted")
  | .error mismatch =>
      unless mismatch.first = Incidence.vertices left ∧ mismatch.second = Incidence.vertices right ∧
          mismatch.first ≠ mismatch.second do
        throw (IO.userError s!"{label}: the typed error discarded an original ordered reading \
          or its violated condition")
  Purelib.System.IO.println s!"Lifted incidence {label}: typed mismatch retains both original ordered readings"

/-- Execute sheet, open orientation, closed orientation and cycle failures on their original lifted paths.

These are finite oriented-incidence diagnostics. Neither a mismatch nor a
successful self comparison asserts equality of transport maps or integrals.
-/
public def check : IO Unit := do
  checkRejected "sheets" (LiftedPath.nil zero) (LiftedPath.nil otherSheet)
  checkRejected "open orientation" openPath openPath.reverse
  checkRejected "closed orientation" cycle.path cycle.path.reverse
  checkRejected "cycles" cycle.path (LiftedPath.nil zero)
  match Incidence.compare cycle.path cycle.path with
  | .error _ => throw (IO.userError "Original cycle incidence rejected its own unchanged ordered readings")
  | .ok _ => pure ()

end TestPurelib.Geometry.Path.Gaussian.LiftedIncidence
