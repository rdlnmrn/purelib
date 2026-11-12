module

import Purelib.System.IO.Reference

public import Purelib.Polynomial.Elimination.Separated.Replay.Computation
public import Purelib.System.IO
public import Purelib.System.FilePath
import scripts.checkpoint.RootRefinement
import scripts.checkpoint.RawSubdivision
import Purelib.Polynomial.Clearance.Box.Line.Elimination.Band
import Purelib.Polynomial.Elimination.Axis.Band
import Purelib.Data.Vector.Basic
import TestPurelib.Polynomial.Elimination.Axis.Prepared
import Purelib.Polynomial.Elimination.Axis.Preparation
import Init.Data.List.Basic
import Init.System.IO

public section

namespace TestPurelib.Polynomial.Elimination.Separated.Computation

open Purelib
open Purelib.Data
open Purelib.Data.Rat
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Polynomial.Elimination.Separated
open Purelib.Polynomial.Clearance.Box.Line.Elimination

/-- Compare every original entry of a retained selected column with the unchanged general producer. -/
def checkColumn {p positive parameter} (column : Replay.Column p positive parameter) : IO Unit := do
  let original := Replay.propose p positive parameter
  unless ∀ row, column.values row = original row do
    throw (IO.userError "checked dispatcher changed an original normalized column entry")

/-- Exercise checked quadratic/cubic selection and preserve complete failed attempts before general fallback. -/
def selfTest (directory : System.FilePath) : IO Unit := do
  if ← directory.pathExists then throw (IO.userError "dispatcher regression needs a fresh store")
  IO.FS.createDirAll directory
  TestPurelib.Polynomial.Elimination.Axis.Prepared.checkReplay
  let writes ← System.IO.mkRef (0 : Nat)
  let saved : IO Unit := System.IO.Ref.modify writes (fun count => count + 1)
  let unexpectedSave : IO Unit := throw (IO.userError "saved-only column replay invoked its after-save hook")
  let quadratic : CoefficientPolynomial := ⟨[1, 0, -4]⟩
  have quadraticPositive : 0 < quadratic.natDegree := by decide +kernel
  match Replay.Computation.compute quadratic quadraticPositive 3 with
  | .quadratic _ column _ => checkColumn column
  | _ => throw (IO.userError "actual real quadratic did not select its checked direct column")
  let cubic : CoefficientPolynomial := ⟨[1, 0, 0, -1]⟩
  have cubicPositive : 0 < cubic.natDegree := by decide +kernel
  match Replay.Computation.compute cubic cubicPositive 2 with
  | .cubic (.unavailable _ _ _) column _ => checkColumn column
  | _ => throw (IO.userError "binomial cubic lost its prior quadratic attempt or selected column")

  let general : CoefficientPolynomial := ⟨[1, -3, -2, 6]⟩
  have generalPositive : 0 < general.natDegree := by decide +kernel
  match Replay.Computation.compute general generalPositive 2 true with
  | .cubic (.unavailable _ _ _) column _ => checkColumn column
  | _ => throw (IO.userError "general cubic lost its original checked column or preceding attempt")
  match Replay.Computation.compute general generalPositive 0 true with
  | .fallback (.unavailable _ _ _) (.unavailable coefficients _ _) =>
      unless coefficients = general.normalize.coeffs do
        throw (IO.userError "nonconstant cubic common factor lost its actual coefficient table")
  | _ => throw (IO.userError "nonconstant cubic common factor lost its inconclusive fallback")
  let linear : CoefficientPolynomial := ⟨[1, -1]⟩
  have linearPositive : 0 < linear.natDegree := by decide +kernel
  match Replay.Computation.compute linear linearPositive 2 with
  | .fallback (.unavailable _ _ _) (.unavailable _ _ _) => pure ()
  | _ => throw (IO.userError "general fallback lost either unavailable original coefficient shape")
  match Replay.Computation.compute quadratic quadraticPositive 0 with
  | .fallback (.rejected _ _ _ (.equation actual _ _)) (.unavailable _ _ _) =>
      unless actual ⟨1, by decide +kernel⟩ = 0 do
        throw (IO.userError "singular quadratic fallback lost its actual computed row")
  | _ => throw (IO.userError "singular quadratic did not retain its failed direct attempt")
  let singular : CoefficientPolynomial := ⟨[1, 0, 0, 0]⟩
  have singularPositive : 0 < singular.natDegree := by decide +kernel
  match Replay.Computation.compute singular singularPositive 0 with
  | .fallback (.unavailable _ _ _) (.rejected _ _ (.equation actual _ _)) =>
      unless actual ⟨0, by decide +kernel⟩ = 0 do
        throw (IO.userError "singular cubic fallback lost its actual computed row")
  | _ => throw (IO.userError "singular cubic did not retain its failed direct attempt")
  let quadraticDirectory := Purelib.System.FilePath.join directory "quadratic-accepted"
  let quadraticColumn ← ClearanceCheckpoint.load { afterSave := saved }
    quadraticDirectory quadratic quadraticPositive 3
  checkColumn quadraticColumn
  let quadraticCold ← ClearanceCheckpoint.load { savedOnly := true, afterSave := unexpectedSave }
    quadraticDirectory quadratic quadraticPositive 3
  unless ∀ row, quadraticCold.values row = quadraticColumn.values row do
    throw (IO.userError "cold quadratic column changed its original entries")
  let cubicDirectory := Purelib.System.FilePath.join directory "cubic-accepted"
  let accepted ← ClearanceCheckpoint.load { afterSave := saved } cubicDirectory cubic cubicPositive 2
  checkColumn accepted
  let cold ← ClearanceCheckpoint.load { savedOnly := true, afterSave := unexpectedSave }
    cubicDirectory cubic cubicPositive 2
  unless ∀ row, cold.values row = accepted.values row do
    throw (IO.userError "cold dispatcher column changed its original retained entries")
  let generalDirectory := Purelib.System.FilePath.join directory "general-cubic-accepted"
  let generalColumn ← ClearanceCheckpoint.load { generalCubic := true, afterSave := saved }
    generalDirectory general generalPositive 2
  checkColumn generalColumn
  let generalCold ← ClearanceCheckpoint.load
    { savedOnly := true, generalCubic := true, afterSave := unexpectedSave }
    generalDirectory general generalPositive 2
  unless ∀ row, generalCold.values row = generalColumn.values row do
    throw (IO.userError "general cubic cold replay changed its original retained entries")
  let rejectedDirectory := Purelib.System.FilePath.join directory "cubic-rejected"
  let stopped ← try
    let _ ← ClearanceCheckpoint.load {} rejectedDirectory singular singularPositive 0
    pure false
  catch _ => pure true
  unless stopped do throw (IO.userError "singular original cubic fallback unexpectedly succeeded")
  unless (← (Purelib.System.FilePath.join rejectedDirectory "rejected-cubic.json").pathExists) &&
      (← (Purelib.System.FilePath.join rejectedDirectory "invalid-generated.json").pathExists) do
    throw (IO.userError "cubic proposal or exact original fallback failure was not retained")
  unless (← System.IO.Ref.get writes) == 3 do
    throw (IO.userError "direct column producers did not run exactly one save hook each")
  let preparedSource : CoefficientPolynomial := ⟨[1, 0, 0, -2]⟩
  have preparedNonzero : preparedSource.isZero = false := by decide +kernel
  have preparedPositive : 0 < preparedSource.natDegree := by decide +kernel
  let axes := Purelib.Polynomial.Elimination.Axis.Preparation.prepare preparedSource preparedNonzero
  if safe : axes.vertical.eliminant.eval 0 ≠ 0 then
    let preparedDirectory := Purelib.System.FilePath.join directory "prepared-accepted"
    let preparedColumn ← ClearanceCheckpoint.loadFromPrepared { afterSave := saved }
      preparedDirectory preparedSource preparedPositive 0 axes.vertical safe
    let preparedCold ← ClearanceCheckpoint.loadFromPrepared
      { savedOnly := true, afterSave := unexpectedSave }
      preparedDirectory preparedSource preparedPositive 0 axes.vertical safe
    unless ∀ row, preparedCold.values row = preparedColumn.values row do
      throw (IO.userError "prepared cold replay changed its complete original unit column")
    let raw := ClearanceCheckpoint.encode preparedColumn
    let invalid := { raw with
      values := List.replicate (preparedSource.natDegree + preparedSource.natDegree)
        (IntegrationCheckpoint.gaussianData 0) }
    match ClearanceCheckpoint.decode preparedSource preparedPositive 0 invalid with
    | .ok _ => throw (IO.userError "prepared saved-column checker accepted an invalid zero vector")
    | .error _ => pure ()
    let absentDirectory := Purelib.System.FilePath.join directory "prepared-missing"
    let missing ← try
      let _ ← ClearanceCheckpoint.loadFromPrepared
        { savedOnly := true, afterSave := unexpectedSave }
        absentDirectory preparedSource preparedPositive 0 axes.vertical safe
      pure false
    catch _ => pure true
    unless missing && !(← (Purelib.System.FilePath.join absentDirectory "column.json").pathExists) do
      throw (IO.userError "saved-only prepared loading generated an absent column")
    let interruptedDirectory := Purelib.System.FilePath.join directory "prepared-after-save"
    let interrupted ← try
      let _ ← ClearanceCheckpoint.loadFromPrepared
        { afterSave := saved *> throw (IO.userError "prepared column after-save interruption") }
        interruptedDirectory preparedSource preparedPositive 0 axes.vertical safe
      pure false
    catch _ => pure true
    unless interrupted do throw (IO.userError "prepared after-save interruption did not propagate")
    let restored ← ClearanceCheckpoint.loadFromPrepared
      { savedOnly := true, afterSave := unexpectedSave }
      interruptedDirectory preparedSource preparedPositive 0 axes.vertical safe
    unless ∀ row, restored.values row = preparedColumn.values row do
      throw (IO.userError "prepared after-save replay changed the already committed column")
  else throw (IO.userError "original cubic prepared inverse lost its zero-coordinate unit column")
  unless (← System.IO.Ref.get writes) == 5 do
    throw (IO.userError "prepared saves, reuse or interruption changed the exact callback count")
  let current : Geometry.Rational.Box := ⟨-1, 1, -1, 1, by decide +kernel, by decide +kernel⟩
  let ambient : Geometry.Rational.Box := ⟨-2, 2, -2, 2, by decide +kernel, by decide +kernel⟩
  let center : Gaussian.Basic.Canonical := 0
  let radius : Fraction.Rational := 1 / 8
  have radiusPositive : 0 < radius := by decide +kernel
  let elimination := axes.certificate preparedNonzero preparedPositive
  let band := Purelib.Polynomial.Elimination.Axis.Band.selectedBand elimination center radius radiusPositive
  let bandDirectory := Purelib.System.FilePath.join directory "prepared-band"
  let lines ← RawSubdivisionCheckpoint.bandLinesPrepared preparedSource axes preparedNonzero preparedPositive
    { afterSave := saved } bandDirectory current ambient center radiusPositive band rfl
  let cold ← RawSubdivisionCheckpoint.bandLinesPrepared preparedSource axes preparedNonzero preparedPositive
    { savedOnly := true, afterSave := unexpectedSave } bandDirectory current ambient center radiusPositive band rfl
  let expected := fun box : Geometry.Rational.Box =>
    [(Band.selectedBandLeftClearance elimination box center radiusPositive).bound,
     (Band.selectedBandRightClearance elimination box center radiusPositive).bound,
     (Band.selectedBandBottomClearance elimination box center radiusPositive).bound,
     (Band.selectedBandTopClearance elimination box center radiusPositive).bound]
  let actual := [lines.left.1.val.bound, lines.right.1.val.bound, lines.bottom.1.val.bound, lines.top.1.val.bound,
    lines.left.2.val.bound, lines.right.2.val.bound, lines.bottom.2.val.bound, lines.top.2.val.bound]
  let restored := [cold.left.1.val.bound, cold.right.1.val.bound, cold.bottom.1.val.bound, cold.top.1.val.bound,
    cold.left.2.val.bound, cold.right.2.val.bound, cold.bottom.2.val.bound, cold.top.2.val.bound]
  unless actual = expected current ++ expected ambient ∧ restored = actual do
    throw (IO.userError "prepared paired columns changed an original current or ambient line bound")
  unless (← System.IO.Ref.get writes) == 9 do
    throw (IO.userError "the eight prepared band lines did not share exactly four column saves")
  System.IO.println "prepared band: eight original line bounds, four shared columns and cold replay passed"
  System.IO.println "checked quadratic/cubic selection, original entries, cold reuse and generic failures passed"
  System.IO.println "prepared columns: shared format, zero-coordinate unit equation, \
    saved-only miss and after-save replay passed"

end TestPurelib.Polynomial.Elimination.Separated.Computation

end
