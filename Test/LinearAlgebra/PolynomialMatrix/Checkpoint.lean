module

import Purelib.Data.List.Control

import Purelib.System.FilePath

import Purelib.System.IO

import Purelib.Data.Json.Codec
import Purelib.Data.Json.Printer
import Purelib.Data.String.Basic
import Purelib.LinearAlgebra.Matrix.Basic
import Purelib.LinearAlgebra.PolynomialMatrix.Basic
import Purelib.LinearAlgebra.PolynomialMatrix.Inverse.Scaled.Compute

public import scripts.checkpoint.InitialExtraction
import Init.Prelude
import Init.System.FilePath
import Init.System.IO
import Init.System.IOError
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Purelib.CCL.Progressive.IntegrationQueries
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.LinearAlgebra.PolynomialMatrix.Inverse.Scaled.Basic
import Purelib.LinearAlgebra.PolynomialMatrix.Inverse.Scaled.Replay
import Purelib.Polynomial.Dense.Basic
import scripts.checkpoint.Integration

-- Use complete constructor eliminators for the original match arms.
set_option backward.match.sparseCases false

open Purelib

open Purelib.LinearAlgebra

open Purelib.LinearAlgebra.PolynomialMatrix.Inverse.Scaled

open Purelib.Data (Json)
open scoped Purelib.Data.String Purelib.Data.List
open Purelib.Data.Json (toJson)

public section

/-! Interrupted execution and exact cold replay of a nonconstant polynomial
matrix. This exercises the same stage loader as the genus-two branch harness.
The checks validate local arithmetic again; they do not claim a cached proof
of that arithmetic or a completed genus-two observation. -/

namespace PolynomialInverseCheckpointHarness

open PolynomialInverseCheckpoint IntegrationCheckpoint
open Purelib.LinearAlgebra.PolynomialMatrix

/-- The nonconstant three-by-three Gaussian polynomial matrix used by the replay regression. -/
@[expose] def fixture : PolynomialMatrix.Basic.Matrix Gaussian 3 :=
  LinearAlgebra.Matrix.matrixOfFn fun row column =>
  if row = column then ⟨[1, (row.val + 1 : Nat)]⟩ else ⟨[1]⟩

/-- Run one calibration, interrupted generation, resume or cold-replay phase.

Check equality with the original inverse data and the exact counts of generated and reused stages. -/
@[expose] def child (directory : System.FilePath) (mode : String) : IO Unit := do
  let action : Execution Unit := do
    IO.FS.createDirAll directory
    if mode == "calibrate" then
      saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk ("canonical.json")))) (inverseData
        (Compute.scaledInverseData 3 fixture))
      return
    let control ← Control.create (mode == "replay") (if mode == "crash" then some 1 else none)
    let restored ← run control ((Purelib.System.FilePath.join directory (System.FilePath.mk ("stages")))) 3 fixture
    let canonical : RawInverse ← loadJson ((Purelib.System.FilePath.join directory (System.FilePath.mk
      ("canonical.json"))))
    unless toJson (inverseData restored.val) == toJson canonical do
      throw (IO.userError "restored polynomial inverse differs from original computation")
    let counts ← Execution.counts
    if mode == "resume" then
      unless counts.generated == 5 && counts.reused == 1 do
        throw (IO.userError "restart did not reuse the completed complement")
    if mode == "replay" then
      unless counts.generated == 0 && counts.reused == 6 do
        throw (IO.userError "cold replay invoked a completed stage producer")
    saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk (s!"counts-{mode}.json")))) counts
    Purelib.System.IO.println (toJson counts).compress
  let (result, _) ← Execution.run action {}
  (@IO.ofExcept IO.Error _ ⟨Purelib.System.IO.Error.toString⟩) result

/-- Invoke one checkpoint phase through the current executable and retained diagnostic deadline.

Every child uses the same compiled harness, original phase and directory. The
process retains its standard output, diagnostic stream and exit status. -/
@[expose] def invoke (directory : System.FilePath) (mode : String) : IO IO.Process.Output := do
  let executable := (← IO.appPath).toString
  Purelib.System.IO.Process.output { cmd := "/usr/bin/timeout", args := #["--signal=KILL", "30s",
    executable, mode, directory.toString] }

/-- Save a child process result and require its successful exit. -/
@[expose] def successful (directory : System.FilePath) (mode : String) : IO IO.Process.Output := do
  let output ← invoke directory mode
  saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk (s!"child-{mode}.json"))))
    (output.exitCode.toNat, output.stdout, output.stderr)
  unless output.exitCode == 0 do throw (IO.userError s!"{mode} failed: {output.stderr}")
  return output

/-- Check interruption recovery, exact replay and rejection of corrupted inverse data.

The fresh-directory protocol verifies reused complements, forbids completed generators during cold replay and retains
invalid scalar and matrix requests. -/
@[expose] def selfTest (directory : System.FilePath) : IO Unit := do
  if ← directory.pathExists then throw (IO.userError "self-test requires a fresh directory")
  IO.FS.createDirAll directory
  discard <| successful directory "calibrate"
  let crashed ← invoke directory "crash"
  saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk ("child-crash.json")))) (crashed.exitCode.toNat,
    crashed.stdout, crashed.stderr)
  unless crashed.exitCode == 137 do throw (IO.userError s!"expected SIGKILL, got {crashed.exitCode}")
  discard <| successful directory "resume"
  for _ in [0, 1] do
    let replay ← successful directory "replay"
    unless ((Purelib.Data.String.splitOn replay.stderr "GENERATOR_FORCED")).length == 1 do
      throw (IO.userError "cold replay forced a stage generator")
  let parentPath := (Purelib.System.FilePath.join (Purelib.System.FilePath.join directory (System.FilePath.mk
    ("stages"))) (System.FilePath.mk ("inverse-v1.json")))
  let saved : RawInverse ← loadJson parentPath
  saveJson parentPath { saved with scalar := [gaussianData 0] }
  let badScalar ← invoke directory "replay"
  unless badScalar.exitCode == 1 && (← ((Purelib.System.FilePath.join (Purelib.System.FilePath.join directory
    (System.FilePath.mk ("stages"))) (System.FilePath.mk ("invalid-inverse.json")))).pathExists) do
    throw (IO.userError "corrupt scalar was not rejected by its equation check")
  saveJson parentPath saved
  let requestPath := (Purelib.System.FilePath.join (Purelib.System.FilePath.join directory (System.FilePath.mk
    ("stages"))) (System.FilePath.mk ("matrix-v1.json")))
  let request : RawMatrix ← loadJson requestPath
  saveJson requestPath (matrixData (LinearAlgebra.Matrix.matrixOfFn fun _ _ : Fin 3 => (0 :
    PolynomialMatrix.Basic.Polynomial Gaussian)))
  let badRequest ← invoke directory "replay"
  unless badRequest.exitCode == 1 && (← ((Purelib.System.FilePath.join (Purelib.System.FilePath.join directory
    (System.FilePath.mk ("stages"))) (System.FilePath.mk ("invalid-request.json")))).pathExists) do
    throw (IO.userError "changed original matrix was not rejected")
  saveJson requestPath request
  discard <| successful directory "replay"
  Purelib.System.IO.println
    "Polynomial inverse: SIGKILL recovery, exact canonical result, two generator-free cold replays, corrupt scalar and \
      changed request rejection passed."

end PolynomialInverseCheckpointHarness

/-- Dispatch the requested polynomial-inverse checkpoint regression phase. -/
@[expose] def main (arguments : List String) : IO Unit := do
  match arguments with
  | ["self-test", directory] => PolynomialInverseCheckpointHarness.selfTest directory
  | [mode, directory] => PolynomialInverseCheckpointHarness.child directory mode
  | _ => throw (IO.userError
    "usage: PolynomialInverseCheckpointHarness.lean self-test|calibrate|crash|resume|replay DIRECTORY")
