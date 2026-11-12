module

public import Purelib.System.IO
public import Purelib.System.FilePath
public import Purelib.Polynomial.Dense.Rational.Basic
public import Purelib.Data.Rat.Fraction.Cast
import scripts.checkpoint.RootRefinement
import Purelib.Data.String.Basic

public section

namespace TestPurelib.RootIsolation.Checkpoint.Winding

open Purelib
open Purelib.Polynomial
open Purelib.Data.Rat
open Purelib.Data (Json)
open IntegrationCheckpoint
open Purelib.System.FilePath (join)
open scoped Purelib.Data.String

/-- The original small dividend used by the mixed winding-checkpoint regression. -/
@[expose] def dividend : Dense.Rational.Basic.CoordinatePolynomial :=
  ⟨[Fraction.Cast.fromInt 1, Fraction.Cast.fromInt 2, Fraction.Cast.fromInt 0, Fraction.Cast.fromInt 1]⟩

/-- The original small divisor whose signed-remainder chain has three divisions. -/
@[expose] def divisor : Dense.Rational.Basic.CoordinatePolynomial :=
  ⟨[Fraction.Cast.fromInt 2, Fraction.Cast.fromInt 1, Fraction.Cast.fromInt 1]⟩

/-- Count an exact diagnostic marker in one completed child output. -/
def markers (output : IO.Process.Output) (marker : String) : Nat :=
  (Data.String.splitOn (output.stdout ++ output.stderr) marker).length - 1

/-- Execute one original legacy-prefix, compact-tail or saved-only winding phase. -/
def child (directory : System.FilePath) (mode : String)
    (inputDigest : Option (String → IO String) := none) : IO Unit := do
  IO.FS.createDirAll directory
  if mode == "legacy" then
    let _ ← WindingCheckpoint.loadStep (m := IO) {} directory 0 dividend divisor (by decide +kernel)
    System.IO.println "winding-checkpoint: original legacy first division saved"
    return
  let afterSave : IO Unit :=
    if mode == "crash" then do
      System.IO.println "winding-checkpoint: interrupting after complete compact witness"
      let pid ← IO.Process.getPID
      let status ← System.IO.Process.output { cmd := "/bin/kill", args := #["-KILL", toString pid] }
      throw (IO.userError s!"interruption unexpectedly returned {status.exitCode}")
    else pure ()
  let control : WindingCheckpoint.Control IO :=
    { savedOnly := mode == "saved", afterSave := afterSave, inputDigest := inputDigest }
  let restored ← WindingCheckpoint.chain control directory divisor.degreeCount 0 dividend divisor le_rfl
  unless restored.val = Dense.Rational.SignedRemainder.Basic.Sturm.signedRemainderChain dividend divisor do
    throw (IO.userError "restored chain changed the complete original signed-remainder chain")
  saveJson (join directory s!"result-{mode}.json") (restored.val.map WindingCheckpoint.polynomialData)
  System.IO.println "winding-checkpoint: complete original chain checked"

/-- Run a completed child phase under the same immutable tested executable. -/
def runChild (directory : System.FilePath) (mode : String) : IO IO.Process.Output := do
  System.IO.Process.output { cmd := (← IO.appPath).toString, args := #["winding-child", directory.toString, mode] }

/-- Copy a completed store for an isolated exact-invalidity regression. -/
def copyStore (source target : System.FilePath) : IO Unit := do
  let result ← System.IO.Process.output { cmd := "/bin/cp", args := #["-a", source.toString, target.toString] }
  unless result.exitCode == 0 do throw (IO.userError s!"checkpoint test copy failed: {result.stderr}")

/-- Require a malformed retained store to fail without invoking a winding generator. -/
def rejected (directory : System.FilePath) (report : String) : IO Unit := do
  let output ← runChild directory "saved"
  saveJson (join directory "rejected-child.json") (output.exitCode.toNat, output.stdout, output.stderr)
  unless output.exitCode != 0 && markers output "WINDING_DIVISION_GENERATOR_FORCED" == 0 &&
      (← (join directory report).pathExists) do
    throw (IO.userError s!"invalid existing winding artifact was accepted or regenerated: \
      {output.stdout}{output.stderr}")

/-- Check mixed-format interrupted recovery, original readback and precise artifact rejection.

One completed legacy division precedes the interrupted compact tail. A fresh
saved-only process reuses both forms, retains its exact next missing request,
and later completes a generator-free replay. Separate stores reject a wrong
manifest request, reference, index, division identity and legacy scalar; an
invalid compact artifact is also rejected when a valid legacy copy exists.
-/
def selfTest (directory : System.FilePath) : IO Unit := do
  if ← directory.pathExists then throw (IO.userError "winding self-test needs a fresh directory")
  IO.FS.createDirAll directory
  let good := join directory "data"
  let legacy ← runChild good "legacy"
  saveJson (join directory "legacy-child.json") (legacy.exitCode.toNat, legacy.stdout, legacy.stderr)
  unless legacy.exitCode == 0 && markers legacy "WINDING_DIVISION_GENERATOR_FORCED" == 1 do
    throw (IO.userError "original legacy fixture did not save exactly one division")
  let crash ← runChild good "crash"
  saveJson (join directory "crash-child.json") (crash.exitCode.toNat, crash.stdout, crash.stderr)
  unless crash.exitCode != 0 && markers crash "WINDING_DIVISION_GENERATOR_FORCED" == 1 &&
      (← (join good "input.json").pathExists) && (← (join good "witness-1.json").pathExists) do
    throw (IO.userError "compact interruption did not retain its completed input and witness")
  let incomplete ← runChild good "saved"
  saveJson (join directory "incomplete-child.json") (incomplete.exitCode.toNat, incomplete.stdout, incomplete.stderr)
  unless incomplete.exitCode != 0 && markers incomplete "WINDING_DIVISION_GENERATOR_FORCED" == 0 &&
      markers incomplete "REUSED winding division 0" == 1 &&
      markers incomplete "REUSED compact winding division 1" == 1 &&
      (← (join good "missing.json").pathExists) do
    throw (IO.userError "saved-only incomplete tail did not reuse both forms and retain its exact next request")
  let resumed ← runChild good "resume"
  saveJson (join directory "resumed-child.json") (resumed.exitCode.toNat, resumed.stdout, resumed.stderr)
  unless resumed.exitCode == 0 && markers resumed "WINDING_DIVISION_GENERATOR_FORCED" == 1 do
    throw (IO.userError "mixed winding tail resume did not complete only its missing original division")
  let cold ← runChild good "saved"
  saveJson (join directory "cold-child.json") (cold.exitCode.toNat, cold.stdout, cold.stderr)
  unless cold.exitCode == 0 && markers cold "WINDING_DIVISION_GENERATOR_FORCED" == 0 &&
      markers cold "REUSED winding division 0" == 1 && markers cold "REUSED compact winding division" == 2 do
    throw (IO.userError "complete mixed winding cold replay regenerated or lost original chain readback")
  let actualHash ← System.IO.Process.output { cmd := "sha256sum", args := #[(join good "input.json").toString] }
  let stored : WindingCheckpoint.RawWitness ← loadJson (join good "witness-1.json")
  unless actualHash.exitCode == 0 &&
      (Data.String.splitOn actualHash.stdout " ").head! == stored.inputSha256 do
    throw (IO.userError "compact reference did not fingerprint the actual retained input bytes")
  let wrongInput := join directory "wrong-input"
  copyStore good wrongInput
  let input : WindingCheckpoint.RawInput ← loadJson (join wrongInput "input.json")
  saveJson (join wrongInput "input.json") { input with fuel := input.fuel + 1 }
  rejected wrongInput "invalid-input.json"
  let wrongReference := join directory "wrong-reference"
  copyStore good wrongReference
  let witness : WindingCheckpoint.RawWitness ← loadJson (join wrongReference "witness-1.json")
  saveJson (join wrongReference "witness-1.json") { witness with inputSha256 := "wrong-reference" }
  rejected wrongReference "invalid-witness.json"
  let wrongIndex := join directory "wrong-index"
  copyStore good wrongIndex
  saveJson (join wrongIndex "witness-1.json") { witness with index := witness.index + 1 }
  rejected wrongIndex "invalid-witness.json"
  let wrongDivision := join directory "wrong-division"
  copyStore good wrongDivision
  let last : WindingCheckpoint.RawWitness ← loadJson (join wrongDivision "witness-2.json")
  saveJson (join wrongDivision "witness-2.json") { last with quotient := [] }
  rejected wrongDivision "invalid-witness.json"
  let wrongLegacy := join directory "wrong-legacy"
  copyStore good wrongLegacy
  let first : WindingCheckpoint.RawStep ← loadJson (join wrongLegacy "division-0.json")
  let invalid : FractionData := ⟨"1", "0"⟩
  saveJson (join wrongLegacy "division-0.json") { first with dividend := [invalid] }
  rejected wrongLegacy "invalid.json"
  let both := join directory "both-forms"
  copyStore good both
  saveJson (join both "witness-0.json") witness
  rejected both "invalid-witness.json"
  System.IO.println "winding-checkpoint: mixed interruption/cold readback and six exact invalidities passed"

end TestPurelib.RootIsolation.Checkpoint.Winding
