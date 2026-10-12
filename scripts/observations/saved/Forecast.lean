module

import Purelib.System.IO
import Purelib.System.FilePath

meta import Purelib.Elab.ConstructiveInjectivity
meta import Purelib.Elab.Deriving.Json
import Purelib.Data.Json.Codec
import Purelib.Data.String.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore

public import Purelib.Riemann.Transport.PreparedForecastReplay
public import scripts.checkpoint.Integration.Import
import Init.Prelude
import Init.System.FilePath
import Init.System.IO
import Init.System.IOError
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.PartialOrder
import Purelib.CCL.Progressive.IntegrationQueries
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import scripts.checkpoint.Integration

-- Use complete constructor eliminators for the original match arms.
set_option backward.match.sparseCases false

open Purelib

open Purelib.Data.Rat

open Purelib.Geometry

open Purelib.Riemann.Integration

open Purelib.Riemann.Transport

section
open Purelib.Data (Json)
open scoped Purelib.Data.List Purelib.Data.Range Purelib.Data.String

public section

/-! Replay the exponent-zero forecast from actual saved v1 refinement inputs.
No branch, owner, centre or coefficient constructor is called.  Checked terms
and completed sum blocks persist across interruptions.  This is numerical
diagnosis, not a restored canonical state or a period observation receipt.
Use a SIGKILL timeout and a systemd memory bound. -/

namespace SavedForecastHarness

open IntegrationCheckpoint
open Purelib.Riemann.Transport.PreparedForecastReplay (Coordinate fromReading)

set_option genInjectivity false in
/-- The retained parent count, polynomial coefficients and refinement target of a saved forecast request.

The parent count, ordered radicand coefficients and exact target remain
separate retained encodings. Restoration checks their scalar data before using
the original finite forecast request. -/
structure Header where
  /-- The number of ordered original parent records. -/ parentCount : Nat
  /-- The serialized coefficients of the retained radicand polynomial. -/ radicand : List GaussianData
  /-- The exact serialized refinement target. -/ target : FractionData
deriving Json.FromJson, Json.ToJson

constructive_injectivity Header

set_option genInjectivity false in
/-- The serialized original endpoints, root box and reading target of one indexed forecast term.

The selected parent, oriented endpoints, box and reading target retain
separate exact encodings. Restoration checks the same finite forecast request
before using a reconstructed numerical view. -/
structure Parent where
  /-- The original ordinal of this parent record. -/ parent : Nat
  /-- The serialized starting endpoint. -/ start : GaussianData
  /-- The serialized finishing endpoint. -/ finish : GaussianData
  /-- The four serialized root-box coordinates. -/ box : List FractionData
  /-- The serialized coefficient-reading target. -/ readingTarget : FractionData
deriving Json.FromJson, Json.ToJson

constructive_injectivity Parent

set_option genInjectivity false in
/-- Decoded exact numerical inputs to one retained forecast formula. -/
structure Inputs where
  /-- The exact starting endpoint. -/ start : Data.Gaussian.Basic.Canonical
  /-- The exact finishing endpoint. -/ finish : Data.Gaussian.Basic.Canonical
  /-- The retained rational root box. -/ box : Rational.Box
  /-- The exact coefficient-reading target. -/ reading : Fraction.Rational

constructive_injectivity Inputs

/-- Decode the saved forecast inputs and certify strict horizontal and vertical box bounds. -/
@[expose] def decode (data : Parent) : IO Inputs := do
  let start ← checked "start" (decodeGaussian data.start)
  let finish ← checked "finish" (decodeGaussian data.finish)
  let [xl, xu, yl, yu] ← data.box.mapM fun value => checked "root coordinate" (decodeFraction value)
    | throw (IO.userError "root box needs four coordinates")
  let reading ← checked "reading target" (decodeFraction data.readingTarget)
  if xp : xl < xu then
    if yp : yl < yu then
      return ⟨start, finish, ⟨xl, xu, yl, yu, xp.le, yp.le⟩, reading⟩
    else throw (IO.userError "root box is not vertically proper")
  else throw (IO.userError "root box is not horizontally proper")

/-- Check a saved forecast value by the exact diameter and cross-product conditions. -/
@[expose] def checkValue (inputs : Inputs) (value : Fraction.Rational) : IO Coordinate := do
  match PreparedForecastReplay.check inputs.start inputs.finish inputs.box inputs.reading value with
  | .ok checked => return checked.val
  | .error (.diameter value _) => throw (IO.userError s!"nonpositive saved root diameter {fractionText value}")
  | .error (.identity left right _) =>
      throw (IO.userError s!"saved forecast cross-product mismatch: {fractionText left} != {fractionText right}")

/-- Certify equality of a saved sum with its independently calculated exact value. -/
@[expose] def checkSum (value expected : Fraction.Rational) :
    Except InvalidData { result : Fraction.Rational // result = expected } :=
  if same : value = expected then .ok ⟨value, same⟩
  else .error (.rationalMismatch "saved forecast sum" value expected same)

/-- Compute one original forecast term with a diagnostic generation marker. -/
@[noinline, expose] def generate (index : Nat) (inputs : Inputs) : Coordinate :=
  if index < 2 || index % 128 == 0 then
    dbg_trace s!"SAVED_FORECAST_TERM_GENERATED_{index}"
    fromReading inputs.start inputs.finish inputs.box inputs.reading
  else fromReading inputs.start inputs.finish inputs.box inputs.reading

/-- Evaluate a thunk through IO without inlining the timing boundary. -/
@[noinline, expose] def evaluate {α : Type} (work : Unit → α) : IO α := pure (work ())

/-- Load or generate the ordered forecast terms with exact validation and atomic checkpoints.

Saved-only and explicit-import modes reuse checked values; interrupted runs preserve their completed prefix. -/
@[expose] def loadTerms (source directory : System.FilePath) (onlySaved : Bool)
    (crashAfterFirst : Bool := false) (prior : Option System.FilePath := none) : IO (Header × Array Fraction.Rational)
      := do
  IO.FS.createDirAll ((Purelib.System.FilePath.join directory (System.FilePath.mk ("terms"))))
  IO.FS.withFile source .read fun handle => do
    unless (Purelib.Data.String.trimAscii (← handle.getLine)) == "ccl-canonical-refinement-inputs-v1" do
      throw (IO.userError "expected canonical refinement inputs v1")
    let header : Header ← parseJson "header" (← handle.getLine)
    let mut values := #[]
    let mut reused := 0
    for index in [:header.parentCount] do
      let raw : Parent ← parseJson s!"parent {index}" (← handle.getLine)
      unless raw.parent == index do throw (IO.userError "parent order does not match the snapshot")
      let inputs ← decode raw
      let path := (Purelib.System.FilePath.join (Purelib.System.FilePath.join directory (System.FilePath.mk ("terms")))
        (System.FilePath.mk (s!"{index}.json")))
      let readPath := if ← path.pathExists then path
        else (Purelib.System.FilePath.join (Purelib.System.FilePath.join (prior.getD directory) (System.FilePath.mk
          ("terms"))) (System.FilePath.mk (s!"{index}.json")))
      let value ← if ← readPath.pathExists then do
        reused := reused + 1
        let saved : FractionData ← loadJson readPath
        let value ← checkValue inputs (← checked "saved forecast" (decodeFraction saved))
        if readPath != path then saveJson path (fractionData value)
        pure value
      else do
        if onlySaved then throw (IO.userError s!"term {index}: restart would invoke completed generation")
        let value ← evaluate fun _ => generate index inputs
        discard <| checkValue inputs value
        saveJson path (fractionData value)
        pure value
      values := values.push value
      if crashAfterFirst && index == 0 then
        let pid ← IO.Process.getPID
        discard <| Purelib.System.IO.Process.output { cmd := "/bin/kill", args := #["-KILL", toString pid] }
        throw (IO.userError "checkpoint-boundary SIGKILL failed")
      if (index + 1) % 128 == 0 then profile directory s!"terms {index + 1}/{header.parentCount}; reused={reused}"
    unless (← handle.getLine).isEmpty do throw (IO.userError "unexpected extra parent records")
    profile directory s!"terms complete: count={values.size}; reused={reused}; generated={values.size - reused}"
    return (header, values)

/-- Compute the requested sequential or blocked exact sum and mark its generation. -/
@[noinline, expose] def generateSum (mode : String) (index : Nat)
    (initial : Fraction.Rational) (chunk : List Fraction.Rational) : Coordinate :=
  dbg_trace s!"SAVED_FORECAST_SUM_GENERATED_{index}"
  if mode == "blocked" then chunk.foldl (fun suffix value => value + suffix) 0 + initial
  else chunk.foldl (fun suffix value => value + suffix) initial

/-- The production forecast is a right-associated sum. Reverse the terms and add them to the accumulator in that same
order. The alternative blocked mode changes only association. Completed blocks are checked against their terms and
preceding sum, not accepted on provenance alone. -/
@[expose] def sumTerms (directory : System.FilePath) (mode : String) (terms : Array Fraction.Rational)
    (onlySaved : Bool) (prior : Option System.FilePath := none) : IO Coordinate := do
  IO.FS.createDirAll ((Purelib.System.FilePath.join directory (System.FilePath.mk ("sums"))))
  let reversed := terms.toList.reverse
  let mut total : Coordinate := 0
  let mut reused := 0
  for block in [:(terms.size + 127) / 128] do
    let chunk := (reversed.drop (128 * block)).take 128
    let path := (Purelib.System.FilePath.join (Purelib.System.FilePath.join directory (System.FilePath.mk ("sums")))
      (System.FilePath.mk (s!"{mode}-{block}.json")))
    let readPath := if ← path.pathExists then path
      else (Purelib.System.FilePath.join (Purelib.System.FilePath.join (prior.getD directory) (System.FilePath.mk
        ("sums"))) (System.FilePath.mk (s!"{mode}-{block}.json")))
    profile directory s!"BEGIN sum block {block}; total denominator bits={total.den.log2 + 1}"
    if ← readPath.pathExists then
      let saved : FractionData ← loadJson readPath
      let value ← checked "saved sum" (decodeFraction saved)
      let expected ← evaluate fun _ => chunk.foldl (fun suffix value => value + suffix) 0 + total
      discard <| checked "saved sum" (checkSum value expected)
      if readPath != path then saveJson path (fractionData value)
      total := value
      reused := reused + 1
    else
      if onlySaved then throw (IO.userError s!"sum block {block}: restart would invoke completed generation")
      total ← evaluate fun _ => generateSum mode block total chunk
      saveJson path (fractionData total)
    profile directory s!"END sum block {block}; denominator bits={total.den.log2 + 1}; reused={reused}"
  saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk (s!"{mode}-forecast.json")))) (fractionData
    total)
  return total

/-- Restore the exact numerical forecast and compute the production root-size proposal.

Bind the source snapshot and import manifests, preserve checked work and retain the distinction from source-owner
restoration. -/
@[expose] def run (source directory : System.FilePath) (mode : String) (onlySaved : Bool)
    (crashAfterFirst : Bool := false) (prior : Option System.FilePath := none) : IO Unit := do
  unless mode == "right" || mode == "blocked" do throw (IO.userError "sum mode must be right or blocked")
  let hash ← Purelib.System.IO.Process.output { cmd := "sha256sum", args := #[source.toString] }
  unless hash.exitCode == 0 do throw (IO.userError "snapshot fingerprint failed")
  let digest := ((Purelib.Data.String.splitOn hash.stdout " ")).head!
  let identity := s!"exponent-zero saved forecast v1; source sha256={digest}; numerical-only, owner history unresolved"
  let origin ← match prior with
    | none => pure none
    | some previous => do
        let previousResolved ← IO.FS.realPath previous
        if ← directory.pathExists then
          if (← IO.FS.realPath directory) == previousResolved then
            throw (IO.userError "import source and destination must be distinct")
        let manifest : Manifest ← loadJson ((Purelib.System.FilePath.join previous (System.FilePath.mk
          ("manifest.json"))))
        match checkImportIdentity identity manifest with
        | .ok _ => pure ()
        | .error (.format actual _) => throw (IO.userError s!"import format rejected: {actual}")
        | .error (.identity actual expected _) =>
            throw (IO.userError s!"import source identity differs: {actual}; expected {expected}")
        pure (some (previousResolved.toString, manifest))
  openStore directory identity
  if let some origin := origin then
    let path := (Purelib.System.FilePath.join directory (System.FilePath.mk ("forecast-import.json")))
    if ← path.pathExists then
      let retained : String × Manifest ← loadJson path
      unless jsonText retained == jsonText origin do throw (IO.userError
        "destination already records a different import")
    else saveJson path origin
  profile directory "BEGIN checked saved-input forecast; no canonical preparation"
  let (header, terms) ← loadTerms source directory onlySaved crashAfterFirst prior
  let total ← sumTerms directory mode terms onlySaved prior
  let target ← checked "saved refinement target" (decodeFraction header.target)
  profile directory "BEGIN production root-size proposal from replayed forecast"
  let bits ← evaluate fun _ => PreparedDirectDyadicRefinements.proposedRootBits header.parentCount total target
  saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk (s!"{mode}-root-bits.json")))) bits
  profile directory s!"COMPLETE numerical forecast; root bits={bits}; no mesh, owner restoration or observation receipt"

/-- Check forecast formula validation, exact sum association and interrupted-prefix reuse.

The protocol verifies generator-free reload and explicit cross-build import while preserving the original manifest. -/
@[expose] def selfTest (directory : System.FilePath) : IO Unit := do
  if ← directory.pathExists then throw (IO.userError "self-test requires a fresh directory")
  IO.FS.createDirAll directory
  let source := (Purelib.System.FilePath.join directory (System.FilePath.mk ("inputs.jsonl")))
  let header : Header := ⟨2, [], fractionData 1⟩
  let parent := fun index : Nat => (⟨index, gaussianData 0, gaussianData 1,
    [fractionData 1, fractionData 2, fractionData 1, fractionData 2], fractionData 1⟩ : Parent)
  atomicText source ("ccl-canonical-refinement-inputs-v1\n" ++ jsonText header ++ "\n" ++
    jsonText (parent 0) ++ "\n" ++ jsonText (parent 1) ++ "\n")
  let executable := (← IO.appPath).toString
  let invoke := fun (mode saved : String) => Purelib.System.IO.Process.output
    { cmd := "/usr/bin/timeout"
      args := #["--signal=KILL", "30s", executable, source.toString, ((Purelib.System.FilePath.join directory
        (System.FilePath.mk ("store")))).toString, mode, saved] }
  let fresh ← invoke "right" "generate"
  unless fresh.exitCode == 0 && ((Purelib.Data.String.splitOn (fresh.stdout ++ fresh.stderr)
    "SAVED_FORECAST_TERM_GENERATED_")).length > 1 do
    throw (IO.userError ("fresh marker calibration failed\n" ++ fresh.stdout ++ fresh.stderr))
  let resumed ← invoke "right" "saved-only"
  unless resumed.exitCode == 0 && ((Purelib.Data.String.splitOn (resumed.stdout ++ resumed.stderr) "GENERATED_")).length
    == 1 do
    throw (IO.userError ("restart did not reuse completed work\n" ++ resumed.stdout ++ resumed.stderr))
  let blocked ← invoke "blocked" "generate"
  unless blocked.exitCode == 0 do throw (IO.userError (blocked.stdout ++ blocked.stderr))
  let first : FractionData ← loadJson ((Purelib.System.FilePath.join (Purelib.System.FilePath.join directory
    (System.FilePath.mk ("store"))) (System.FilePath.mk ("right-forecast.json"))))
  let second : FractionData ← loadJson ((Purelib.System.FilePath.join (Purelib.System.FilePath.join directory
    (System.FilePath.mk ("store"))) (System.FilePath.mk ("blocked-forecast.json"))))
  unless jsonText first == jsonText second do throw (IO.userError "sum associations disagree")
  let inputs ← decode (parent 0)
  match PreparedForecastReplay.check inputs.start inputs.finish inputs.box inputs.reading 0 with
  | .error (.identity _ _ _) => pure ()
  | _ => throw (IO.userError "altered term was not certified invalid")
  let invokePartial := fun (saved : String) => Purelib.System.IO.Process.output
    { cmd := "/usr/bin/timeout"
      args := #["--signal=KILL", "30s", executable, source.toString,
        ((Purelib.System.FilePath.join directory (System.FilePath.mk ("interrupted")))).toString, "right", saved] }
  let crashed ← invokePartial "crash"
  unless crashed.exitCode == 137 do throw (IO.userError "partial-run fixture did not receive SIGKILL")
  unless ← ((Purelib.System.FilePath.join (Purelib.System.FilePath.join (Purelib.System.FilePath.join directory
    (System.FilePath.mk ("interrupted"))) (System.FilePath.mk ("terms"))) (System.FilePath.mk ("0.json")))).pathExists
    do
    throw (IO.userError "SIGKILL lost the completed atomic term")
  let partialResume ← invokePartial "generate"
  let output := partialResume.stdout ++ partialResume.stderr
  unless partialResume.exitCode == 0 && ((Purelib.Data.String.splitOn output "SAVED_FORECAST_TERM_GENERATED_0")).length
    == 1 &&
      ((Purelib.Data.String.splitOn output "SAVED_FORECAST_TERM_GENERATED_1")).length > 1 do
    throw (IO.userError ("partial restart did not skip the completed term\n" ++ output))
  let original : Manifest ← loadJson ((Purelib.System.FilePath.join (Purelib.System.FilePath.join directory
    (System.FilePath.mk ("store"))) (System.FilePath.mk ("manifest.json"))))
  let old : Manifest := { original with binarySha256 := "simulated-old-forecast-binary" }
  saveJson ((Purelib.System.FilePath.join (Purelib.System.FilePath.join directory (System.FilePath.mk ("store")))
    (System.FilePath.mk ("manifest.json")))) old
  let rejected ← invoke "right" "saved-only"
  unless rejected.exitCode != 0 do throw (IO.userError "ordinary resume silently accepted a changed binary")
  let imported ← Purelib.System.IO.Process.output
    { cmd := "/usr/bin/timeout"
      args := #["--signal=KILL", "30s", executable, "import-saved", source.toString,
        ((Purelib.System.FilePath.join directory (System.FilePath.mk ("store")))).toString,
          ((Purelib.System.FilePath.join directory (System.FilePath.mk ("imported")))).toString, "right"] }
  unless imported.exitCode == 0 && ((Purelib.Data.String.splitOn (imported.stdout ++ imported.stderr)
    "GENERATED_")).length == 1 do
    throw (IO.userError ("checked cross-build import failed\n" ++ imported.stdout ++ imported.stderr))
  let preserved : Manifest ← loadJson ((Purelib.System.FilePath.join (Purelib.System.FilePath.join directory
    (System.FilePath.mk ("store"))) (System.FilePath.mk ("manifest.json"))))
  unless jsonText preserved == jsonText old do throw (IO.userError "import changed the original manifest")
  Purelib.System.IO.println
    "Saved forecast: formula checks, separate-process reuse, sum association and malformed-term rejection passed."

end SavedForecastHarness

/-- Dispatch forecast generation, saved-only replay, explicit import or the checkpoint regression. -/
@[expose] def main (arguments : List String) : IO Unit := do
  match arguments with
  | ["self-test", directory] => SavedForecastHarness.selfTest directory
  | ["import-saved", source, previous, directory, mode] =>
      SavedForecastHarness.run source directory mode true false (some previous)
  | [source, directory, mode, saved] =>
      unless saved == "generate" || saved == "saved-only" || saved == "crash" do throw (IO.userError
        "use generate or saved-only")
      SavedForecastHarness.run source directory mode (saved == "saved-only") (saved == "crash")
  | _ => throw (IO.userError
    "usage: saved_forecast_harness self-test FRESH_DIRECTORY | INPUTS_JSONL STORE right|blocked generate|saved-only | \
      import-saved INPUTS_JSONL OLD_STORE NEW_STORE right|blocked")

end
