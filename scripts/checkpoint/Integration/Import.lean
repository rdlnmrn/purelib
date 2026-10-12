module

import Purelib.System.FilePath

meta import Purelib.Elab.ConstructiveInjectivity
meta import Purelib.Elab.Deriving.Json
import Purelib.Data.Json.Codec
import Purelib.Data.String.Basic
import Purelib.Data.String.Parsing
import Purelib.Data.List.Control
-- Exposed numerical imports retain the original stable index sorter.
public import Purelib.Data.List.Sort.Basic
import Purelib.Integration.Program.Gaussian.Cached.Basic
import Purelib.Integration.CertifiedProgram

public import scripts.checkpoint.Integration
import Init.Prelude
import Init.System.FilePath
import Init.System.IO
import Init.System.IOError
import Purelib.CCL.Progressive.IntegrationQueries
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.Basic

open Purelib.Integration.CertifiedProgram

open Purelib.Integration.Program.Gaussian

open Purelib.Data (Json)
open Purelib.Data.String
open scoped Purelib.Data.List Purelib.Data.Range Purelib.Data.String Purelib.Data.List

public section

/-!
Explicit, restartable numerical checkpoint import across executable rebuilds.
The original store is read-only.  Exact input identity and finite numerical
checks are mandatory; neither fingerprints nor import reconstruct ownership.
Receipts and their fresh-source flags are deliberately not imported.
-/

namespace IntegrationCheckpoint

set_option genInjectivity false in
/-- A certified checkpoint-format or source-identity mismatch.

Each constructor retains the original actual text and its failed comparison
with the expected format or source identity. It does not discard either operand. -/
inductive ImportInvalidity where
  /-- The recorded format differs from the supported checkpoint format. -/ | format (actual : String) (invalid : actual
    ≠ "ccl-integration-checkpoint-v1")
  /-- The actual and expected source identities are unequal. -/ | identity (actual expected : String) (invalid : actual
    ≠ expected)

constructive_injectivity ImportInvalidity

/-- Certify the supported checkpoint format and exact expected source identity. -/
@[expose] def checkImportIdentity (expected : String) (manifest : Manifest) :
    Except ImportInvalidity (PLift
      (manifest.format = "ccl-integration-checkpoint-v1" ∧ manifest.sourceIdentity = expected)) :=
  if format : manifest.format = "ccl-integration-checkpoint-v1" then
    if identity : manifest.sourceIdentity = expected then .ok ⟨⟨format, identity⟩⟩
    else .error (.identity manifest.sourceIdentity expected identity)
  else .error (.format manifest.format format)

set_option genInjectivity false in
/-- The original source directory and both retained executable-store manifests.

Both retained manifests remain separate from the resolved original directory.
An import binds the source and destination stores while retaining their distinct
executable identities and verification scope. -/
structure ImportOrigin where
  /-- The resolved original source-store directory. -/ sourceDirectory : String
  /-- The retained original source-store manifest. -/ sourceManifest : Manifest
  /-- The retained destination manifest for this explicit import. -/ destinationManifest : Manifest
deriving Json.ToJson, Json.FromJson, BEq

constructive_injectivity ImportOrigin

set_option genInjectivity false in
/-- The completed numerical import work and its explicit verification scope.

The ordered model indices, cell count and controller/request outcomes record
completed checked numerical work. The retained verification text distinguishes
that work from reconstruction of original source ownership. -/
structure ImportReport where
  /-- The ordered indices of complete checked numerical models. -/ models : List Nat
  /-- The number of individually checked and imported cells. -/ cells : Nat
  /-- Whether a checked controller record was imported. -/ control : Bool
  /-- Whether a checked positive-target request was imported. -/ request : Bool
  /-- The explicit statement that numerical validation does not reconstruct source ownership. -/ verification : String
    := "checked numerical data only; no reconstructed source ownership"
deriving Json.ToJson, Json.FromJson

constructive_injectivity ImportReport

/-- Write a new JSON record or require exact agreement with its existing retained value.

An existing file is loaded once and its complete serialized value is compared
with the supplied record. Agreement retains that file; disagreement rejects
overwrite, and only an absent file is written. -/
@[expose] def importJson {α : Type} [Json.ToJson α] [Json.FromJson α]
    (path : System.FilePath) (value : α) : IO Unit := do
  if ← path.pathExists then
    let retained : α ← loadJson path
    unless jsonText retained == jsonText value do
      throw (IO.userError s!"{path}: existing imported data differ; refusing to overwrite")
  else saveJson path value

set_option backward.match.sparseCases false in
/-- Parse a canonical model index from supported model, reply or cell-directory names.

Only canonical supported model, reply and cell-directory suffixes are accepted.
The decimal index must round-trip to the original filename component. -/
@[expose] def modelFileIndex (name : String) : Option Nat := do
  let ["model", suffix] := splitOn name "-" | none
  let number ← match splitOn suffix "." with
    | [number, "cells", "jsonl"] => some number
    | [number, "reply", "json"] => some number
    | [number, "cells"] => some number
    | _ => none
  let index ← toNat? number
  if number == toString index then some index else none

set_option backward.match.sparseCases false in
/-- Parse a canonical cell index from an individual JSON cell filename.

Only a canonical cell prefix and json suffix are accepted. The parsed decimal
index must round-trip to its original filename component. -/
@[expose] def cellFileIndex (name : String) : Option Nat := do
  let ["cell", suffix] := splitOn name "-" | none
  let [number, "json"] := splitOn suffix "." | none
  let index ← toNat? number
  if number == toString index then some index else none

/-- Check and import a complete numerical model and its exact cached reply.

Reject replies without complete models and retain any existing destination only when every serialized cell agrees. -/
@[expose] def importModel (source destination : System.FilePath) (index : Nat) : IO Bool := do
  let hasModel ← ((Purelib.System.FilePath.join source (System.FilePath.mk (s!"model-{index}.cells.jsonl")))).pathExists
  let hasReply ← ((Purelib.System.FilePath.join source (System.FilePath.mk (s!"model-{index}.reply.json")))).pathExists
  if hasReply && !hasModel then
    throw (IO.userError s!"model {index}: saved reply has no complete model")
  unless hasModel do return false
  profile destination s!"import model {index}: BEGIN numerical checks; no generator"
  let model ← loadModel source index
  let reply ← if hasReply then do
      let raw : ReplyData ← loadJson ((Purelib.System.FilePath.join source (System.FilePath.mk
        (s!"model-{index}.reply.json"))))
      pure (← checked s!"import model {index}" (decodeReply model raw)).val
    else pure (CachedModel.canonical (operations := Cached.Basic.modelOperations) model)
  if ← ((Purelib.System.FilePath.join destination (System.FilePath.mk (s!"model-{index}.cells.jsonl")))).pathExists then
    let retained ← loadModel destination index
    unless (retained.cells.map (fun cell => jsonText (cellData cell))) ==
        (model.cells.map (fun cell => jsonText (cellData cell))) do
      throw (IO.userError s!"model {index}: existing imported cells differ; refusing to overwrite")
  else saveModel destination index model
  importJson ((Purelib.System.FilePath.join destination (System.FilePath.mk (s!"model-{index}.reply.json")))) (replyData
    reply)
  profile destination s!"import model {index}: END checked reuse; source generator not called"
  return true

/-- Decode and import individual cells in sorted source-index order while retaining completed work.

The original source indices are sorted before traversal. Each cell is decoded
and checked once, and completed destination records are kept only after exact
agreement with that checked source cell. -/
@[expose] def importCells (source destination : System.FilePath) (index : Nat) : IO Nat := do
  let sourceCells := (Purelib.System.FilePath.join source (System.FilePath.mk (s!"model-{index}.cells")))
  unless ← sourceCells.pathExists do return 0
  let entries ← sourceCells.readDir
  let indices := (Purelib.Data.List.Sort.mergeSort (entries.toList.filterMap fun entry => cellFileIndex entry.fileName))
  let targetCells := (Purelib.System.FilePath.join destination (System.FilePath.mk (s!"model-{index}.cells")))
  IO.FS.createDirAll targetCells
  let mut imported := 0
  for offset in indices do
    let raw : CellData ← loadJson ((Purelib.System.FilePath.join sourceCells (System.FilePath.mk
      (s!"cell-{offset}.json"))))
    let cell ← checked s!"import model {index}, cell {offset}" (decodeCell raw)
    importJson ((Purelib.System.FilePath.join targetCells (System.FilePath.mk (s!"cell-{offset}.json")))) (cellData
      cell)
    imported := imported + 1
    if imported % 1024 == 0 then
      profile destination s!"import model {index}: {imported} individual cells checked; no generator"
  return imported

/-- Import checked numerical work into this executable's store. Repeating the same import checks and keeps completed
destination files. An unrelated existing destination is never overwritten. Preparation/refinement snapshots have no
loader here and are not falsely advertised as restored source state. -/
@[expose] def importNumerical (source destination : System.FilePath) (expectedIdentity : String) : IO ImportReport := do
  let source ← IO.FS.realPath source
  let original : Manifest ← loadJson ((Purelib.System.FilePath.join source (System.FilePath.mk ("manifest.json"))))
  match checkImportIdentity expectedIdentity original with
  | .error (.format actual _) => throw (IO.userError s!"unsupported checkpoint format: {actual}")
  | .error (.identity actual expected _) =>
      throw (IO.userError s!"checkpoint source identity differs: actual={actual}; expected={expected}")
  | .ok _ => pure ()
  let originPath := (Purelib.System.FilePath.join destination (System.FilePath.mk ("import-origin.json")))
  let existing ← destination.pathExists
  if existing then
    let resolvedDestination ← IO.FS.realPath destination
    if resolvedDestination == source then
      throw (IO.userError "the import destination must differ from the original store")
  if existing && !(← originPath.pathExists) then
    throw (IO.userError "import requires a new destination or the same interrupted import")
  openStore destination expectedIdentity
  let target : Manifest ← loadJson ((Purelib.System.FilePath.join destination (System.FilePath.mk ("manifest.json"))))
  let origin : ImportOrigin := ⟨source.toString, original, target⟩
  importJson originPath origin
  profile destination "BEGIN explicit numerical import; original store preserved"
  let hasControl ← ((Purelib.System.FilePath.join source (System.FilePath.mk ("control.json")))).pathExists
  if hasControl then
    let raw : ControlData ← loadJson ((Purelib.System.FilePath.join source (System.FilePath.mk ("control.json"))))
    let control ← checked "import control" (decodeControl raw)
    importJson ((Purelib.System.FilePath.join destination (System.FilePath.mk ("control.json")))) (controlData control)
  let hasRequest ← ((Purelib.System.FilePath.join source (System.FilePath.mk ("request.json")))).pathExists
  if hasRequest then
    let raw : Nat × FractionData ← loadJson ((Purelib.System.FilePath.join source (System.FilePath.mk
      ("request.json"))))
    let target ← checked "import request" (decodeFraction raw.2)
    unless 0 < target do throw (IO.userError "saved observation target is not positive")
    importJson ((Purelib.System.FilePath.join destination (System.FilePath.mk ("request.json")))) (raw.1, fractionData
      target)
  let entries ← source.readDir
  let indices := (Purelib.Data.List.Sort.mergeSort ((entries.toList.filterMap fun entry => modelFileIndex
    entry.fileName).eraseDups))
  let mut models := []
  let mut cells := 0
  for index in indices do
    if ← importModel source destination index then models := models ++ [index]
    cells := cells + (← importCells source destination index)
    saveJson ((Purelib.System.FilePath.join destination (System.FilePath.mk ("import-progress.json"))))
      ({ models := models, cells := cells, control := hasControl, request := hasRequest } : ImportReport)
  let report : ImportReport :=
    { models := models, cells := cells, control := hasControl, request := hasRequest }
  saveJson ((Purelib.System.FilePath.join destination (System.FilePath.mk ("import-complete.json")))) report
  profile destination
    s!"COMPLETE numerical import: {models.length} models, {cells} individual cells; no source-ownership proof or \
      receipt imported"
  return report

end IntegrationCheckpoint
