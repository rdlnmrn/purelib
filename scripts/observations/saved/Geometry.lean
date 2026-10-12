module

import Purelib.System.IO
import Purelib.System.FilePath

meta import Purelib.Elab.ConstructiveInjectivity
meta import Purelib.Elab.Deriving.Json
import Purelib.Data.Json.Codec
import Purelib.Data.String.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic

public import Purelib.Riemann.Transport.PreparedGeometryReplay
public import scripts.checkpoint.Integration.Import
import Init.Prelude
import Init.System.FilePath
import Init.System.IO
import Init.System.IOError
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.CCL.Progressive.IntegrationQueries
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import scripts.checkpoint.Integration

-- Use complete constructor eliminators for the original match arms.
set_option backward.match.sparseCases false

open Purelib.Polynomial.Dense.Gaussian.Basic

open Purelib.Riemann.Transport

open Purelib.Data (Json)
open scoped Purelib.Data.List Purelib.Data.Range Purelib.Data.String

public section

/-!
Recover whole-segment endpoints from existing v1 refinement snapshots, without
branch isolation, prepared-owner search or centre generation.  Every saved
candidate is checked by affine evaluation on reload.  These are recovered
geometry data, not restored clearance/owner certificates or period receipts.
Run under an explicit SIGKILL timeout and systemd memory bounds.
-/

namespace SavedGeometryHarness

open IntegrationCheckpoint
open Purelib.Riemann.Transport.PreparedGeometryReplay

set_option genInjectivity false in
/-- The retained parent count and radicand coefficients of a saved geometry request.

The parent count and ordered radicand coefficients remain separate retained
fields. Scalar restoration preserves those coefficients without reconstructing
original parent ownership from the count. -/
structure Header where
  /-- The number of original ordered parent records. -/ parentCount : Nat
  /-- The serialized original radicand coefficients. -/ radicand : List GaussianData
deriving Json.FromJson, Json.ToJson

constructive_injectivity Header

set_option genInjectivity false in
/-- The ordered serialized local segment, source interval, polynomial value and sheet.

The selected parent, oriented endpoints, interval bounds, parameter and sheet
retain their distinct fields. Restoration checks their scalar readings without
identifying the original source from the serialized parent index. -/
structure Parent where
  /-- The original parent index in the retained stream. -/ parent : Nat
  /-- The serialized local starting point. -/ start : GaussianData
  /-- The serialized local finishing point. -/ finish : GaussianData
  /-- The serialized left source parameter. -/ left : FractionData
  /-- The serialized right source parameter. -/ right : FractionData
  /-- The retained polynomial value at the local starting point. -/ parameter : GaussianData
  /-- The original recorded sheet index. -/ sheet : Nat
deriving Json.FromJson, Json.ToJson

constructive_injectivity Parent

set_option genInjectivity false in
/-- Serialized endpoints of one recovered whole affine segment.

Both endpoints retain their separate exact Gaussian encodings.
They are restored with their original orientation before constructing geometry. -/
structure GeometryData where
  /-- The serialized starting point of the whole affine segment. -/ start : GaussianData
  /-- The serialized finishing point of the whole affine segment. -/ finish : GaussianData
deriving Json.FromJson, Json.ToJson

constructive_injectivity GeometryData

/-- Serialize the exact whole-segment endpoints. -/
@[expose] def geometryData (geometry : Geometry) : GeometryData :=
  ⟨gaussianData geometry.start, gaussianData geometry.finish⟩

/-- Decode the local endpoints and retained source interval. -/
@[expose] def decode (raw : Parent) : IO Inputs := do
  return ⟨← checked "local start" (decodeGaussian raw.start),
    ← checked "local finish" (decodeGaussian raw.finish),
    ← checked "left parameter" (decodeFraction raw.left),
    ← checked "right parameter" (decodeFraction raw.right)⟩

/-- Decode the exact whole-segment endpoint candidate. -/
@[expose] def decodeGeometry (raw : GeometryData) : IO Geometry := do
  return ⟨← checked "whole start" (decodeGaussian raw.start),
    ← checked "whole finish" (decodeGaussian raw.finish)⟩

/-- Describe the certified interval or affine-sample mismatch with its actual operands. -/
@[expose] def invalidityMessage : PreparedGeometryReplay.Invalidity → String
  | .leftOutside input _ => s!"left parameter is negative: {fractionText input.left}"
  | .rightOutside input _ => s!"right parameter exceeds one: {fractionText input.right}"
  | .unordered input _ =>
      s!"subinterval is not proper: {fractionText input.left}, {fractionText input.right}"
  | .leftMismatch input candidate actual _ _ =>

        s!"whole segment {gaussianText candidate.start} -> {gaussianText candidate.finish}: left sample \
          {gaussianText actual} != {gaussianText input.start}"
  | .rightMismatch input candidate actual _ _ =>

        s!"whole segment {gaussianText candidate.start} -> {gaussianText candidate.finish}: right sample \
          {gaussianText actual} != {gaussianText input.finish}"

/-- Check the candidate affine geometry against both original endpoint equations. -/
@[expose] def checkGeometry (input : Inputs) (candidate : Geometry) : IO (Solution input) := do
  match check input candidate with
  | .ok solution => return solution
  | .error invalid => throw (IO.userError (invalidityMessage invalid))

/-- Certify that the saved polynomial parameter equals its exact expected value. -/
@[expose] def checkParameter (actual expected : Gaussian) :
    Except InvalidData { value : Gaussian // value = expected } :=
  if same : actual = expected then .ok ⟨actual, same⟩
  else .error (.gaussianMismatch "saved polynomial parameter" actual expected same)

/-- Recover whole-segment endpoints from the original local inputs with a generation marker. -/
@[noinline, expose] def generate (index : Nat) (input : Inputs) : Geometry :=
  if index < 2 || index % 128 == 0 then
    dbg_trace s!"SAVED_GEOMETRY_GENERATED_{index}"
    recover input
  else recover input

/-- Evaluate a thunk through IO without inlining its timing boundary. -/
@[noinline, expose] def evaluate {α : Type} (work : Unit → α) : IO α := pure (work ())

set_option genInjectivity false in
/-- An informational grouping of consecutive records, not a switched-chain certificate. Preserve sheet and parameter
boundaries; do not invent omitted stationary switches, owner transitions or canonical bank identities.

The first parent, count, sheet and geometric request fields retain their
original ordered run. The exact interval bounds remain distinct from its
endpoint geometry and selected sheet. -/
structure SegmentRun where
  /-- The original index of the first record in this consecutive run. -/ firstParent : Nat
  /-- The number of consecutively grouped original parent records. -/ count : Nat
  /-- The retained common sheet index. -/ sheet : Nat
  /-- The shared recovered whole-segment endpoints. -/ geometry : GeometryData
  /-- The first retained source parameter of the run. -/ left : FractionData
  /-- The last retained source parameter of the run. -/ right : FractionData
deriving Json.ToJson, Json.FromJson

constructive_injectivity SegmentRun

/-- Extend the last informational run only when geometry, sheet and adjacent source parameters agree. -/
@[expose] def addRun (runs : Array SegmentRun) (raw : Parent) (input : Inputs)
    (geometry : Geometry) : IO (Array SegmentRun) := do
  let data := geometryData geometry
  if let some last := runs.back? then
    let previous ← decodeGeometry last.geometry
    let right ← checked "previous interval right" (decodeFraction last.right)
    if previous == geometry && last.sheet == raw.sheet && right == input.left then
      return runs.pop.push { last with count := last.count + 1, right := fractionData input.right }
  return runs.push ⟨raw.parent, 1, raw.sheet, data, fractionData input.left, fractionData input.right⟩

/-- Check and restore saved affine geometry in the original parent order.

Validate polynomial values and both endpoint equations, preserve atomic completed records and retain consecutive
grouping without reconstructing owners. -/
@[expose] def loadParents (source directory : System.FilePath) (onlySaved crashAfterFirst : Bool)
    (prior : Option System.FilePath) : IO Unit := do
  IO.FS.createDirAll ((Purelib.System.FilePath.join directory (System.FilePath.mk ("geometry"))))
  IO.FS.withFile source .read fun handle => do
    unless (Purelib.Data.String.trimAscii (← handle.getLine)) == "ccl-canonical-refinement-inputs-v1" do
      throw (IO.userError "expected canonical refinement inputs v1")
    let header : Header ← parseJson "header" (← handle.getLine)
    let coefficients ← header.radicand.mapM fun value => checked "polynomial coefficient" (decodeGaussian value)
    let polynomial : Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial :=
      ⟨coefficients⟩
    let mut reused := 0
    let mut runs := #[]
    for index in [:header.parentCount] do
      let raw : Parent ← parseJson s!"parent {index}" (← handle.getLine)
      unless raw.parent == index do throw (IO.userError "parent order does not match the snapshot")
      let input ← decode raw
      let parameter ← checked "saved parameter" (decodeGaussian raw.parameter)
      discard <| checked s!"parent {index}" (checkParameter parameter (polynomial.eval input.start))
      let path := (Purelib.System.FilePath.join (Purelib.System.FilePath.join directory (System.FilePath.mk
        ("geometry"))) (System.FilePath.mk (s!"{index}.json")))
      let readPath := if ← path.pathExists then path
        else (Purelib.System.FilePath.join (Purelib.System.FilePath.join (prior.getD directory) (System.FilePath.mk
          ("geometry"))) (System.FilePath.mk (s!"{index}.json")))
      let solution ← if ← readPath.pathExists then do
        let raw : GeometryData ← loadJson readPath
        let solution ← checkGeometry input (← decodeGeometry raw)
        if readPath != path then saveJson path (geometryData solution.geometry)
        reused := reused + 1
        pure solution
      else do
        if onlySaved then throw (IO.userError s!"parent {index}: restart would invoke geometry generation")
        let candidate ← evaluate fun _ => generate index input
        let solution ← checkGeometry input candidate
        saveJson path (geometryData solution.geometry)
        pure solution
      runs ← addRun runs raw input solution.geometry
      if crashAfterFirst && index == 0 then
        let pid ← IO.Process.getPID
        discard <| Purelib.System.IO.Process.output { cmd := "/bin/kill", args := #["-KILL", toString pid] }
        throw (IO.userError "checkpoint-boundary SIGKILL failed")
      if (index + 1) % 128 == 0 then
        profile directory
          s!"geometry {index + 1}/{header.parentCount}; reused={reused}; consecutive segment runs={runs.size}"
    unless (← handle.getLine).isEmpty do throw (IO.userError "unexpected extra parent records")
    saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk ("segment-runs.json")))) runs
    profile directory
      s!"COMPLETE checked geometry: parents={header.parentCount}; reused={reused}; \
        generated={header.parentCount - reused}; consecutive segment runs={runs.size}; clearance/owner history \
        unresolved; no period receipt"

/-- Bind the source snapshot and explicitly restore or import checked numerical geometry.

The source store remains unchanged and every resumed import must retain the same original and destination manifests. -/
@[expose] def run (source directory : System.FilePath) (onlySaved : Bool)
    (crashAfterFirst : Bool := false) (prior : Option System.FilePath := none) : IO Unit := do
  let hash ← Purelib.System.IO.Process.output { cmd := "sha256sum", args := #[source.toString] }
  unless hash.exitCode == 0 do throw (IO.userError "snapshot fingerprint failed")
  let digest := ((Purelib.Data.String.splitOn hash.stdout " ")).head!
  let identity := s!"saved affine geometry v1; source sha256={digest}; clearance/owner history unresolved"
  let origin ← match prior with
    | none => pure none
    | some previous => do
        let resolved ← IO.FS.realPath previous
        if ← directory.pathExists then
          if (← IO.FS.realPath directory) == resolved then
            throw (IO.userError "import source and destination must be distinct")
        let manifest : Manifest ← loadJson ((Purelib.System.FilePath.join previous (System.FilePath.mk
          ("manifest.json"))))
        match checkImportIdentity identity manifest with
        | .ok _ => pure ()
        | .error (.format actual _) => throw (IO.userError s!"import format rejected: {actual}")
        | .error (.identity actual expected _) =>
            throw (IO.userError s!"import source identity differs: {actual}; expected {expected}")
        pure (some (resolved.toString, manifest))
  openStore directory identity
  if let some (previous, manifest) := origin then
    let destination : Manifest ← loadJson ((Purelib.System.FilePath.join directory (System.FilePath.mk
      ("manifest.json"))))
    let record : ImportOrigin := ⟨previous, manifest, destination⟩
    let path := (Purelib.System.FilePath.join directory (System.FilePath.mk ("geometry-import.json")))
    if ← path.pathExists then
      let retained : ImportOrigin ← loadJson path
      unless retained == record do throw (IO.userError "destination already records a different import")
    else saveJson path record
  profile directory "BEGIN saved affine geometry; no canonical preparation"
  loadParents source directory onlySaved crashAfterFirst prior

/-- Check exact endpoint recovery, interrupted-prefix reuse and typed invalidity rejection.

Also verify explicit cross-build import, unchanged source provenance and rejection before destination creation for wrong
identities. -/
@[expose] def selfTest (directory : System.FilePath) : IO Unit := do
  if ← directory.pathExists then throw (IO.userError "self-test requires a fresh directory")
  IO.FS.createDirAll directory
  let source := (Purelib.System.FilePath.join directory (System.FilePath.mk ("inputs.jsonl")))
  let header : Header := ⟨2, [gaussianData 1]⟩
  let geometry : Geometry := ⟨⟨1, 2⟩, ⟨3, 4⟩⟩
  let half : Coordinate := 1 / 2
  let input0 : Inputs := ⟨geometry.at 0, geometry.at half, 0, half⟩
  let input1 : Inputs := ⟨geometry.at half, geometry.at 1, half, 1⟩
  let parent := fun index (input : Inputs) => (⟨index, gaussianData input.start,
    gaussianData input.finish, fractionData input.left, fractionData input.right,
    gaussianData 1, 0⟩ : Parent)
  atomicText source ("ccl-canonical-refinement-inputs-v1\n" ++ jsonText header ++ "\n" ++
    jsonText (parent 0 input0) ++ "\n" ++ jsonText (parent 1 input1) ++ "\n")
  let executable := (← IO.appPath).toString
  let invoke := fun (store mode : String) => Purelib.System.IO.Process.output
    { cmd := "/usr/bin/timeout", args := #["--signal=KILL", "30s", executable,
        source.toString, ((Purelib.System.FilePath.join directory (System.FilePath.mk (store)))).toString, mode] }
  let fresh ← invoke "store" "generate"
  unless fresh.exitCode == 0 && ((Purelib.Data.String.splitOn (fresh.stdout ++ fresh.stderr)
    "SAVED_GEOMETRY_GENERATED_0")).length > 1 do
    throw (IO.userError ("fresh marker calibration failed\n" ++ fresh.stdout ++ fresh.stderr))
  let runs : Array SegmentRun ← loadJson ((Purelib.System.FilePath.join (Purelib.System.FilePath.join directory
    (System.FilePath.mk ("store"))) (System.FilePath.mk ("segment-runs.json"))))
  unless runs.toList.map (·.count) == [2] do
    throw (IO.userError "consecutive geometry grouping failed")
  let actual : GeometryData ← loadJson ((Purelib.System.FilePath.join (Purelib.System.FilePath.join
    (Purelib.System.FilePath.join directory (System.FilePath.mk ("store"))) (System.FilePath.mk ("geometry")))
    (System.FilePath.mk ("0.json"))))
  unless (← decodeGeometry actual) == geometry do throw (IO.userError "recovered endpoints differ")
  let resumed ← invoke "store" "saved-only"
  unless resumed.exitCode == 0 && ((Purelib.Data.String.splitOn (resumed.stdout ++ resumed.stderr) "GENERATED_")).length
    == 1 do
    throw (IO.userError ("restart repeated generation\n" ++ resumed.stdout ++ resumed.stderr))
  let crashed ← invoke "partial" "crash"
  unless crashed.exitCode == 137 do throw (IO.userError "partial fixture did not receive SIGKILL")
  unless ← ((Purelib.System.FilePath.join (Purelib.System.FilePath.join (Purelib.System.FilePath.join directory
    (System.FilePath.mk ("partial"))) (System.FilePath.mk ("geometry"))) (System.FilePath.mk ("0.json")))).pathExists do
    throw (IO.userError "interruption lost the completed geometry")
  let resumedPartial ← invoke "partial" "generate"
  let output := resumedPartial.stdout ++ resumedPartial.stderr
  unless resumedPartial.exitCode == 0 && ((Purelib.Data.String.splitOn output "SAVED_GEOMETRY_GENERATED_0")).length == 1
    &&
      ((Purelib.Data.String.splitOn output "SAVED_GEOMETRY_GENERATED_1")).length > 1 do
    throw (IO.userError ("partial restart failed to skip its completed prefix\n" ++ output))
  match check input0 { geometry with start := 0 } with
  | .error (.leftMismatch _ _ _ _ _) => pure ()
  | _ => throw (IO.userError "wrong start was not certified invalid")
  match check input0 { geometry with finish := 0 } with
  | .error (.rightMismatch _ _ _ _ _) => pure ()
  | _ => throw (IO.userError "wrong finish was not certified invalid")
  match check { input0 with right := 0 } geometry with
  | .error (.unordered _ _) => pure ()
  | _ => throw (IO.userError "degenerate subinterval was not certified invalid")
  match check { input0 with left := -1 } geometry with
  | .error (.leftOutside _ _) => pure ()
  | _ => throw (IO.userError "negative left parameter was not certified invalid")
  match check { input0 with right := 2 } geometry with
  | .error (.rightOutside _ _) => pure ()
  | _ => throw (IO.userError "excessive right parameter was not certified invalid")
  match checkParameter 0 1 with
  | .error (.gaussianMismatch _ _ _ _) => pure ()
  | _ => throw (IO.userError "incorrect polynomial value was not certified invalid")
  let original : Manifest ← loadJson ((Purelib.System.FilePath.join (Purelib.System.FilePath.join directory
    (System.FilePath.mk ("store"))) (System.FilePath.mk ("manifest.json"))))
  let old : Manifest := { original with binarySha256 := "simulated-old-geometry-binary" }
  saveJson ((Purelib.System.FilePath.join (Purelib.System.FilePath.join directory (System.FilePath.mk ("store")))
    (System.FilePath.mk ("manifest.json")))) old
  let rejected ← invoke "store" "saved-only"
  unless rejected.exitCode != 0 do throw (IO.userError "ordinary resume silently accepted a changed binary")
  let importRun := fun (mode target : String) => Purelib.System.IO.Process.output
    { cmd := "/usr/bin/timeout", args := #["--signal=KILL", "30s", executable, mode,
        source.toString, ((Purelib.System.FilePath.join directory (System.FilePath.mk ("store")))).toString,
          ((Purelib.System.FilePath.join directory (System.FilePath.mk (target)))).toString] }
  let interrupted ← importRun "import-crash" "imported"
  unless interrupted.exitCode == 137 do throw (IO.userError "import fixture did not receive SIGKILL")
  unless ← ((Purelib.System.FilePath.join (Purelib.System.FilePath.join (Purelib.System.FilePath.join directory
    (System.FilePath.mk ("imported"))) (System.FilePath.mk ("geometry"))) (System.FilePath.mk ("0.json")))).pathExists
    do
    throw (IO.userError "interrupted import lost its checked prefix")
  let imported ← importRun "import-saved" "imported"
  unless imported.exitCode == 0 && ((Purelib.Data.String.splitOn (imported.stdout ++ imported.stderr)
    "GENERATED_")).length == 1 do
    throw (IO.userError ("checked cross-build import failed\n" ++ imported.stdout ++ imported.stderr))
  let preserved : Manifest ← loadJson ((Purelib.System.FilePath.join (Purelib.System.FilePath.join directory
    (System.FilePath.mk ("store"))) (System.FilePath.mk ("manifest.json"))))
  unless preserved == old do throw (IO.userError "import changed original provenance")
  saveJson ((Purelib.System.FilePath.join (Purelib.System.FilePath.join directory (System.FilePath.mk ("store")))
    (System.FilePath.mk ("manifest.json")))) { old with sourceIdentity := "different source" }
  let wrong ← importRun "import-saved" "wrong-source"
  if wrong.exitCode == 0 || (← ((Purelib.System.FilePath.join directory (System.FilePath.mk
    ("wrong-source")))).pathExists) then
    throw (IO.userError "wrong source was not rejected before creating a destination")
  saveJson ((Purelib.System.FilePath.join (Purelib.System.FilePath.join directory (System.FilePath.mk ("store")))
    (System.FilePath.mk ("manifest.json")))) { old with format := "different format" }
  let wrongFormat ← importRun "import-saved" "wrong-format"
  if wrongFormat.exitCode == 0 || (← ((Purelib.System.FilePath.join directory (System.FilePath.mk
    ("wrong-format")))).pathExists) then
    throw (IO.userError "wrong format was not rejected before creating a destination")
  saveJson ((Purelib.System.FilePath.join (Purelib.System.FilePath.join directory (System.FilePath.mk ("store")))
    (System.FilePath.mk ("manifest.json")))) old
  saveJson ((Purelib.System.FilePath.join (Purelib.System.FilePath.join (Purelib.System.FilePath.join directory
    (System.FilePath.mk ("partial"))) (System.FilePath.mk ("geometry"))) (System.FilePath.mk ("1.json")))) (geometryData
    ⟨0, 0⟩)
  let malformed ← invoke "partial" "saved-only"
  unless malformed.exitCode != 0 do throw (IO.userError "modified saved geometry was accepted")
  Purelib.System.IO.println
    "Saved geometry: exact endpoints, checked restart/import, interrupted-prefix reuse and typed invalidity tests \
      passed."

end SavedGeometryHarness

/-- Dispatch geometry generation, saved-only replay, explicit import or checkpoint regression. -/
@[expose] def main (arguments : List String) : IO Unit := do
  match arguments with
  | ["self-test", directory] => SavedGeometryHarness.selfTest directory
  | ["import-saved", source, previous, directory] =>
      SavedGeometryHarness.run source directory true false (some previous)
  | ["import-crash", source, previous, directory] =>
      SavedGeometryHarness.run source directory true true (some previous)
  | [source, directory, mode] =>
      unless mode == "generate" || mode == "saved-only" || mode == "crash" do
        throw (IO.userError "use generate or saved-only")
      SavedGeometryHarness.run source directory (mode == "saved-only") (mode == "crash")
  | _ => throw (IO.userError
    "usage: saved_geometry_harness self-test FRESH_DIRECTORY | INPUTS_JSONL STORE generate|saved-only | import-saved \
      INPUTS_JSONL OLD_STORE NEW_STORE")
