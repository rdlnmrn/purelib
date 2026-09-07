import Export
import Lean.Compiler.MetaAttr

/-!
Exports every source-facing, kernel-checkable declaration defined by the
project modules named in a newline-delimited manifest. Declaration provenance
comes from Lean's compiled module metadata, so no list of theorem names or
facade modules has to be maintained. Private and generated dependencies are
included transitively by lean4export whenever a checked declaration uses them.

Standard output is reserved for lean4export's NDJSON stream.  Human-readable
progress goes to standard error so the stream can be piped directly to nanoda.
-/

open Lean

private def readModuleManifest (path : System.FilePath) : IO (Array Name) := do
  let contents ← IO.FS.readFile path
  let modules := contents.splitOn "\n" |>.filterMap fun line =>
    let moduleName := line.trimAscii.toString
    if moduleName.isEmpty then none else some moduleName.toName
  if modules.isEmpty then
    throw <| IO.userError s!"nanoda module manifest is empty: {path}"
  pure modules.toArray

private def isSourceFacing (environment : Environment) (name : Name)
    (info : ConstantInfo) : Bool :=
  let generatedCongruence := name.toString.endsWith ".congr_simp"
  let generatedEquation := name.toString.endsWith ".eq_def"
  let generatedInduction := name.toString.endsWith ".induct_unfolding"
  !(name.isInternal || generatedCongruence || generatedEquation ||
      generatedInduction || info.isUnsafe || info.isPartial ||
      Lean.isMarkedMeta environment name)

def main (args : List String) : IO Unit := do
  let manifest ← match args with
    | [path] => pure (System.FilePath.mk path)
    | _ => throw (IO.userError
        "usage: lean --run scripts/ProjectNanodaExport.lean MODULE_MANIFEST")
  initSearchPath (← findSysroot)
  let modules ← readModuleManifest manifest
  let imports : Array Import := modules.map fun moduleName =>
    { module := moduleName }
  let environment ← importModules imports {}
  let mut roots : Array Name := #[]
  let mut seen : NameSet := {}
  let mut runtimeAuxiliaries : Array (Name × Name) := #[]
  let mut unexpectedNonKernel : Array (Name × Name) := #[]
  for moduleName in modules do
    let some moduleIndex := environment.getModuleIdx? moduleName
      | throw <| IO.userError s!"nanoda exporter did not import: {moduleName}"
    let some moduleData := environment.header.moduleData[moduleIndex.toNat]?
      | throw <| IO.userError s!"nanoda exporter found no module data for: {moduleName}"
    for name in moduleData.constNames ++ moduleData.extraConstNames do
      unless seen.contains name do
        if let some info := environment.constants.find? name then
          seen := seen.insert name
          if info.isUnsafe || info.isPartial then
            if info.isPartial && name.toString.endsWith "._unsafe_rec" then
              runtimeAuxiliaries := runtimeAuxiliaries.push (moduleName, name)
            else
              unexpectedNonKernel := unexpectedNonKernel.push (moduleName, name)
          else if isSourceFacing environment name info then
            roots := roots.push name
  unless unexpectedNonKernel.isEmpty do
    let examples := unexpectedNonKernel.extract 0 (min 10 unexpectedNonKernel.size)
    throw <| IO.userError s!"nanoda found unexpected unsafe or partial project declarations: {examples.toList}"
  IO.eprintln s!"nanoda: exporting {roots.size} source-facing declarations from {modules.size} project modules"
  if !runtimeAuxiliaries.isEmpty then
    IO.eprintln s!"nanoda: ignored {runtimeAuxiliaries.size} compiler-generated _unsafe_rec runtime auxiliaries"
    if (← IO.getEnv "NANODA_VERBOSE").isSome then
      for (moduleName, name) in runtimeAuxiliaries do
        IO.eprintln s!"nanoda: runtime auxiliary\t{moduleName}\t{name}"
  M.run environment do
    initState environment
    dumpMetadata
    for root in roots do
      modify fun state => { state with noMDataExprs := {} }
      dumpConstant root
