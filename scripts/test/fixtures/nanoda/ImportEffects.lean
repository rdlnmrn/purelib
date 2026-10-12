module

import Lean

namespace NanodaImportEffects

open Lean

meta section

/-- Record execution of a target initializer when a test supplies its marker path. -/
initialize sentinel : Unit ← do
  if let some marker ← IO.getEnv "NANODA_INITIALIZER_MARKER" then
    IO.FS.writeFile marker "target initializer executed"

/-- Record execution of a target extension's import callback. -/
initialize callback : PersistentEnvExtension Name Name (Array Name) ←
  registerPersistentEnvExtension {
    name := `NanodaImportEffects.callback
    mkInitial := pure #[]
    addImportedFn := fun _ => do
      if let some marker ← IO.getEnv "NANODA_CALLBACK_MARKER" then
        IO.FS.writeFile marker "target import callback executed"
      pure #[]
    addEntryFn := Array.push
    exportEntriesFn := fun entries => entries
  }

end

/-- A retained private proof independent of target initialization. -/
private theorem privateProof : True := True.intro

/-- An unused private source proof selected by the authoritative root policy. -/
private theorem unusedProof : True := by exact True.intro

/-- A public proof whose complete body depends on a private proof. -/
public theorem sourceProof : True := privateProof

/-- A source function eligible for a registered compiler rewrite. -/
@[expose] public def original : Nat := 1

/-- A retained replacement for the same executable source function. -/
@[expose] public def replacement : Nat := 1

/-- A registered global rewrite retained despite its generated logical suffix. -/
@[csimp] public theorem compiler.eq_def : original = replacement := rfl

/-- An unsafe declaration excluded from mathematical roots. -/
public unsafe def unsafeValue : Nat := 3

/-- A meta declaration excluded from mathematical roots. -/
public meta def metaValue : Nat := 4

end NanodaImportEffects
