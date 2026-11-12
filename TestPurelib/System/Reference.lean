module

import Purelib.System.IO.Reference

/-! # Shared reference identity, retained snapshots and mutation after errors -/

namespace TestPurelib.System.Reference

open Purelib.System.IO

/-- Check shared mutation, retained heap values and updates preceding an IO error.

Both native adapters and the original set operation consume the same reference
carrier. An alias observes each completed write, an earlier list remains
unchanged, and a caught loader error preserves the completed update.
-/
public def check : IO Unit := do
  let reference ← mkRef ([1, 2] : List Nat)
  let alias := reference
  let previous ← Ref.get reference
  Ref.modify reference (fun values => values ++ [3])
  unless previous == [1, 2] && (← Ref.get alias) == [1, 2, 3] do
    throw (IO.userError "a reference update changed a snapshot or lost its alias")
  unless ← ST.Ref.ptrEq reference alias do
    throw (IO.userError "a reference adapter replaced the original cell")
  let snapshot ← Ref.get alias
  reference.set [4, 5]
  unless snapshot == [1, 2, 3] && (← Ref.get alias) == [4, 5] do
    throw (IO.userError "the original set operation lost the shared cell")
  let result ← (do
    Ref.modify reference (fun values => values ++ [6])
    throw (IO.userError "intentional loader error") : IO Unit).toBaseIO
  match result with
  | .ok _ => throw (IO.userError "an intentional loader error was discarded")
  | .error (.userError message) =>
      unless message == "intentional loader error" do
        throw (IO.userError "a reference adapter changed the loader error")
  | .error error => throw error
  unless snapshot == [1, 2, 3] && (← Ref.get alias) == [4, 5, 6] do
    throw (IO.userError "a loader error discarded an earlier reference update")

-- Lake must load the reference library for interpreted construction as well.
#eval check

end TestPurelib.System.Reference

/-- Execute the original-reference regression as a native standalone client. -/
public def main : IO Unit := TestPurelib.System.Reference.check
