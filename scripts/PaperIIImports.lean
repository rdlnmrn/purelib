import ImportGraph.Imports.FromSource

/-!
Print the exact source-level transitive import closure of the combined
CCL-1/CCL-2 umbrella.  The companion shell check rejects legacy modules and
stale module names while requiring both the CCL facade and its RFAP adapter.
-/

open Lean System

#eval do
  let imports ← findTransitiveImportsFromSource "CCL.lean"
  for moduleName in imports.toArray.qsort Name.lt do
    IO.println moduleName
