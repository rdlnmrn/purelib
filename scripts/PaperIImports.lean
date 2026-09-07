import ImportGraph.Imports.FromSource

/-!
Print the exact source-level transitive import closure of the Paper-I facade.
The companion shell check rejects every CCL module and all CCL-2 adapters;
the finite rational-box carrier is `RFAP.Boxes`.
-/

open Lean System

#eval do
  let imports ← findTransitiveImportsFromSource "RFAP/Paper.lean"
  for moduleName in imports.toArray.qsort Name.lt do
    IO.println moduleName
