import ImportGraph.Imports.FromSource

/-!
Print the exact source-level transitive import closure of the finite measure
umbrella.  The companion shell check rejects completed-object, infinitary,
topological, and upstream measure-theory modules.
-/

open Lean System

#eval do
  let imports ← findTransitiveImportsFromSource "FiniteMeasure.lean"
  for moduleName in imports.toArray.qsort Name.lt do
    IO.println moduleName
