import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts
import Lean.Elab.Command

/-!
# Compact declaration-to-axiom tracing

`#trace_axiom target in declaration` reports whether `declaration` depends on
`target`, the target-bearing immediate dependencies of `declaration`, and one
shortest dependency path from the declaration to the target.  The shell
wrapper `scripts/trace-axiom.sh` supplies the project import and invokes this
command without requiring a task-specific Lean probe.
-/

namespace AxiomTrace

open Lean Elab Command

private def targetBearingDependencies
    (environment : Environment) (target declaration : Name) :
    CommandElabM (Array Name) := do
  let some info := environment.constants.find? declaration
    | throwError m!"unknown declaration {declaration}"
  let mut dependencies : Array Name := #[]
  for dependency in info.getUsedConstantsAsSet do
    if dependency == target then
      dependencies := dependencies.push dependency
    else
      let axioms ← Lean.collectAxioms dependency
      if axioms.contains target then
        dependencies := dependencies.push dependency
  return dependencies.qsort Name.lt

private def shortestDependencyPath
    (environment : Environment) (target declaration : Name) :
    CommandElabM (Option (List Name)) := do
  let mut queue : Array (Name × List Name) := #[(declaration, [declaration])]
  let mut visited : NameSet := {}
  visited := visited.insert declaration
  let mut next : Nat := 0
  let mut result : Option (List Name) := none
  while next < queue.size && result.isNone do
    let (current, path) := queue[next]!
    next := next + 1
    if current == target then
      result := some path
    else if let some info := environment.constants.find? current then
      for dependency in info.getUsedConstantsAsSet.toArray.qsort Name.lt do
        unless visited.contains dependency do
          let dependencyCarriesTarget ←
            if dependency == target then
              pure true
            else do
              let dependencyAxioms ← Lean.collectAxioms dependency
              pure (dependencyAxioms.contains target)
          if dependencyCarriesTarget then
            visited := visited.insert dependency
            queue := queue.push (dependency, path ++ [dependency])
  return result

private def namesText (names : Array Name) : String :=
  "[" ++ String.intercalate ", " (names.toList.map Name.toString) ++ "]"

private def pathText (path : List Name) : String :=
  String.intercalate " -> " (path.map Name.toString)

private partial def directApplications (target : Name) : Expr → Array Expr
  | expression@(.app function argument) =>
      let here := if expression.getAppFn.isConstOf target then #[expression]
        else #[]
      here ++ directApplications target function ++
        directApplications target argument
  | .lam _ type body _ | .forallE _ type body _ =>
      directApplications target type ++ directApplications target body
  | .letE _ type value body _ =>
      directApplications target type ++ directApplications target value ++
        directApplications target body
  | .mdata _ body | .proj _ _ body => directApplications target body
  | _ => #[]

private def clippedRepr (expression : Expr) : String :=
  let rendered := toString (repr expression)
  if rendered.length ≤ 600 then rendered
  else (rendered.take 600).toString ++ "…"

elab "#trace_axiom " targetSyntax:ident " in " declarationSyntax:ident : command => do
  let environment ← getEnv
  let target := targetSyntax.getId
  let declaration := declarationSyntax.getId
  unless environment.constants.contains declaration do
    throwError m!"unknown declaration {declaration}"
  unless environment.constants.contains target do
    throwError m!"unknown target axiom or declaration {target}"
  let closure ← Lean.collectAxioms declaration
  let closureNames := closure.qsort Name.lt
  if !closure.contains target then
    logInfo m!"{declaration} closure axioms: {namesText closureNames}\n\
      does not depend on {target}"
  else
    let immediate ← targetBearingDependencies environment target declaration
    let path ← shortestDependencyPath environment target declaration
    let pathDescription := match path with
      | some names => pathText names
      | none => "<no path found despite closure result>"
    logInfo m!"{declaration} closure axioms: {namesText closureNames}\n\
      immediate dependencies carrying {target}: {namesText immediate}\n\
      shortest path: {pathDescription}"

/-- Show the direct applications of one declaration inside another proof
term.  This complements the closure path when the first problematic edge is
introduced directly by a tactic-generated proof term. -/
elab "#trace_use " targetSyntax:ident " in " declarationSyntax:ident : command => do
  let environment ← getEnv
  let target := targetSyntax.getId
  let declaration := declarationSyntax.getId
  let some info := environment.constants.find? declaration
    | throwError m!"unknown declaration {declaration}"
  let some value := info.value? (allowOpaque := true)
    | throwError m!"declaration {declaration} has no inspectable value"
  let applications := directApplications target value
  if applications.isEmpty then
    logInfo m!"{declaration} contains no direct application of {target}"
  else
    for applicationIndex in [:applications.size] do
      let application := applications[applicationIndex]!
      let arguments := application.getAppArgs
      logInfo m!"{declaration} directly applies {target} \
        at occurrence {applicationIndex + 1} with {arguments.size} arguments"
      for argumentIndex in [:arguments.size] do
        logInfo m!"  argument {argumentIndex + 1}: \
          {clippedRepr arguments[argumentIndex]!}"

end AxiomTrace
