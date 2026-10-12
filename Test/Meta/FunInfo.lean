module

-- The regression needs the private dependency collector's original body.
meta import all Lean.Meta.FunInfo
meta import Lean.Elab.Command

/-!
# Dependency collection on shared expressions

The original tree traversal provides a reference on small expressions. A deeply
shared application checks that collection follows the expression DAG without
changing its sorted parameter dependencies.
-/

namespace Test.Meta.FunInfo

open Lean

meta section

/-- The original tree traversal retained as a small-input reference. -/
private def referenceDeps (fvars : Array Expr) (e : Expr) : Array Nat :=
  let rec visit (e : Expr) (deps : Array Nat) : Array Nat :=
    if !e.hasFVar then deps else
      match e with
      | .app f a => visit a (visit f deps)
      | .forallE _ d b _ => visit b (visit d deps)
      | .lam _ d b _ => visit b (visit d deps)
      | .letE _ t v b _ => visit b (visit v (visit t deps))
      | .proj _ _ e => visit e deps
      | .mdata _ e => visit e deps
      | .fvar .. =>
        match fvars.idxOf? e with
        | none => deps
        | some i => if deps.contains i then deps else deps.push i
      | _ => deps
  (visit e #[]).qsort (· < ·)

/-- Compare collected dependencies with the original traversal and an explicit result. -/
private def checkDeps (fvars : Array Expr) (e : Expr) (expected : Array Nat) :
    Elab.Command.CommandElabM Unit := do
  let actual := Lean.Meta.collectDeps fvars e
  unless actual == expected && actual == referenceDeps fvars e do
    throwError "incorrect parameter dependencies: {actual}, expected {expected}"

run_cmd do
  let a := mkFVar ⟨`a⟩
  let b := mkFVar ⟨`b⟩
  let c := mkFVar ⟨`c⟩
  let absent := mkFVar ⟨`absent⟩
  let fvars := #[c, a, b]
  let closed := mkConst ``Nat
  checkDeps fvars closed #[]
  checkDeps fvars absent #[]
  checkDeps fvars (.app b a) #[1, 2]
  checkDeps fvars (.forallE `x c (.app a (.bvar 0)) .default) #[0, 1]
  checkDeps fvars (.lam `x b (.app c (.bvar 0)) .default) #[0, 2]
  checkDeps fvars (.letE `x a b (.app c (.bvar 0)) false) #[0, 1, 2]
  checkDeps fvars (.proj ``Prod 0 (.mdata {} (.app a b))) #[1, 2]
  let small := (List.range 7).foldl (fun e _ => mkApp2 closed e e) (.app b a)
  checkDeps fvars small #[1, 2]
  let shared := (List.range 30).foldl (fun e _ => mkApp2 closed e e) (.app b a)
  unless Lean.Meta.collectDeps fvars shared == #[1, 2] do
    throwError "incorrect dependencies on the deeply shared expression"

end

end Test.Meta.FunInfo
