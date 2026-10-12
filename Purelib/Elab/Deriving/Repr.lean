module

public meta import Lean.Elab.Deriving.Repr
public meta import Lean.Elab.Deriving.Util
public meta import Lean.Elab.Term.TermElabM
public meta import Lean.Elab.Command

/-!
# Exposed derived `Repr` methods

Lean 4.32.2's `Repr` deriving handler marks its generated methods
`@[no_expose]`, even when the inductive and instance are public and exposed.
This command uses the same name, binder, body, and instance builders as that
handler, changing only the method's exposure attribute.
-/

@[expose] public section

namespace Purelib.Elab.Deriving.Repr

open Lean Lean.Elab Lean.Elab.Command Lean.Elab.Deriving Lean.Parser.Term

/-- The pinned `Repr.mkAuxFunction`, with its `no_expose` attribute replaced. -/
meta def mkExposedAuxFunction (ctx : Deriving.Context) (i : Nat) : TermElabM Command := do
  let auxFunName := ctx.auxFunNames[i]!
  let indVal := ctx.typeInfos[i]!
  let header ← Repr.mkReprHeader indVal
  let mut body ← Repr.mkBody header indVal auxFunName
  if ctx.usePartial then
    let letDecls ← mkLocalInstanceLetDecls ctx `Repr header.argNames
    body ← mkLet letDecls body
  let binders := header.binders
  if ctx.usePartial then
    `(@[expose] partial def $(mkIdent auxFunName):ident $binders:bracketedBinder* : Format := $body:term)
  else
    `(@[expose] def $(mkIdent auxFunName):ident $binders:bracketedBinder* : Format := $body:term)

/-- Syntax for deriving the standard Repr instance with exposed generated methods. -/
syntax (name := deriveExposedRepr) "derive_exposed_repr " ident : command

/-- Derive the standard `Repr` instance while exposing its generated method. -/
@[command_elab Purelib.Elab.Deriving.Repr.deriveExposedRepr]
meta def elabDeriveExposedRepr : CommandElab := fun stx => do
  let declName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo stx[1]
  unless (← isInductive declName) do
    throwError "`derive_exposed_repr` expects an inductive type"
  let indVal ← getConstInfoInduct declName
  for typeName in indVal.all do
    let typeInfo ← getConstInfoInduct typeName
    if typeInfo.ctors.any isPrivateName then
      throwError "`derive_exposed_repr` cannot expose a type with private constructors"
  let cmds ← liftTermElabM do
    let ctx ← mkContext ``Repr "repr" declName
    let mut auxDefs := #[]
    for i in [:ctx.typeInfos.size] do
      auxDefs := auxDefs.push (← mkExposedAuxFunction ctx i)
    let auxBlock ← `(mutual
      $auxDefs:command*
    end)
    return #[auxBlock] ++ (← mkInstanceCmds ctx `Repr #[declName])
  cmds.forM elabCommand

end Purelib.Elab.Deriving.Repr

end
