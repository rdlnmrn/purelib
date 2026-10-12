module

/-
Copyright (c) 2020 Sebastian Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich, Dany Fabian

Record syntax generation follows the pinned Lean JSON deriving implementation.
Generated terms retain the owned finite JSON carrier and codecs instead.
-/

-- Public handlers retain the original elaborator headers and instance builders.
public meta import Lean.Elab.Deriving.Basic
public meta import Lean.Elab.Deriving.Util
public import Purelib.Data.Json.Codec
import Purelib.Data.String.Basic

/-!
# Finite JSON record codec generation

The two deriving handlers generate the original flattened record-field wire
format, optional question-mark fields and field-qualified failure diagnostics.
Record constructors retain every original field and default definition.
-/

namespace Purelib.Elab.Deriving.Json

open Lean Elab Command Meta
open Lean.Elab.Deriving
open Lean.Parser.Term
open Purelib.Data.Json

set_option backward.match.sparseCases false in
/-- Read a record field's original wire key and optional-field marker.

All trailing question marks are omitted from the wire key, matching the original
record codec. The marker selects omission only through the optional-field codec. -/
private meta def fieldKey (field : Name) : CoreM (Bool × Term) := do
  let .str .anonymous text := field | throwError "invalid JSON record field name"
  let key := text.dropEndWhile (· == '?') |>.copy
  return (text != key, Syntax.mkStrLit key)

/-- Assemble the original finite record encoding from its flattened fields.

Each field is read once from the retained record. Optional marked fields omit
none; all other fields encode under their original key before object normalization. -/
private meta def encodeBody (header : Header) (inductiveName : Name) : TermElabM Term := do
  let fields := getStructureFieldsFlattened (← getEnv) inductiveName (includeSubobjectFields := false)
  let entries ← fields.mapM fun field => do
    let (optional, key) ← fieldKey field
    let target := mkIdent header.targetNames[0]!
    if optional then
      ``(Purelib.Data.Json.opt $key $target.$(mkIdent field))
    else
      ``([($key, Purelib.Data.Json.toJson ($target).$(mkIdent field))])
  ``(Purelib.Data.Json.mkObj (List.flatten [$entries,*]))

/-- Assemble the original ordered record decoder and field-qualified failures.

Missing fields use the retained null convention, including missing optional
values. Each original field decoder runs once in declaration order and the first
failure retains the original fully qualified record and field label. Prefixes
are generated as string literals; emitted diagnostics use the owned append. -/
private meta def decodeBody (inductiveName : Name) : TermElabM Term := do
  let fields := getStructureFieldsFlattened (← getEnv) inductiveName (includeSubobjectFields := false)
  let getters ← fields.mapM fun field => do
    let (_, key) ← fieldKey field
    let getter ← `(Purelib.Data.Json.getObjValAs? json _ $key)
    let errorPrefix := toString inductiveName ++ "." ++ toString field ++ ": "
    `(doElem| Except.mapError (fun error => Purelib.Data.String.append $(quote errorPrefix) error) <| $getter)
  let names := fields.map mkIdent
  `(do
    $[let $names:ident ← $getters]*
    return { $[$names:ident := $(id names)],* })

/-- Generate the retained record encoder and its original named instance.

Original implicit parameters and local codec assumptions come from the compiler's
header builder. The executable helper is exposed so downstream record literals
can reduce their exact finite encoding. -/
private meta def encoderCommands (name : Name) : TermElabM (Array Command) := do
  let context ← mkContext ``Purelib.Data.Json.ToJson "toJson" name
  let header ← mkHeader ``Purelib.Data.Json.ToJson 1 context.typeInfos[0]!
  let body ← encodeBody header name
  let helper := mkIdent context.auxFunNames[0]!
  let binders := header.binders
  let command ← if isPrivateName name then
    `(def $helper:ident $binders:bracketedBinder* : Purelib.Data.Json := $body:term)
  else
    `(@[expose] def $helper:ident $binders:bracketedBinder* : Purelib.Data.Json := $body:term)
  return #[command] ++ (← mkInstanceCmds context ``Purelib.Data.Json.ToJson #[name])

/-- Generate the retained ordered record decoder and its original named instance.

Original implicit parameters and local codec assumptions come from the compiler's
header builder. The exposed executable helper preserves direct reduction of a
literal JSON record and its exact first-error result. -/
private meta def decoderCommands (name : Name) : TermElabM (Array Command) := do
  let context ← mkContext ``Purelib.Data.Json.FromJson "fromJson" name
  let base ← mkHeader ``Purelib.Data.Json.FromJson 0 context.typeInfos[0]!
  let jsonBinder ← `(bracketedBinderF|(json : Purelib.Data.Json))
  let binders := base.binders.push jsonBinder
  let body ← decodeBody name
  let helper := mkIdent context.auxFunNames[0]!
  let target := base.targetType
  let command ← if isPrivateName name then
    `(def $helper:ident $binders:bracketedBinder* : Except String $target := $body:term)
  else
    `(@[expose] def $helper:ident $binders:bracketedBinder* : Except String $target := $body:term)
  return #[command] ++ (← mkInstanceCmds context ``Purelib.Data.Json.FromJson #[name])

/-- Derive finite JSON encoders for retained structure declarations.

The handler keeps original flattened fields and typed codec parameters. Other
inductive declarations are declined rather than given an incompatible wire format. -/
public meta def deriveToJson (names : Array Name) : CommandElabM Bool := do
  unless names.size > 0 && names.all (isStructure (← getEnv)) do return false
  for name in names do
    let commands ← liftTermElabM (encoderCommands name)
    commands.forM elabCommand
  return true

/-- Derive finite JSON decoders for retained structure declarations.

The handler keeps original flattened fields, typed codec parameters and first-error
labels. Other inductive declarations are declined without changing their codec API. -/
public meta def deriveFromJson (names : Array Name) : CommandElabM Bool := do
  unless names.size > 0 && names.all (isStructure (← getEnv)) do return false
  for name in names do
    let commands ← liftTermElabM (decoderCommands name)
    commands.forM elabCommand
  return true

meta initialize
  registerDerivingHandler ``Purelib.Data.Json.ToJson deriveToJson
  registerDerivingHandler ``Purelib.Data.Json.FromJson deriveFromJson

end Purelib.Elab.Deriving.Json
