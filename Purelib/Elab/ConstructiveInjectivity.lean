module

/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura

The constructor argument and proof construction below follows the pinned
Lean.Meta.Injective implementation, replacing proposition equality with Iff
and omitting the simplifier's proposition-equality registration.
-/

-- Generated theorem splitters retain the original expression datatype in the normal phase.
import Lean.Expr
import Purelib.Data.Nat.Subtraction
public meta import Lean.Elab.Command
-- The public command retains the original constructor-name and optParam builders.
public meta import Lean.Meta.Injective
meta import Lean.Meta.Tactic.Injection
meta import Lean.Meta.Tactic.Assumption
-- Generated reverse proofs retain the compiler's reflexivity stage.
public meta import Lean.Meta.Tactic.Refl
meta import Lean.Meta.Tactic.Subst
-- Shared correctness-bearing indices use this original public compiler operation.
public meta import Lean.Meta.SameCtorUtils
meta import Lean.DocString.Extension
meta import Lean.Elab.DeclarationRange

/-!
# Constructive constructor injectivity certificates

`constructive_injectivity TypeName` generates the constructor's original
`.inj` implication and `.injEq` logical equivalence names. Each owning
inductive declaration first scopes `genInjectivity=false`; the command restores
the full pair without proposition equality or simplifier registration.

The original constructor parameters, dependent fields and correctness-bearing
indices determine the theorem types. Kernel-checked no-confusion and scalar
substitution prove the certificates; the command does not change the datatype,
its constructors, computational fields or executable operations.
-/

namespace Purelib.Elab.ConstructiveInjectivity

open Lean Elab Command Meta

/-- Assemble a right-associated conjunction of the displayed field relations.

An empty array supplies no constructor injectivity API, matching the original
compiler's treatment of constructors without relevant nonproof fields. -/
private meta def conjunction? (relations : Array Expr) : Option Expr := Id.run do
  if relations.isEmpty then
    return none
  let mut result := relations.back!
  for relation in relations.reverse[1...*] do
    result := mkApp2 (mkConst ``And) relation result
  return some result

/-- Compare corresponding original nonproof fields by equality or heterogeneous equality.

The constructor's dependent field types select Eq or HEq. Shared indices and
proof fields require no additional field relation, matching the original
constructor certificate's mathematical claim. -/
private meta def fieldRelations (left right : Array Expr) : MetaM (Array Expr) := do
  let mut relations := #[]
  for first in left, second in right do
    unless (← isProp (← inferType first)) || first == second do
      relations := relations.push (← mkEqHEq first second)
  return relations

/-- Choose an accessible binder name without shadowing an original constructor argument.

Primed variants retain the conventional right-hand field and equality-proof
names, including when anonymous instance arguments share a field's spelling. -/
private meta partial def unusedBinderName (context : LocalContext) (suggestion : Name) : Name :=
  if context.usesUserName suggestion then
    unusedBinderName context (suggestion.appendAfter "'")
  else
    suggestion

/-- Give anonymous constructor dictionaries accessible names after reserving authored arguments.

Only hygienic user labels change; the original free-variable identities, types,
instance registrations and binder modes are retained. -/
private meta def withAccessibleArguments (arguments : Array Expr) (action : MetaM α) : MetaM α := do
  let mut context ← getLCtx
  for argument in arguments do
    let declaration := context.get! argument.fvarId!
    if declaration.userName.hasMacroScopes then
      let name := unusedBinderName context declaration.userName.eraseMacroScopes
      context := context.setUserName declaration.fvarId name
  withLCtx' context action

open Purelib.Data.Nat in
set_option backward.match.sparseCases false in
/-- Construct an original constructor's implication or equivalence certificate type.

Fields occurring in the constructor's result type or the types of its indices
are shared between the two applications. Remaining dependent fields are
introduced in their original order, with the compiler's original binder choices.
Ordinary case splitting retains these expression cases without sparse bitmask
discriminator certificates. -/
private meta def certificateType? (constructor : ConstructorVal) (equivalence : Bool) :
    MetaM (Option Expr) := do
  let levels := constructor.levelParams.map mkLevelParam
  let type ← elimOptParam constructor.type
  forallBoundedTelescope type constructor.numParams fun parameters type =>
    forallTelescope type fun left resultType => withAccessibleArguments (parameters ++ left) do
      let finish (right newRight : Array Expr) : MetaM (Option Expr) := do
        let constructorExpression := mkAppN (mkConst constructor.name levels) parameters
        let equality ← mkEq (mkAppN constructorExpression left) (mkAppN constructorExpression right)
        let some relations := conjunction? (← fieldRelations left right) | return none
        let context ← getLCtx
        let result := if equivalence then mkIff equality relations else
          mkForall (unusedBinderName context `x) .default equality (relations.liftLooseBVars 0 1)
        return some (← mkForallFVars parameters (← mkForallFVars left (← mkForallFVars newRight result)))
      let rec introduceRight (index : Nat) (remaining : Expr)
          (right newRight : Array Expr) : MetaM (Option Expr) := do
        if bound : index < left.size then
          let .forallE name domain body _ ← whnf remaining
            | throwError "unexpected constructor type for `{constructor.name}`"
          let field := left[index]'bound
          if occursOrInType (← getLCtx) field resultType then
            introduceRight (index + 1) (body.instantiate1 field) (right.push field) newRight
          else
            let name := unusedBinderName (← getLCtx) name.eraseMacroScopes
            withLocalDecl name (if equivalence then .default else .implicit) domain fun other =>
              introduceRight (index + 1) (body.instantiate1 other)
                (right.push other) (newRight.push other)
        else
          finish right newRight
      termination_by left.size - index
      decreasing_by
        all_goals
          exact (Nat.sub_succ left.size index).symm ▸
            Nat.pred_lt (Nat.ne_of_gt
              (Subtraction.sub_pos_of_lt bound))
      if equivalence then
        introduceRight 0 type #[] #[]
      else
        withImplicitBinderInfos (parameters ++ left) do
          introduceRight 0 type #[] #[]

/-- Prove the original forward field-identification claim by constructor no-confusion.

No-confusion retains the datatype's original indices and dependent field
relations. Splitting the scalar conjunction exposes the corresponding
identities already supplied by that constructor certificate. -/
private meta def implicationProof (constructor : Name) (type : Expr) : MetaM Expr :=
  forallTelescopeReducing type fun arguments target => do
    let goal ← mkFreshExprSyntheticOpaqueMVar target
    match ← injection goal.mvarId! arguments.back!.fvarId! with
    | .solved => throwError "unexpected solved constructor injection for `{constructor}`"
    | .subgoal reduced .. =>
      for scalarGoal in ← reduced.splitAnd do
        unless ← scalarGoal.assumptionCore do
          throwError "could not identify a constructor field for `{constructor}`"
    mkLambdaFVars arguments goal

set_option backward.match.sparseCases false in
/-- Prove both directions of the original constructor's field equivalence.

The forward direction consumes the generated implication. The reverse
substitutes the original Eq and HEq field identities in their dependency
order, then closes equality of the same constructors by kernel reflexivity.
Ordinary case splitting handles the expression and proof-goal branches without
retaining sparse bitmask discriminator certificates. -/
private meta def equivalenceProof (constructor : ConstructorVal) (type : Expr) : MetaM Expr :=
  forallTelescopeReducing type fun arguments target => do
    let goal ← mkFreshExprSyntheticOpaqueMVar target
    let [forward, reverse] ← goal.mvarId!.apply (mkConst ``Iff.intro)
      | throwError "unexpected equivalence proof goals for `{constructor.name}`"
    let implication := mkConst (mkInjectiveTheoremNameFor constructor.name)
      (constructor.levelParams.map mkLevelParam)
    forward.assign (mkAppN implication arguments)
    let mut reverse := reverse
    while true do
      let type ← reverse.getType
      let some (relation, target) := type.arrow? | break
      match_expr relation with
      | And first second =>
        let [next] ← reverse.applyN
          (mkApp3 (mkConst ``Lean.injEq_helper) first second target) 1
          | throwError "unexpected field-conjunction proof goals for `{constructor.name}`"
        reverse := next
      | _ => pure ()
      (_, reverse) ← introSubstEq reverse
    reverse.refl
    mkLambdaFVars arguments goal

set_option backward.match.sparseCases false in
/-- Add one opaque constructor certificate under its original mathematical name.

The datatype's original visibility and universe parameters are retained.
The certificate is kernel checked, documented and left without simplifier
registration, whose generated proposition equality would require propext.
Ordinary case splitting handles the optional field relation without retaining
sparse bitmask discriminator certificates. -/
private meta def emitCertificate (constructor : ConstructorVal) (equivalence : Bool)
    (origin : Syntax) : MetaM Unit := do
  let name := if equivalence then mkInjectiveEqTheoremNameFor constructor.name
    else mkInjectiveTheoremNameFor constructor.name
  if (← getEnv).contains name then
    throwError
      "constructor certificate `{name}` already exists; scope `genInjectivity=false` around its original declaration"
  let some type ← certificateType? constructor equivalence | return ()
  let proof ← if equivalence then equivalenceProof constructor type
    else implicationProof constructor.name type
  addDecl <| .thmDecl {
    name
    levelParams := constructor.levelParams
    type := ← instantiateMVars type
    value := ← instantiateMVars proof
  }
  addDeclarationRangesFromSyntax name origin origin[1]
  let summary := if equivalence then
    "Equality of the original constructor applications is equivalent to their field identities."
    else
    "Equality of the original constructor applications identifies their nonproof fields."
  addDocStringCore name (summary ++
    "\n\nThe original parameters, dependent field types and correctness-bearing indices are retained. " ++
    "Proof fields are identified by kernel proof irrelevance after the scalar field identities are substituted.")

public section

/-- Generate the original named constructor implication and constructive equivalence APIs.

Scope `genInjectivity=false` around the preceding datatype declaration so the
old proposition-equality pair is replaced atomically. The command preserves
original constructor parameters, fields, indices and declaration visibility. -/
syntax (name := constructiveInjectivity) "constructive_injectivity " ident : command

/-- Elaborate direct constructor certificates for an original inductive datatype.

Each nontrivial constructor receives its original `.inj` and `.injEq` names,
with the second asserting Iff. No executable datatype operation changes and
no simplifier-generated proposition-equality certificate is registered. -/
@[command_elab constructiveInjectivity]
meta def elabConstructiveInjectivity : CommandElab := fun stx => do
  let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo stx[1]
  let information ← getConstInfoInduct name
  if information.isUnsafe then
    throwError "`constructive_injectivity` expects a safe inductive datatype"
  liftTermElabM do
    if ← isInductivePredicate name then
      throwError "`constructive_injectivity` expects a datatype, not an inductive predicate"
    withLCtx {} {} do
      let saved ← Meta.saveState
      try
        -- Check every original name before publishing any part of the family.
        for constructorName in information.ctors do
          for certificateName in [mkInjectiveTheoremNameFor constructorName,
              mkInjectiveEqTheoremNameFor constructorName] do
            if (← getEnv).contains certificateName then
              throwError
                "constructor certificate `{certificateName}` already exists; \
                  scope `genInjectivity=false` around its original declaration"
        for constructorName in information.ctors do
          withExporting (isExporting := !isPrivateName constructorName) do
            let constructor ← getConstInfoCtor constructorName
            if constructor.numFields > 0 then
              emitCertificate constructor false stx
              emitCertificate constructor true stx
      catch exception =>
        saved.restore
        throw exception

end

end Purelib.Elab.ConstructiveInjectivity
