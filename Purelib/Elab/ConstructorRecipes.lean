module

public meta import Lean.Parser.Command
meta import Lean.Elab.Macro
meta import Lean.Parser.Tactic
meta import Init.Tactics

open Lean

set_option backward.match.sparseCases false

namespace Purelib.Elab.ConstructorRecipes

/-- The mathematical role of one original constructor argument. -/
declare_syntax_cat ctorRole (behavior := symbol)
/-- A constructor argument shared by both sides of its equality. -/
syntax (name := sharedRole) &"shared" : ctorRole
/-- A constructor argument compared by ordinary equality. -/
syntax (name := equalityRole) &"eq" : ctorRole
/-- A constructor argument compared by heterogeneous equality. -/
syntax (name := heterogeneousRole) &"heq" : ctorRole
/-- A proof argument omitted from the retained field relations. -/
syntax (name := proofRole) &"proof" : ctorRole

/-- An original binder, its optional right partner and its retained relation. -/
declare_syntax_cat ctorArgument
/-- An explicitly supplied constructor argument and its retained relation. -/
syntax (name := explicitArgument) "(" ident (ident)? " : " ctorRole (" :: " term (" => " term)?)? ")" : ctorArgument
/-- An implicit constructor argument and its retained relation. -/
syntax (name := implicitArgument) "{" ident (ident)? " : " ctorRole (" :: " term (" => " term)?)? "}" : ctorArgument
/-- A strictly implicit constructor argument and its retained relation. -/
syntax (name := strictArgument) "⦃" ident (ident)? " : " ctorRole (" :: " term (" => " term)?)? "⦄" : ctorArgument
/-- An instance constructor argument and its retained relation. -/
syntax (name := instanceArgument) "[" ident (ident)? " : " ctorRole (" :: " term (" => " term)?)? "]" : ctorArgument

/-- Recognize the empty optional syntax node without compiler match certificates. -/
private meta def emptyOptional : Syntax → Bool
  | .node _ kind arguments => kind == nullKind && arguments.size == 0
  | .missing => true
  | _ => false

/-- Retain a supplied identifier's source spelling and replace only its mathematical name. -/
private meta def renameIdentifier (source : Ident) (name : Name) : Ident :=
  match source.raw with
  | .ident information spelling _ _ => ⟨.ident information spelling name []⟩
  | _ => source

/-- Construct a local proof binder from its fixed source spelling and mathematical name. -/
private meta def fixedIdentifier (name : Name) (spelling : String) : Ident :=
  ⟨.ident .none spelling.toRawSubstring name []⟩

/-- Give a proof-local identifier a fresh scope while retaining its user binder name. -/
private meta def proofIdentifier (name : Name) (spelling : String) : MacroM Ident :=
  withFreshMacroScope do
    let scopedName ← Macro.addMacroScope name
    return fixedIdentifier scopedName spelling

/-- Construct one binder of the original requested syntactic mode. -/
private meta def binder (argument : Syntax) (name : Ident) (domain : Term)
    (allImplicit : Bool) : MacroM (TSyntax ``Lean.Parser.Term.bracketedBinder) := do
  if allImplicit || argument.isOfKind ``implicitArgument then
    `(bracketedBinder| {$name : $domain})
  else if argument.isOfKind ``strictArgument then
    `(bracketedBinder| ⦃$name : $domain⦄)
  else if argument.isOfKind ``instanceArgument then
    `(bracketedBinder| [$name : $domain])
  else
    `(bracketedBinder| ($name : $domain))

/-- Assemble the right-associated conjunction and its reflexive constructor proof. -/
private meta def conjunction (relations : List (Term × Term)) : MacroM (Term × Term) := do
  match relations with
  | [] => Macro.throwError "constructor recipe has no field relations"
  | [(relation, reflexivity)] => return (relation, reflexivity)
  | (relation, reflexivity) :: remaining =>
    let (tail, proofTerm) ← conjunction remaining
    return (← `($relation ∧ $tail), ← `(⟨$reflexivity, $proofTerm⟩))

/-- Eliminate the retained ordered field identities and finish with reflexivity. -/
private meta def elimination (relations : List Term) (equalities : Ident) :
    MacroM (TSyntax ``Lean.Parser.Tactic.tacticSeq) := do
  match relations with
  | [] => Macro.throwError "constructor recipe has no field relations"
  | [_] => `(tacticSeq| cases $equalities:term; rfl)
  | _ :: remaining =>
    let relation ← proofIdentifier `relation "relation"
    let tail ← elimination remaining equalities
    `(tacticSeq| cases $equalities:term with
      | intro $relation $equalities =>
        cases $relation:term
        ($tail:tacticSeq))

public section

/-- Generate constructor implications and field equivalences from their exact recipe.

The recipe retains every parameter and field in constructor order, original
binder modes, shared indices, right partners, ordered Eq/HEq relations, proof
fields, visibility and universe labels. Macro expansion performs no environment
lookup and creates ordinary kernel-checked constructor proofs. -/
syntax (name := constructorCertificates)
  "constructor_certificates" ("public")? ident
  &"universes" "[" ident,* "]" (&"omitting" "[" ident* "]")? (&"proof_binder" ident)? &"arguments" ctorArgument+ :
    command

/-- Expand a complete constructor recipe into its original named certificates. -/
@[macro constructorCertificates]
meta def expandConstructorCertificates : Macro := fun stx => do
  let isPublic := !emptyOptional (stx.getArg 1)
  let constructor : Ident := ⟨stx.getArg 2⟩
  let levels : Syntax.TSepArray `level "," := ⟨(stx.getArg 5).getArgs⟩
  let omittedScope := stx.getArg 7
  let omittedNames : Array Ident := if emptyOptional omittedScope then #[] else
    ((omittedScope.getArg 2).getArgs.toList.foldl (fun names raw => names.push ⟨raw⟩) #[])
  let recipeArguments := (stx.getArg 10).getArgs.toList
  let (leftArguments, rightArguments, implicationBinders, equivalenceLeft,
      equivalenceRight, implicationRight, scalarRelations) ← recipeArguments.foldlM
    (fun (leftArguments, rightArguments, implicationBinders, equivalenceLeft,
        equivalenceRight, implicationRight, scalarRelations) argument => do
      let left : Ident := ⟨argument.getArg 1⟩
      let role := argument.getArg 4
      let rightOption := argument.getArg 2
      let domain : Term ← if emptyOptional (argument.getArg 5) then `(_) else
        pure ⟨(argument.getArg 5).getArg 1⟩
      let rightDomain : Term ← if emptyOptional (argument.getArg 5) || emptyOptional ((argument.getArg 5).getArg 2) then
        `(_) else
        pure ⟨((argument.getArg 5).getArg 2).getArg 1⟩
      let isShared := role.isOfKind ``sharedRole
      let right : Ident := if isShared then left else ⟨rightOption.getArg 0⟩
      if isShared && !emptyOptional rightOption then
        Macro.throwError "a shared argument must not have a right partner"
      if !isShared && emptyOptional rightOption then
        Macro.throwError "each unshared argument needs its explicit right partner"
      let leftArguments := leftArguments.push (← `(@$left))
      let rightArguments := rightArguments.push (← `(@$right))
      let implicationBinders := implicationBinders.push (← binder argument left domain true)
      let equivalenceLeft := equivalenceLeft.push (← binder argument left domain false)
      let equivalenceRight ← if isShared then pure equivalenceRight else
        pure (equivalenceRight.push (← `(bracketedBinder| ($right : $rightDomain))))
      let implicationRight ← if isShared then pure implicationRight else
        pure (implicationRight.push (← `(bracketedBinder| {$right : $rightDomain})))
      let scalarRelations ← if role.isOfKind ``equalityRole then
        pure (scalarRelations.push (← `((@$left) = (@$right)), ← `(rfl)))
        else if role.isOfKind ``heterogeneousRole then
          pure (scalarRelations.push (← `(HEq (@$left) (@$right)), ← `(HEq.rfl)))
        else pure scalarRelations
      return (leftArguments, rightArguments, implicationBinders, equivalenceLeft,
        equivalenceRight, implicationRight, scalarRelations))
    ((#[] : Array Term), (#[] : Array Term), #[], #[], #[], #[], (#[] : Array (Term × Term)))
  if scalarRelations.isEmpty then return mkNullNode #[]
  let lhs ← `(@$constructor.{$levels,*} $leftArguments*)
  let rhs ← `(@$constructor.{$levels,*} $rightArguments*)
  let equality ← `($lhs = $rhs)
  let (relationClaim, reflexivity) ← conjunction scalarRelations.toList
  let forwardName := renameIdentifier constructor (constructor.getId ++ `inj)
  let equivalenceName := renameIdentifier constructor (constructor.getId ++ `injEq)
  let selectedProof := stx.getArg 8
  let forwardProof : Ident := if emptyOptional selectedProof then
    fixedIdentifier `x "x" else ⟨selectedProof.getArg 1⟩
  let x ← proofIdentifier `x "x"
  let equalities ← proofIdentifier `equalities "equalities"
  let reverse ← elimination (scalarRelations.toList.map Prod.fst) equalities
  let forwardDecl ← `(declId| $forwardName)
  let equivalenceDecl ← `(declId| $equivalenceName)
  let forwardBinders := implicationBinders ++ implicationRight
  let equivalenceBinders := equivalenceLeft ++ equivalenceRight
  let forward ← `(command|
    /-- Constructor equality identifies its ordered nonproof fields. -/
    theorem $forwardDecl:declId $forwardBinders:bracketedBinder*
        ($forwardProof : $equality) : $relationClaim := by
      cases $forwardProof:term
      exact $reflexivity)
  let equivalence ← `(command|
    /-- Constructor equality is equivalent to its ordered nonproof field identities. -/
    theorem $equivalenceDecl:declId $equivalenceBinders:bracketedBinder* :
        $equality ↔ $relationClaim := by
      constructor
      · intro $x:term
        cases $x:term
        exact $reflexivity
      · intro $equalities:term
        ($reverse:tacticSeq))
  let visibility ← if isPublic then `(visibility| public) else `(visibility| private)
  let forward := forward.raw.setArg 0 ((forward.raw.getArg 0).setArg 2
    (mkNullNode #[visibility.raw]))
  let equivalence := equivalence.raw.setArg 0 ((equivalence.raw.getArg 0).setArg 2
    (mkNullNode #[visibility.raw]))
  let expansion : TSyntax `command := ⟨mkNullNode #[forward, equivalence]⟩
  if omittedNames.isEmpty then return expansion.raw
  else return (← `(command| omit $omittedNames:ident* in $expansion:command)).raw

end
end Purelib.Elab.ConstructorRecipes
