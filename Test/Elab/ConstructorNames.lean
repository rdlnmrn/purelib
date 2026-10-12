module
meta import Purelib.Elab.ConstructiveInjectivity

public section
namespace Test.Elab.ConstructorNames
set_option genInjectivity false in
/-- Data fields retain the original names used by proof-local binders. -/
structure Names where
  /-- The original x data field. -/ x : Nat
  /-- The original equalities data field. -/ equalities : Nat
  /-- The original relation data field. -/ relation : Nat
constructive_injectivity Names

/-- Named data lookup retains the first accessible original x binder. -/
theorem namedData (h : Names.mk 1 2 3 = Names.mk 1 2 3) :
    1 = 1 ∧ 2 = 2 ∧ 3 = 3 :=
  Names.mk.inj (x := 1) h

set_option genInjectivity false in
/-- A parameter retains the original x argument name. -/
structure Parameter (x : Nat) where
  /-- The scalar entry. -/ value : Nat
constructive_injectivity Parameter
/-- Named x lookup selects the original parameter before the equality proof. -/
theorem namedParameter (h : Parameter.mk (x := 3) 1 = Parameter.mk (x := 3) 1) : 1 = 1 :=
  Parameter.mk.inj (x := 3) h

set_option genInjectivity false in
/-- A proof field retains its original x argument name. -/
structure ProofField where
  /-- The original proof data. -/ x : True
  /-- The scalar entry. -/ value : Nat
constructive_injectivity ProofField
/-- Named x lookup selects the original proof field before the equality proof. -/
theorem namedProofField (h : ProofField.mk True.intro 1 = ProofField.mk True.intro 1) : 1 = 1 :=
  ProofField.mk.inj (x := True.intro) h

set_option genInjectivity false in
/-- A scalar retains a role word as its ordinary mathematical field name. -/
structure Shared where
  /-- The scalar entry named shared. -/ shared : Nat
constructive_injectivity Shared
/-- Non-reserved role words preserve ordinary first-matching named arguments. -/
theorem namedShared (h : Shared.mk 3 = Shared.mk 3) : 3 = 3 :=
  Shared.mk.inj (shared := 3) h
/-- Schema modifier words remain ordinary mathematical binder names. -/
private def declaring (omitting arguments universes proof_binder eq heq proof : Nat) : Nat :=
  omitting + arguments + universes + proof_binder + eq + heq + proof

set_option genInjectivity false in
/-- A local owner deliberately shares the primitive Boolean type spelling. -/
structure Bool where
  /-- The retained signal. -/ signal : Nat
constructive_injectivity Bool

/-- The local Boolean-named carrier retains its original signal argument. -/
theorem namedSignal (h : Bool.mk 3 = Bool.mk 3) : 3 = 3 :=
  Bool.mk.inj (signal := 3) h

set_option genInjectivity false in
/-- Anonymous dictionaries retain two original local instances and a named data entry. -/
structure Dictionary (α : Type) [DecidableEq α] [DecidableEq _root_.Bool] where
  /-- The accessible data field named inst. -/ inst : Nat
  /-- The typed scalar entry. -/ value : α
constructive_injectivity Dictionary
/-- Anonymous instance aliases preserve the original accessible inst data argument. -/
theorem namedInstanceField
    (h : Dictionary.mk (α := _root_.Bool) 3 true = Dictionary.mk (α := _root_.Bool) 3 true) :
    3 = 3 ∧ true = true :=
  Dictionary.mk.inj (inst := 3) h
namespace Unrelated
set_option genInjectivity false in
/-- A nominal owner declared at its original root route inside another namespace. -/
public structure _root_.Test.Elab.ConstructorNames.Rooted where
  /-- The retained scalar. -/ value : Nat
constructive_injectivity Test.Elab.ConstructorNames.Rooted
/-- A qualified constructor request retains the original nominal theorem route. -/
theorem rootedNamed (h : Rooted.mk 3 = Rooted.mk 3) : 3 = 3 :=
  Rooted.mk.inj (x := h)
end Unrelated
end Test.Elab.ConstructorNames
end
