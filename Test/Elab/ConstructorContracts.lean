module
meta import Purelib.Elab.ConstructiveInjectivity

namespace Test.Elab.ConstructorContracts

set_option genInjectivity false in
/-- A generic pair. -/
public structure Pair (α : Type u) (β : Type v) where
  /-- The first original typed field. -/ first : α
  /-- The second original typed field. -/ second : β

constructive_injectivity Pair

#check Pair.mk.inj
#check Pair.mk.injEq

set_option genInjectivity false in
/-- A value retaining its own type. -/
public inductive Typed : Type (u + 1) where
  /-- Retain the carrier and its original value. -/
  | mk (α : Type u) (value : α)

constructive_injectivity Typed

#check Typed.mk.inj
#check Typed.mk.injEq

set_option genInjectivity false in
/-- A positive natural coordinate. -/
public structure Positive where
  /-- The positive coordinate. -/ value : Nat
  /-- The original positivity certificate. -/ positive : 0 < value

constructive_injectivity Positive

#check Positive.mk.inj
#check Positive.mk.injEq

set_option genInjectivity false in
/-- A list retaining its length. -/
public inductive Indexed (α : Type u) : Nat → Type u where
  /-- The empty indexed constructor. -/
  | nil : Indexed α 0
  /-- The head and original indexed recursive tail. -/
  | cons {size : Nat} (head : α) (tail : Indexed α size) : Indexed α (size + 1)

constructive_injectivity Indexed

#check Indexed.cons.inj
#check Indexed.cons.injEq

set_option genInjectivity false in
/-- A private carrier whose certificates keep its mathematical names. -/
structure Hidden where
  /-- The retained natural field. -/ value : Nat

constructive_injectivity Hidden

#check Hidden.mk.inj
#check Hidden.mk.injEq

set_option genInjectivity false in
/-- A constructor whose only field is evidence. -/
public structure ProofOnly : Type where
  /-- The retained proposition witness. -/ evidence : True

constructive_injectivity ProofOnly

#check_failure ProofOnly.mk.inj
#check_failure ProofOnly.mk.injEq

set_option genInjectivity false in
/-- A constructor with original instance and strict implicit data binders. -/
public inductive DictionaryTagged (α : Type u) where
  /-- Keep the original field dictionary, strict index and scalar entry. -/
  | mk [dictionary : Inhabited α] ⦃index : Nat⦄ (value : α)

constructive_injectivity DictionaryTagged

#check DictionaryTagged.mk.inj
#check DictionaryTagged.mk.injEq

/-- Original instance and strict implicit data fields retain their complete ordered relations. -/
private theorem dictionaryCertificate {α : Type u}
    [dictionary : Inhabited α] [otherDictionary : Inhabited α]
    ⦃index otherIndex : Nat⦄ (first second : α) :
    @DictionaryTagged.mk α dictionary index first = @DictionaryTagged.mk α otherDictionary otherIndex second ↔
      dictionary = otherDictionary ∧ index = otherIndex ∧ first = second :=
  @DictionaryTagged.mk.injEq α dictionary index first otherDictionary otherIndex second

namespace Neighbor

set_option genInjectivity false in
/-- Another generic pair with the same basename. -/
public structure Pair (α : Type u) where
  /-- The retained typed value. -/ value : α

constructive_injectivity Pair

#check Pair.mk.inj
#check Pair.mk.injEq
#check Test.Elab.ConstructorContracts.Pair.mk.injEq

end Neighbor
end Test.Elab.ConstructorContracts
