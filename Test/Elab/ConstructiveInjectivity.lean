module

meta import Purelib.Elab.ConstructiveInjectivity
meta import Lean.Meta.Tactic.Simp.Attr

/-!
# Constructor certificate generation regressions

The private fixtures exercise scalar fields, original finite bounds, dependent
proof fields, heterogeneous data, indexed recursion, private visibility and
proof-only records. Named kernel theorems consume the exact emitted APIs;
ordinary authoritative auditing checks their complete proof closures.

The command's original-named certificates remain selected audit roots, including
private constructor APIs. No simplifier registration or proposition-equality
fallback is used in these regressions.
-/

namespace Test.Elab.ConstructiveInjectivity

set_option genInjectivity false in
/-- Two original scalar coordinates for a simple constructor-generation check.

The two coordinates have different scalar types. Their generated implication
and equivalence retain the original constructor argument order. -/
structure Pair where
  /-- The original natural coordinate. -/ first : Nat
  /-- The original signed coordinate. -/ second : Int
  deriving DecidableEq

constructive_injectivity Pair

/-- The generated equivalence identifies both original scalar constructor fields.

The statement quantifies all four original scalar coordinates, so its proof
checks the emitted certificate type beyond a single closed constructor case. -/
private theorem pairCertificate (a : Nat) (b : Int) (c : Nat) (d : Int) :
    Pair.mk a b = Pair.mk c d ↔ a = c ∧ b = d :=
  Pair.mk.injEq a b c d

set_option genInjectivity false in
/-- A bounded original index and its explicit traversal orientation.

The original finite count remains a parameter of both constructors. The
index retains its bound, while the Boolean distinguishes the two orientations. -/
structure Signed (count : Nat) where
  /-- The original index with its retained finite bound. -/ index : Fin count
  /-- The original traversal orientation. -/ reversed : Bool
  deriving DecidableEq

constructive_injectivity Signed

/-- Shared original bounds are retained in both signed constructor applications.

The generic finite count and both original bounded indices remain in the
certificate. Their equality and the orientation equality are separate fields. -/
private theorem signedCertificate {count : Nat} (a b : Fin count) (s t : Bool) :
    Signed.mk a s = Signed.mk b t ↔ a = b ∧ s = t :=
  Signed.mk.injEq a s b t

set_option genInjectivity false in
/-- A scalar coordinate retaining its arbitrary original positivity certificate.

The natural coordinate indexes its supplied positivity proof. Distinct proof
terms at equal coordinates are identified by kernel proof irrelevance. -/
structure PositiveCoordinate where
  /-- The retained natural coordinate. -/ coordinate : Nat
  /-- The supplied positivity proof at that coordinate. -/ positive : 0 < coordinate
  deriving DecidableEq

constructive_injectivity PositiveCoordinate

/-- The generated equivalence keeps both dependent positivity proofs at their original indices.

Both supplied proofs are arbitrary, with their actual natural coordinates
as indices. The conclusion requires only equality of those scalar coordinates. -/
private theorem positiveCertificate (a b : Nat) (p : 0 < a) (q : 0 < b) :
    PositiveCoordinate.mk a p = PositiveCoordinate.mk b q ↔ a = b :=
  PositiveCoordinate.mk.injEq a p b q

set_option genInjectivity false in
/-- A retained type and value require the original heterogeneous field comparison.

The value field depends on the retained carrier type. Its constructor
certificate preserves that dependency using the original heterogeneous equality. -/
structure Typed where
  /-- The original carrier type. -/ Carrier : Type
  /-- The retained value in that same original carrier. -/ value : Carrier

constructive_injectivity Typed

/-- The generated relation keeps the dependent value comparison heterogeneous until type substitution.

Both carriers and their original values are arbitrary. The certificate first
identifies the types, then retains heterogeneous equality of those same values. -/
private theorem typedCertificate (A B : Type) (a : A) (b : B) :
    Typed.mk A a = Typed.mk B b ↔ A = B ∧ HEq a b :=
  Typed.mk.injEq A a B b

set_option genInjectivity false in
/-- An indexed constructor family retains its original correctness-bearing length.

The original constructor length indexes the recursive tail. The head and tail
remain their stored values, with no reconstruction of an alternate carrier. -/
inductive Indexed (Carrier : Type) : Nat → Type where
  /-- The original empty indexed constructor. -/
  | nil : Indexed Carrier 0
  /-- The original head and recursive tail at their retained count. -/
  | cons {count : Nat} (head : Carrier) (tail : Indexed Carrier count) :
      Indexed Carrier (count + 1)

constructive_injectivity Indexed

/-- The generated indexed-constructor equivalence retains the shared original length.

Both tails have the same original count index. The generated certificate
identifies their heads and tails without introducing a second length owner. -/
private theorem indexedCertificate {Carrier : Type} {count : Nat}
    (a b : Carrier) (s t : Indexed Carrier count) :
    Indexed.cons a s = Indexed.cons b t ↔ a = b ∧ s = t :=
  Indexed.cons.injEq a s b t

set_option genInjectivity false in
/-- A private original datatype exercises preservation of constructor visibility.

Its coordinate remains private fixture data. Constructor certificate generation
preserves that owner instead of introducing a duplicate public datatype. -/
private structure Hidden where
  /-- The retained natural coordinate. -/ coordinate : Nat

constructive_injectivity Hidden

/-- The private constructor's equivalence identifies its original scalar coordinate.

The theorem consumes the certificate under the original private constructor
name, checking that its generated API remains usable within the owning module. -/
private theorem hiddenCertificate (a b : Nat) :
    Hidden.mk a = Hidden.mk b ↔ a = b :=
  Hidden.mk.injEq a b

set_option genInjectivity false in
/-- A datatype retaining only proof data has no original nonproof field certificate.

The original proposition is a parameter and the stored evidence is proof data.
Generation omits the empty field relation, matching the compiler's original API. -/
structure ProofOnly (statement : Prop) : Type where
  /-- The retained original proposition witness. -/ evidence : statement

constructive_injectivity ProofOnly

#check_failure ProofOnly.mk.inj
#check_failure ProofOnly.mk.injEq

/-- Original proof-only constructors with arbitrary supplied evidence are equal.

The proposition parameter and both original witnesses are retained. Kernel
proof irrelevance identifies the records without a scalar injectivity API. -/
private theorem proofOnlyCertificate (statement : Prop) (first second : statement) :
    ProofOnly.mk first = ProofOnly.mk second := rfl

set_option genInjectivity false in
mutual
  /-- A finite mutual tree retaining its original right child. -/
  inductive LeftTree where
    /-- The empty left tree carries no field identities. -/
    | leaf : LeftTree
    /-- A left branch retains its original right child. -/
    | branch (child : RightTree) : LeftTree
  /-- A finite mutual tree retaining its original left child. -/
  inductive RightTree where
    /-- A right branch retains its original left child. -/
    | branch (child : LeftTree) : RightTree
end

constructive_injectivity LeftTree
constructive_injectivity RightTree

#check_failure LeftTree.leaf.inj
#check_failure LeftTree.leaf.injEq

/-- Both constructors of the mutual family retain their original child identities. -/
private theorem mutualCertificates (left otherLeft : LeftTree) (right otherRight : RightTree) :
    (LeftTree.branch right = LeftTree.branch otherRight ↔ right = otherRight) ∧
      (RightTree.branch left = RightTree.branch otherLeft ↔ left = otherLeft) :=
  ⟨LeftTree.branch.injEq right otherRight, RightTree.branch.injEq left otherLeft⟩

-- Inspect the actual simplifier registry rather than a tactic's incidental success.
run_cmd Lean.Elab.Command.liftCoreM do
  let theorems ← Lean.Meta.getSimpTheorems
  for name in #[``Pair.mk.inj, ``Pair.mk.injEq, ``Typed.mk.inj, ``Typed.mk.injEq,
      ``LeftTree.branch.injEq, ``RightTree.branch.injEq] do
    for post in #[false, true] do
      for inverse in #[false, true] do
        if theorems.isLemma (.decl name post inverse) then
          throwError "constructor certificate unexpectedly registered for simplification: {name}"
    match (← Lean.getConstInfo name) with
    | .thmInfo _ => pure ()
    | _ => throwError "constructor certificate is not an opaque theorem: {name}"

set_option genInjectivity false in
/-- A family whose later constructor deliberately already has an implication. -/
inductive AtomicCollision where
  /-- The earlier constructor must receive no partial API after rejection. -/
  | first (value : Nat)
  /-- The later constructor provides the deliberate name collision. -/
  | second (value : Nat)

/-- The deliberately existing later implication is retained by a rejected request. -/
private theorem AtomicCollision.second.inj {left right : Nat}
    (equal : AtomicCollision.second left = AtomicCollision.second right) : left = right := by
  cases equal
  rfl

/-- already exists -/
#guard_msgs (error, substring := true) in
constructive_injectivity AtomicCollision

#check_failure AtomicCollision.first.inj
#check_failure AtomicCollision.first.injEq
#check_failure AtomicCollision.second.injEq

/-- The existing implication remains callable after atomic rejection. -/
private theorem collisionPreservesExisting {left right : Nat}
    (equal : AtomicCollision.second left = AtomicCollision.second right) : left = right :=
  AtomicCollision.second.inj equal

/-- already exists -/
#guard_msgs (error, substring := true) in
constructive_injectivity Pair

/-- A scalar definition is not an inductive constructor owner. -/
private def notDatatype : Nat := 0

/-- is not an inductive type -/
#guard_msgs (error, substring := true) in
constructive_injectivity notDatatype

set_option genInjectivity false in
/-- An inductive proposition is outside the datatype certificate interface. -/
private inductive Predicate : Prop where
  /-- The proposition's only witness. -/
  | witness : Predicate

/-- expects a datatype, not an inductive predicate -/
#guard_msgs (error, substring := true) in
constructive_injectivity Predicate

set_option genInjectivity false in
/-- An unsafe datatype cannot acquire safe constructor certificates. -/
private unsafe inductive UnsafeOwner where
  /-- The retained unsafe scalar payload. -/
  | payload (value : Nat)

/-- expects a safe inductive datatype -/
#guard_msgs (error, substring := true) in
constructive_injectivity UnsafeOwner

end Test.Elab.ConstructiveInjectivity
