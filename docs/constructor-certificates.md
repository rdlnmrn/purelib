# Constructor certificates

`Purelib.Elab.ConstructiveInjectivity` provides
`constructive_injectivity TypeName`. The command derives opaque constructor
`.inj` implications and `.injEq` logical equivalences from the original
inductive declaration's metadata. Import the command in the meta phase and
suppress Lean's default injectivity generation locally around the owner:

```lean
module
meta import Purelib.Elab.ConstructiveInjectivity

namespace Example

set_option genInjectivity false in
/-- An ordered pair of scalar entries. -/
public structure Pair where
  /-- The first entry. -/ first : Nat
  /-- The second entry. -/ second : Nat

constructive_injectivity Pair

end Example
```

The resulting `Pair.mk.inj` identifies its ordered fields from constructor
equality. `Pair.mk.injEq` states the corresponding `Iff`, consumed with `.mp`
or `.mpr`. Neither theorem is registered with `simp`: proposition-equality
companions would retain `propext`.

Name the complete datatype once, including each actual owner in a mutual group.
The command examines every constructor of that owner; a request for
`Parent.Child` does not cover `Parent`. A qualified datatype request resolves
the original owner without needing field recipes, universe lists or rooted
constructor names. Existing certificates, unsafe datatypes, inductive
predicates and unsupported constructor shapes are errors, with no partially
published family.

Certificate types retain the original ordered parameters, universe labels and
binder modes. Constructor fields that determine the result or index types are
shared by both applications. Other nonproof fields contribute ordered `Eq` or
`HEq` relations, according to their dependent types. Proof fields retain their
original domains and are identified by kernel proof irrelevance after the
relevant data identities are substituted. Constructors without relevant field
relations have no `.inj` or `.injEq` API, including nullary and proof-only
constructors.

The implication keeps constructor arguments implicit and takes its equality
proof explicitly. The equivalence retains the original left argument modes
and explicit right partners. Fresh primed names avoid shadowing an original
accessible named argument, including anonymous dictionaries and fields named
`x` or `inst`. Original optional and automatic proof domains, polymorphic
callbacks and local type expressions remain part of the constructor contract.
Unrelated ambient included variables do not enter generated theorem types.

Generated names use the original constructor's mathematical route and
visibility, including private constructors. Public certificates remain opaque
inside exposed public sections. Generation changes neither constructor data
nor executable operations and derived equality helpers.

`Test.Elab.ConstructiveInjectivity` and the supporting constructor-certificate
regressions cover dependent and indexed claims, private and rooted owners,
opacity, universe scopes, dictionaries, named arguments, original field domains,
polymorphic functions, empty APIs and failed-family rollback. Lean kernel checks
and the normal authoritative axiom audit establish the generated mathematical
proofs and their complete transitive dependencies. Full build, axiom and nanoda
checks verify the complete project and configured script owners.

The normal audit does not select every independent internal metaprogramming
helper. Strict `--all-helpers` auditing of the provider is deferred to a separate
follow-up. Clean generated certificates alone do not
establish that the provider's entire internal helper closure is axiom-free.
