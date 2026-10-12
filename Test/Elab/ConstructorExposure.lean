module
meta import Purelib.Elab.ConstructiveInjectivity

@[expose] public section
namespace Test.Elab.ConstructorExposure
universe u

set_option genInjectivity false in
/-- A pair retaining two original entries under an exposed public section. -/
structure Pair (α : Type u) where
  /-- The first original entry. -/ first : α
  /-- The second original entry. -/ second : α

constructive_injectivity Pair
end Test.Elab.ConstructorExposure
end
