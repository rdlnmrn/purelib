module

public import Purelib.Approximation.Gaussian.Name.Coherent
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Approximation.Gaussian

section
@[expose] public section

/-!
# Progressive finite Taylor and multivariable CCL tables

The displayed higher-jet layer stores Gaussian rationals.  Here every entry is
instead a coherent productive CCL channel.  All operations recurse over the
displayed finite coefficient lists, and every resulting table inherits one
computable joint request from `ProgressiveFiniteTable`.
-/

namespace Purelib.Polynomial.Ascending.Gaussian.Progressive.Basic

set_option genInjectivity false in
/-- A finite low-to-high table of productive CCL coefficient channels. -/
structure TaylorJet where
  /-- The retained finite list of coherent productive Gaussian coefficient channels. -/ coefficients : List
    Name.Coherent.CoherentNamed

constructive_injectivity TaylorJet

namespace TaylorJet

open Purelib.Polynomial
/-- The number of retained coherent coefficient channels in the Taylor jet. -/
def length (jet :
  TaylorJet) : Nat := jet.coefficients.length

/-- Construct a constant progressive jet with the supplied coherent channel. -/
def constant (value :
  Name.Coherent.CoherentNamed) : TaylorJet := ⟨[value]⟩
end TaylorJet

end Purelib.Polynomial.Ascending.Gaussian.Progressive.Basic

end
