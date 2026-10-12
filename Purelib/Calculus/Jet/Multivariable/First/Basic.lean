module

public import Purelib.Data.Gaussian.Basic
meta import Purelib.Elab.ConstructiveInjectivity

section
@[expose] public section

/-!
# Finite higher, Taylor, directional, and multivariable jets

The one-variable Taylor object below is a wrapper around the repository's
low-to-high finite rational polynomial program.  Repeated differentiation is
structural recursion on a requested natural order.  Multivariable first jets
store a displayed finite list of Gaussian-rational partial coefficients; a
directional coefficient is a finite dot-product recursion.

These are finite tables, not function spaces or infinite formal series.
-/

namespace Purelib.Calculus.Jet.Multivariable.First.Basic

open Purelib.Data.Gaussian in
set_option genInjectivity false in
/-- A Gaussian rational value and a finite list of partial coefficients.

The list length supplies the displayed dimension. The record alone carries no claim that the coefficients differentiate
a function. -/
structure MultivariableFirstJet where
  /-- The retained Gaussian rational value. -/ value : Basic.Canonical
  /-- The ordered finite list of Gaussian rational partial coefficients. -/ partials : List Basic.Canonical
deriving DecidableEq

constructive_injectivity MultivariableFirstJet

namespace MultivariableFirstJet

open Purelib.Calculus.Jet.Multivariable.First.Basic in
/-- Count the displayed partial coefficients. -/
def dimension (jet : MultivariableFirstJet)
  : Nat := jet.partials.length
end MultivariableFirstJet

end Purelib.Calculus.Jet.Multivariable.First.Basic

end
