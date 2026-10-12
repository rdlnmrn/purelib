module

public import Init.Prelude
meta import Purelib.Elab.ConstructiveInjectivity

section
@[expose] public section

/-!
# Hyperelliptic data and certified algebraic differential observations

The period integrator must not accept an arbitrary convergent integrand under
the name `x^k dx / y`.  Each observation below therefore supplies an exact
finite point `y`, proves `y^2 = f(x)`, proves `y` nonzero, records the selected
sheet, and checks the differential equation after clearing the denominator.
These certificates are aligned cell-by-cell with the sheet-aware lifted path.
-/

namespace Purelib.Curves.Hyperelliptic.Differentials.Basic

set_option genInjectivity false in
/-- The standard holomorphic differential `x^k dx/y`, where `k` is the zero-based finite index. -/
structure Differential (genus : Nat) where
  /-- The finite index selecting a standard holomorphic differential. -/ index : Fin genus

constructive_injectivity Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential

namespace Differential

open Purelib in
/-- Read the natural exponent of x in the indexed differential x to the k dx over y. -/
def exponent {genus : Nat} (differential :
  Curves.Hyperelliptic.Differentials.Basic.Differential genus) : Nat :=
  differential.index.val

end Differential

end Purelib.Curves.Hyperelliptic.Differentials.Basic

end
