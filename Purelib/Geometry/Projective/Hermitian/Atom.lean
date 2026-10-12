module

import Purelib.Data.Gaussian.Basic
public import Purelib.Data.Rat.SignTest
public import Purelib.Geometry.Projective.Hermitian.Basic
import Init.Prelude
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib

open Purelib.Data.Rat

open Purelib.Geometry.Projective

section
@[expose] public section

/-!
# Finite Hermitian formulas for raw CCL parser states

Every predicate in an arbitrary finite raw-parser state is compiled into a
finite Boolean formula whose atoms are signs of four-coefficient rational
Hermitian forms.  Unfinished sector prefixes use the direct finite
disjunction of their `8/4/2` candidate rows.  This keeps the implementation
small while preserving the exact weak/strict boundary convention.
-/

section

namespace Purelib.Geometry.Projective.Hermitian

set_option genInjectivity false in
/-- One sign test on a generalized-circle form. -/
structure Atom where
  /-- The Hermitian form whose value is tested. -/ form : Hermitian.HermitianForm
  /-- The required weak, strict, or equality sign of the form value. -/ sign : Data.Rat.SignTest
deriving DecidableEq

constructive_injectivity Atom

end Purelib.Geometry.Projective.Hermitian

section

namespace Purelib.Geometry.Projective.Hermitian.Atom

/-- The atom holds when its sign test accepts the evaluated Hermitian form. -/
def Holds (atom : Atom) (value :
  Data.Gaussian.Basic.Canonical) : Prop :=
  atom.sign.Holds (atom.form.eval value)

end Purelib.Geometry.Projective.Hermitian.Atom

namespace Purelib.CCL.Boundary.Formula.Atom

/-- Decide a Hermitian atom by evaluating its rational form and sign test. -/
instance (atom : Hermitian.Atom) (value : Data.Gaussian.Basic.Canonical) : Decidable (atom.Holds
  value) := by
  unfold Hermitian.Atom.Holds
  infer_instance

end Purelib.CCL.Boundary.Formula.Atom

end
end

end
