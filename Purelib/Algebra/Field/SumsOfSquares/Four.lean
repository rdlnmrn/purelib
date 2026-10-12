module

public import Purelib.Algebra.Field.ExplicitField
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Algebra.Field

section
@[expose] public section

/-!
# Rational rotations, Theorem 61: the quadrance class

Square classes are represented quotient-free.  Equality carries an explicit
nonzero square factor, so invariance and multiplicativity remain executable
finite field calculations.
-/

namespace Purelib.Algebra.Field.SumsOfSquares.Four

variable {K : Type*} [ExplicitField K]

set_option genInjectivity false in
/-- Four displayed scalars whose squared sum is the indexed value.

The record retains all four coordinates and the exact sum-of-squares certificate. -/
structure FourSquareRepresentation (value : K) where
  /-- The first retained coordinate. -/ scalar : K
  /-- The second retained coordinate. -/ t : K
  /-- The third retained coordinate. -/ r : K
  /-- The fourth retained coordinate. -/ s : K
  /-- The four coordinate squares sum to the indexed value. -/ equation : scalar ^ 2 + t ^ 2 + r ^ 2 + s ^ 2 = value

constructive_injectivity FourSquareRepresentation

end Purelib.Algebra.Field.SumsOfSquares.Four

end
