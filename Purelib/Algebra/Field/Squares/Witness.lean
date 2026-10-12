module
public import Purelib.Data.Nat.Order
public import Purelib.Algebra.Group.Negation

public import Purelib.Algebra.Field.ExplicitField
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

section
open Purelib.Algebra
open Purelib.Data

-- These owned adapters retain the complete original operation dictionaries.
attribute [local instance 2000] Group.Negation.subNegZeroMonoid
  Nat.successorNeZero Nat.successorAtLeastTwo

open Purelib.Algebra.Field

section
public section

/-!
# Rational rotations, Theorem 65 and Examples 66--67

The square condition for a prescribed axis and half spread is carried by an
explicit nonzero root.  From that root we compute the two opposite anchor
vectors and hence the two inverse rotations.  No square-root operation or
choice principle enters the construction.
-/

namespace Purelib.Algebra.Field.Squares.Witness

variable {K : Type*} [ExplicitField K]

set_option genInjectivity false in
/-- A scalar with a retained nonzero square root.

The record stores the root, its nonzero certificate, and the equation identifying its square with the indexed scalar. -/
structure NonzeroSquare (value : K) where
  /-- The retained root of the indexed scalar. -/ root : K
  /-- The retained root is nonzero. -/ rootNonzero : root ≠ 0
  /-- The root square equals the indexed scalar. -/ square : root ^ 2 = value

constructive_injectivity NonzeroSquare

namespace NonzeroSquare

open Purelib.Algebra.Field.Squares.Witness in
/-- Negate the retained root of a nonzero square certificate.

The represented scalar is unchanged, and the new root remains nonzero. -/
@[expose] def neg {value : K} (certificate : NonzeroSquare
  value) :
    NonzeroSquare value where
  root := -certificate.root
  rootNonzero := by
    intro negZero
    apply certificate.rootNonzero
    calc
      certificate.root = -(-certificate.root) := by ring1
      _ = -0 := by rw [negZero]
      _ = 0 := by ring1
  square := by
    calc
      (-certificate.root) ^ 2 = certificate.root ^ 2 := by ring1
      _ = value := certificate.square

end NonzeroSquare

end Purelib.Algebra.Field.Squares.Witness

end

end
