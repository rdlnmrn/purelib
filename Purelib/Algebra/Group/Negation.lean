module

public import Mathlib.Algebra.Group.Defs

namespace Purelib.Algebra.Group.Negation

-- Keep the negation operation in the original retained parent.
attribute [local instance high] SubNegMonoid.toNeg

/-- Involutive subtraction retains its operations and fixes zero under negation.

The zero equation follows directly from the retained inverse characterization
applied to the displayed sum of two zeroes. The parent, subtraction and scalar
multiplication fields are preserved. Its instance priority replaces the derived
adapter while retaining higher-priority direct and local data instances. -/
@[expose, reducible] public def subNegZeroMonoid {G : Type*} [SubtractionMonoid G] :
    SubNegZeroMonoid G where
  toSubNegMonoid := SubtractionMonoid.toSubNegMonoid
  neg_zero := SubtractionMonoid.neg_eq_of_add 0 0 (AddZeroClass.add_zero 0)

attribute [instance 101] subNegZeroMonoid

end Purelib.Algebra.Group.Negation
