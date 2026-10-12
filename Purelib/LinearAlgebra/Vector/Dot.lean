module

public import Purelib.Algebra.FiniteSum.Fin
public import Purelib.Data.Vector.Basic
import Mathlib.Tactic.TypeStar
import Mathlib.Algebra.Ring.Defs

open Purelib.Algebra

open Purelib

section
@[expose] public section

/-!
# Fraction-free finite matrix inversion

Vectors and matrices are dimension-indexed structural `Vector` data, exposed
through entry lookup, and every sum is a fold over `List.ofFn`.  A scaled
inverse records both multiplication identities.  The block extension below
is division-free: a pivot and a scaled inverse of its Schur complement produce
a scaled inverse of the whole matrix.
-/

namespace Purelib.LinearAlgebra

universe u
variable {K : Type*} [CommRing K]

/-- Compute the finite coordinatewise dot product of two structural vectors.

The natural dimension determines the finite sum of products over the supplied commutative ring. -/
def Vector.Dot.dot {n : Nat} (left right : Data.Vector K n) : K :=
  FiniteSum.Fin.sumFin (fun i => left i * right i)
end Purelib.LinearAlgebra

end
