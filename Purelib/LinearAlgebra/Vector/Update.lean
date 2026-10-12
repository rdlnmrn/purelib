module

public import Mathlib.Algebra.Ring.Defs

public import Purelib.Data.Vector.Basic
import Mathlib.Tactic.TypeStar

open Purelib

section
@[expose] public section

/-!
# Pairing-preserving dual changes of coordinates

Congruence changes a matrix as `S C Sᵀ`; its arguments must change by
`S⁻ᵀ`, not by `S`. The formulas here use two cached finite weighted sums
per shear and work over any supplied commutative ring.
-/

namespace Purelib.LinearAlgebra.Vector.Update

variable {K : Type*} [CommRing K] {n : Nat}

/-- Add the supplied amount at one retained vector coordinate.

All other coordinates are copied unchanged into structural vector data of the same dimension. -/
def bump (values : Data.Vector K n) (index : Fin n) (amount : K)
  : Data.Vector K n :=
  Data.Vector.Basic.vectorOfFn fun position => values position + if position = index then amount else 0

open Purelib.LinearAlgebra.Vector in
/-- Read a coordinate update as the original entry plus its equality-indicated increment. -/
theorem bump_apply (values : Data.Vector K n) (index : Fin n)
  (amount : K) (position : Fin n) :
    bump values index amount position = values position + if position = index then amount else 0 :=
  Data.Vector.Basic.vectorOfFn_apply _ position

end Purelib.LinearAlgebra.Vector.Update

end
