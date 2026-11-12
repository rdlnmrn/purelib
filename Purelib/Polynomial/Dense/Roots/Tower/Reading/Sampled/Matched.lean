module

public import Purelib.Polynomial.Dense.Roots.Tower.Reading.Sampled

/-!
# Original bounded coordinates of ordered sampled roots

The ordered correspondence retains the same root and sample positions.
Its length equality transports only the original natural index bound;
the indexed readback does not construct another list or enumeration.
-/

public section

namespace Purelib.Polynomial.Dense.Roots.Tower.Reading.Matched

open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat.Fraction (Rational)

universe u

variable {K : Type u} {read : K → Canonical} {bound : Rational}
variable {roots : List (Block K)} {nodes : List Canonical}

/-- The original ordered root and sample lists have the same length. -/
theorem length (matched : Matched read bound roots nodes) : roots.length = nodes.length := by
  induction matched with
  | nil => rfl
  | cons _ _ previous => exact congrArg Nat.succ previous

/-- The same bounded original root position is a valid original sample position. -/
theorem nodeBound (matched : Matched read bound roots nodes) (index : Fin roots.length) :
    index.val < nodes.length := matched.length ▸ index.isLt

/-- The original indexed root reading stays within the same original indexed sample's paid bound. -/
theorem get (matched : Matched read bound roots nodes) (index : Fin roots.length) :
    Norm.Basic.normSq (read (roots[index.val]'index.isLt).point -
      nodes[index.val]'(matched.nodeBound index)) ≤ bound := by
  induction matched with
  | nil => exact Fin.elim0 index
  | cons current _ previous =>
      rcases index with ⟨position, bounded⟩
      cases position with
      | zero => exact current
      | succ position => exact previous ⟨position, Nat.lt_of_succ_lt_succ bounded⟩

end Purelib.Polynomial.Dense.Roots.Tower.Reading.Matched

end
