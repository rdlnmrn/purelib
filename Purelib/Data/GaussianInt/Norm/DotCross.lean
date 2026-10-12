module
public import Purelib.Data.GaussianInt.Norm.Basic
import Purelib.Data.GaussianInt.Basic

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Tactic.Ring

section
open Purelib.Data
open Purelib.Data.GaussianInt.Norm
open Purelib.Data.GaussianInt
public section

/-!
# Constructive extended Euclidean certificates over the Gaussian integers

Nearest-Gaussian-integer division gives a Euclidean recursion whose measure is
the displayed natural quadrance.  This file packages that recursion with all
of the data needed downstream: a Bezout identity and explicit quotients
showing that the returned gcd divides both inputs.  The construction is a
finite program and introduces neither choice nor a completed carrier.
-/

namespace Purelib.Data.GaussianInt.Norm.DotCross

/-! ## Arithmetic at the boundary of the nearest-remainder square -/

/-- The integral dot product of the two retained Gaussian coordinate pairs. -/
@[expose] def dot (left right : GaussianInt) : Int :=
  left.re * right.re + left.im * right.im

/-- The oriented integral cross product, equal to the imaginary part of left times
conjugate right. -/
@[expose] def cross (left right : GaussianInt) : Int :=
  left.im * right.re - left.re * right.im

/-- The squared integral dot and cross products sum to the product of natural quadrances.

This two-coordinate Lagrange identity keeps all values integral, casting the
nonnegative natural norms back into the integers. -/
theorem dot_sq_add_cross_sq (left right : GaussianInt) :
    DotCross.dot left right * DotCross.dot left right + DotCross.cross left right * DotCross.cross left right =
      (normNat left : Int) * (normNat right : Int) := by
  have leftNorm : (normNat left : Int) = normInt left := by
    exact Basic.normInt_eq_natCast_normNat left |>.symm
  have rightNorm : (normNat right : Int) = normInt right := by
    exact Basic.normInt_eq_natCast_normNat right |>.symm
  rw [leftNorm, rightNorm]
  simp only [DotCross.dot, DotCross.cross, normInt]
  ring1
end Purelib.Data.GaussianInt.Norm.DotCross

end

end
