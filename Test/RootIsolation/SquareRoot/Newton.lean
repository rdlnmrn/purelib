module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
public import Purelib.RootIsolation.SquareRoot.Newton.Search

import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib

open Purelib.RootIsolation.SquareRoot.Newton

section
@[expose] public section

namespace Test.RootIsolation.SquareRoot.Newton

open Purelib.CCL.Geometry.CheckedSquareRootNewton

/-- An exact complex root is retained by the checked grid proposal. -/
theorem exact_complex_root :
    (Search.search ⟨0, 2⟩ (fun point => point * point = (⟨0, 2⟩ : Data.Gaussian.Basic.Canonical))
      1 (1 / 4) ⟨1, 1⟩).map Subtype.val = some ⟨1, 1⟩ := by
  decide +kernel

/-- The first proposal fails; the rounded Newton successor passes the exact squared residual bound. No convergence
theorem is used. -/
theorem refined_real_sample :
    (Search.search 2 (fun point =>
      Data.Gaussian.Norm.Basic.normSq (point * point - 2) < 1 / 8)
      2 (1 / 16) 1).map Subtype.val = some ⟨3 / 2, 0⟩ := by
  decide +kernel

/-- A checked axis projection removes an off-axis coordinate even when it is large enough to survive rounding; both
candidates meet the residual request, but the real sample avoids unnecessary coefficient growth. -/
theorem checked_axis_projection :
    (Search.search 2 (fun point =>
      Data.Gaussian.Norm.Basic.normSq (point * point - 2) < 1 / 8)
      1 (1 / 16) ⟨3 / 2, 1 / 16⟩).map Subtype.val = some ⟨3 / 2, 0⟩ := by
  decide +kernel

/-- The other axis and a negative selected occurrence are checked too. -/
theorem checked_imaginary_projection :
    (Search.search (-1) (fun point => point * point = (-1 : Data.Gaussian.Basic.Canonical) ∧ point.im < 0)
      1 (1 / 16) ⟨1 / 16, -1⟩).map Subtype.val = some ⟨0, -1⟩ := by
  decide +kernel

/-- A zero seed for a nonzero target may fail throughout the finite search; failure is explicit and does not pretend
that every Newton orbit succeeds. -/
theorem rejected_zero_seed :
    (Search.search 1 (fun point => point = (1 : Data.Gaussian.Basic.Canonical)) 3 (1 / 4) 0).isNone = true := by
  decide +kernel

end Test.RootIsolation.SquareRoot.Newton

end

end
