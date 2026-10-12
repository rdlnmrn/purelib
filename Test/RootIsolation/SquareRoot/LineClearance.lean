module
import Purelib.Data.Rat.Fraction.Cast
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Data.Rat.Fraction.Order
import Purelib.RootIsolation.SquareRoot.Clearance.QuadraticLineClearance

open Purelib.Data.Rat

open Purelib.Geometry

open Purelib.RootIsolation.SquareRoot.Clearance.QuadraticLineClearance

@[expose] public section

/-!
Small kernel-checked regressions for the executable quadratic line bounds.
The zero-coordinate cases have nonzero imaginary parameter, so no spurious
nonzero-coordinate assumption is needed.  These import no generated bank.
-/

namespace Test.RootIsolation.SquareRoot.LineClearance

open Purelib.RootIsolation.SquareRoot.Clearance.QuadraticLineClearance.Owner

/-- The rational rectangle with real interval [-2, 2] and imaginary interval [-1, 1]. -/
private def box : Rational.Box where
  xLower := -2
  xUpper := 2
  yLower := -1
  yUpper := 1
  x_valid := by decide
  y_valid := by decide

/-- The vertical axis has squared clearance bound one half in the retained rectangle. -/
example : ((Owner.quadraticAxisClearances ⟨2, 1⟩).vertical LineClearance.box 0 (by decide)).bound =
    1 / 2 := by decide

/-- The vertical line at one has squared clearance bound twenty-five twenty-sixths. -/
example : ((Owner.quadraticAxisClearances ⟨2, 1⟩).vertical LineClearance.box 1 (by decide)).bound =
    25 / 26 := by decide

/-- The horizontal axis has squared clearance bound one half in the retained rectangle. -/
example : ((Owner.quadraticAxisClearances ⟨2, 1⟩).horizontal LineClearance.box 0 (by decide)).bound =
    1 / 2 := by decide

/-- The horizontal line at one has squared clearance bound one hundred twenty-one fiftieths. -/
example : ((Owner.quadraticAxisClearances ⟨2, 1⟩).horizontal LineClearance.box 1 (by decide)).bound =
    Fraction.Cast.fromInt 121 / Fraction.Cast.fromInt 50 := by decide

end Test.RootIsolation.SquareRoot.LineClearance
