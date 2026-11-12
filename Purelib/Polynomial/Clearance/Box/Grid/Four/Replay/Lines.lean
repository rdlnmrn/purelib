module

public import Purelib.Polynomial.Clearance.Box.Grid.Four.Replay
public import Purelib.Polynomial.Clearance.Box.Line.Elimination.Provider
import Purelib.Polynomial.Elimination.Axis.Cuts
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Clearance.Box.Grid.Four.Elimination
import Purelib.Data.Rat.Fraction.Order.Basic

public section

namespace Purelib.Polynomial.Clearance.Box.Grid.Four.Replay

open Purelib.Geometry.Rational
open Purelib.Polynomial
open Purelib.Polynomial.Clearance.Box.Line.Elimination
open Purelib.Data.Rat.Fraction (Rational)

variable {p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {degreeBound : Nat}
  (elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p degreeBound)
  (box : Box) (proper : box.Proper)

/-- A retained vertical clearance equal to the original certificate at the original safe cut. -/
abbrev Vertical :=
  { value : Clearance.Box.Line.Basic.VerticalLineClearance p box
      (Elimination.Axis.Cuts.verticalSafeCoordinate elimination box proper) //
    value = (Provider.AxisClearances.canonical elimination).vertical box
      (Elimination.Axis.Cuts.verticalSafeCoordinate elimination box proper)
      (Elimination.Axis.Cuts.verticalSafeCoordinate_spec elimination box proper).1 }

/-- A retained horizontal clearance equal to the original certificate at the original safe cut. -/
abbrev Horizontal :=
  { value : Clearance.Box.Line.Basic.HorizontalLineClearance p box
      (Elimination.Axis.Cuts.horizontalSafeCoordinate elimination box proper) //
    value = (Provider.AxisClearances.canonical elimination).horizontal box
      (Elimination.Axis.Cuts.horizontalSafeCoordinate elimination box proper)
      (Elimination.Axis.Cuts.horizontalSafeCoordinate_spec elimination box proper).1 }

/-- Reconstruct the exact original four-cell grid from its retained original line clearances.

The supplied coordinates retain equality to the original finite selections.
Both actual coordinates and clearance records are consumed directly; this
constructor executes neither coordinate search nor clearance provider while
reproducing every original grid field.
-/
@[expose] def fromLines
    (x : { value : Rational //
      value = Elimination.Axis.Cuts.verticalSafeCoordinate elimination box proper })
    (y : { value : Rational //
      value = Elimination.Axis.Cuts.horizontalSafeCoordinate elimination box proper })
    (vertical : Vertical elimination box proper) (horizontal : Horizontal elimination box proper) :
    Checked elimination box proper :=
  let xSpec := Elimination.Axis.Cuts.verticalSafeCoordinate_spec elimination box proper
  let ySpec := Elimination.Axis.Cuts.horizontalSafeCoordinate_spec elimination box proper
  let result : Clearance.Box.Grid.Four.Basic.ClearFourGrid p box :=
    { xCut := x.val
      yCut := y.val
      xInside := by
        rewrite [x.property]
        exact ⟨xSpec.2.1.le, xSpec.2.2.le⟩
      yInside := by
        rewrite [y.property]
        exact ⟨ySpec.2.1.le, ySpec.2.2.le⟩
      verticalClearance := x.property.symm ▸ vertical.val
      horizontalClearance := y.property.symm ▸ horizontal.val }
  ⟨result, by
    rcases x with ⟨x, xEq⟩
    rcases y with ⟨y, yEq⟩
    cases xEq
    cases yEq
    rcases vertical with ⟨vertical, verticalEq⟩
    rcases horizontal with ⟨horizontal, horizontalEq⟩
    cases verticalEq
    cases horizontalEq
    rfl⟩

end Purelib.Polynomial.Clearance.Box.Grid.Four.Replay
