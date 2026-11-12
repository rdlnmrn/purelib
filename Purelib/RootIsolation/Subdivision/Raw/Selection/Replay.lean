module

public import Purelib.RootIsolation.Subdivision.Raw.Selection
public import Purelib.RootIsolation.Isolation.RawSubdivisionReplay
import Purelib.Polynomial.Winding.Box.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic

public section

namespace Purelib.RootIsolation.Subdivision.Raw.Selection.Replay

open Purelib.Geometry.Rational
open Purelib.Polynomial
open Purelib.RootIsolation

variable {p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
  {state : State.Raw.RawWindingState p ambient}

/-- Select the original first nonzero child from retained exact winding readbacks.

The original lower-left, upper-left, lower-right order and upper-right fallback
are preserved. Each saved scalar retains its equation to the original winding
of the corresponding original child box.
-/
@[expose] def choose (grid : Subdivision.Raw.Grid.RawFourGrid state)
    (lowerLeft : { value : Int // value = Winding.Box.Basic.quadrupledBoxWinding p grid.lowerLeft.box })
    (upperLeft : { value : Int // value = Winding.Box.Basic.quadrupledBoxWinding p grid.upperLeft.box })
    (lowerRight : { value : Int // value = Winding.Box.Basic.quadrupledBoxWinding p grid.lowerRight.box }) :
    Clearance.Box.Refinement.Contracting.RawChild p ambient state.box :=
  if lowerLeft.val ≠ 0 then grid.lowerLeft
  else if upperLeft.val ≠ 0 then grid.upperLeft
  else if lowerRight.val ≠ 0 then grid.lowerRight
  else grid.upperRight

/-- Ordered selection from the retained scalar readbacks is the exact original selected child. -/
theorem choose_eq (grid : Subdivision.Raw.Grid.RawFourGrid state)
    (lowerLeft : { value : Int // value = Winding.Box.Basic.quadrupledBoxWinding p grid.lowerLeft.box })
    (upperLeft : { value : Int // value = Winding.Box.Basic.quadrupledBoxWinding p grid.upperLeft.box })
    (lowerRight : { value : Int // value = Winding.Box.Basic.quadrupledBoxWinding p grid.lowerRight.box }) :
    choose grid lowerLeft upperLeft lowerRight = Subdivision.Raw.Selection.firstNonzeroChild grid := by
  unfold choose Subdivision.Raw.Selection.firstNonzeroChild
  rewrite [lowerLeft.property, upperLeft.property, lowerRight.property]
  rfl

/-- Restore the original raw-refinement state using the retained grid and exact winding scalars.

The selected original child's fields are consumed directly. The scalar agreement
proof transfers the original first-nonzero winding certificate without executing
any original winding producer.
-/
@[expose] def step (grid : Subdivision.Raw.Grid.RawFourGrid state)
    (lowerLeft : { value : Int // value = Winding.Box.Basic.quadrupledBoxWinding p grid.lowerLeft.box })
    (upperLeft : { value : Int // value = Winding.Box.Basic.quadrupledBoxWinding p grid.upperLeft.box })
    (lowerRight : { value : Int // value = Winding.Box.Basic.quadrupledBoxWinding p grid.lowerRight.box }) :
    State.Raw.RawWindingState p ambient :=
  let child := choose grid lowerLeft upperLeft lowerRight
  ⟨child.box, child.refinesAmbient, child.proper, child.clearance, by
    change Winding.Box.Basic.quadrupledBoxWinding p (choose grid lowerLeft upperLeft lowerRight).box ≠ 0
    rewrite [choose_eq]
    exact Subdivision.Raw.Selection.firstNonzeroChild_rawWinding_ne grid⟩

/-- Restored ordered scalar selection yields every original raw-refinement state field. -/
theorem step_eq {degreeBound : Nat}
    (elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p degreeBound)
    (saved : Clearance.Box.Grid.Four.Replay.Checked elimination state.box state.proper)
    (lowerLeft : { value : Int // value = Winding.Box.Basic.quadrupledBoxWinding p
      (Isolation.RawSubdivisionReplay.grid elimination state saved).lowerLeft.box })
    (upperLeft : { value : Int // value = Winding.Box.Basic.quadrupledBoxWinding p
      (Isolation.RawSubdivisionReplay.grid elimination state saved).upperLeft.box })
    (lowerRight : { value : Int // value = Winding.Box.Basic.quadrupledBoxWinding p
      (Isolation.RawSubdivisionReplay.grid elimination state saved).lowerRight.box }) :
    step (Isolation.RawSubdivisionReplay.grid elimination state saved) lowerLeft upperLeft lowerRight =
      Subdivision.Raw.Step.refineOnce elimination state := by
  rcases lowerLeft with ⟨lowerLeft, lowerLeftEq⟩
  rcases upperLeft with ⟨upperLeft, upperLeftEq⟩
  rcases lowerRight with ⟨lowerRight, lowerRightEq⟩
  cases lowerLeftEq
  cases upperLeftEq
  cases lowerRightEq
  exact Isolation.RawSubdivisionReplay.step_eq elimination state saved

end Purelib.RootIsolation.Subdivision.Raw.Selection.Replay
