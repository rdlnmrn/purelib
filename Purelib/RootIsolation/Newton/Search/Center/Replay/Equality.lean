module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Clearance.Box.Line.Elimination.Provider
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Elimination.Axis.Certificate
public import Purelib.RootIsolation.Newton.Search.Center.Basic
import Purelib.RootIsolation.State.Raw

import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order
import Purelib.RootIsolation.Refinement.Basic
import Purelib.RootIsolation.State.WindingOne.Basic

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

section
@[expose] public section

/-!
# Exact checked-refinement outputs from the same box

The bounded Newton shortcut does not inspect the incoming clearance number.
With a fixed ambient and clearance constructor, equal incoming boxes produce
equal complete optional output states.  No such assertion is made about the
total extraction fallback.
-/

namespace Purelib.RootIsolation.Newton.Search.Center.Replay.Equality

/-- Equal original input boxes give identical optional checked states, independently of the input proof payloads. -/
theorem checkCenter_state_eq_of_box_eq
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box} {degreeBound :
      Nat}
    (elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p degreeBound)
    (left right : State.Raw.RawWindingState p ambient)
    (same : left.box = right.box) (epsilon : Fraction.Rational) (center : Gaussian.Basic.Canonical)
    (clearances : Clearance.Box.Line.Elimination.Provider.AxisClearances elimination) :
    (Newton.Search.Center.Basic.checkCenter elimination left epsilon center clearances).map (fun result => result.state)
      =
      (Newton.Search.Center.Basic.checkCenter elimination right epsilon center clearances).map (fun result =>
        result.state) := by
  cases left
  cases right
  cases same
  unfold Newton.Search.Center.Basic.checkCenter
  dsimp only
  split
  · split
    · split
      · split <;> rfl
      · rfl
    · rfl
  · rfl
end Purelib.RootIsolation.Newton.Search.Center.Replay.Equality

end
