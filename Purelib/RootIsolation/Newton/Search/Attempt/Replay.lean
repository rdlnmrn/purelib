module
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Clearance.Box.Line.Elimination.Provider
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Elimination.Axis.Certificate
public import Purelib.RootIsolation.Newton.Search.Attempt
import Purelib.RootIsolation.State.Raw

import Purelib.Data.Rat.Fraction.Field
import Purelib.RootIsolation.Newton.Search.Iteration.Replay
import Purelib.RootIsolation.Refinement.Basic
import Purelib.RootIsolation.State.WindingOne.Basic

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

namespace Purelib.RootIsolation.Newton.Search.Attempt.Replay

/-- Equal original input boxes produce the same optional checked state in the fixed six-proposal Newton attempt. -/
theorem attempt_state_eq_of_box_eq
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box} {degreeBound :
      Nat}
    (elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p degreeBound)
    (left right : State.Raw.RawWindingState p ambient)
    (same : left.box = right.box) (epsilon : Fraction.Rational) (clearances :
      Clearance.Box.Line.Elimination.Provider.AxisClearances elimination) :
    (Newton.Search.Attempt.attempt elimination left epsilon clearances).map (fun result => result.state) =
      (Newton.Search.Attempt.attempt elimination right epsilon clearances).map (fun result => result.state) := by
  unfold Newton.Search.Attempt.attempt
  rw [← same]
  exact Newton.Search.Iteration.Replay.search_state_eq_of_box_eq elimination left right same epsilon 6 0 _ clearances

end Purelib.RootIsolation.Newton.Search.Attempt.Replay

end
