module
import Purelib.Polynomial.Dense.Gaussian.Derivative.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Newton.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Grid.Box
import Purelib.Data.Gaussian.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Clearance.Box.Line.Elimination.Provider
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Elimination.Axis.Certificate
import Purelib.RootIsolation.Newton.Search.Center.Basic
public import Purelib.RootIsolation.Newton.Search.Iteration
import Purelib.RootIsolation.State.Raw

import Purelib.RootIsolation.Newton.Search.Center.Replay.Equality
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

namespace Purelib.RootIsolation.Newton.Search.Iteration.Replay

/-- Equal original input boxes produce the same optional checked state throughout the bounded Newton search. -/
theorem search_state_eq_of_box_eq
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box} {degreeBound :
      Nat}
    (elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p degreeBound)
    (left right : State.Raw.RawWindingState p ambient)
    (same : left.box = right.box) (epsilon : Fraction.Rational)
    (attempts extraBits : Nat) (proposal : Gaussian.Basic.Canonical) (clearances :
      Clearance.Box.Line.Elimination.Provider.AxisClearances elimination) :
    (Newton.Search.Iteration.search elimination left epsilon attempts extraBits proposal clearances).map (fun result =>
      result.state) =
      (Newton.Search.Iteration.search elimination right epsilon attempts extraBits proposal clearances).map (fun result
        => result.state) := open Purelib.Approximation.Gaussian in by
  induction attempts generalizing extraBits proposal with
  | zero => rw [Newton.Search.Iteration.search_zero, Newton.Search.Iteration.search_zero]; rfl
  | succ attempts ih =>
      let center := Grid.Box.roundedCenter left.box epsilon extraBits proposal
      have centers : Grid.Box.roundedCenter right.box epsilon extraBits proposal = center := by rw [← same]
      have agree := Newton.Search.Center.Replay.Equality.checkCenter_state_eq_of_box_eq elimination left right same
        epsilon center clearances
      rw [Newton.Search.Iteration.search_succ, Newton.Search.Iteration.search_succ, centers]
      change (match Newton.Search.Center.Basic.checkCenter elimination left epsilon center clearances with
        | some accepted => some accepted
        | none => if Gaussian.Basic.value
            (Dense.Gaussian.Derivative.Evaluation.derivativeEval p center) = 0 then none
          else Newton.Search.Iteration.search elimination left epsilon attempts (extraBits + 2)
            (Gaussian.Basic.value (Dense.Gaussian.Newton.Basic.newtonCenter p center)) clearances).map _ =
        (match Newton.Search.Center.Basic.checkCenter elimination right epsilon center clearances with
        | some accepted => some accepted
        | none => if Gaussian.Basic.value
            (Dense.Gaussian.Derivative.Evaluation.derivativeEval p center) = 0 then none
          else Newton.Search.Iteration.search elimination right epsilon attempts (extraBits + 2)
            (Gaussian.Basic.value (Dense.Gaussian.Newton.Basic.newtonCenter p center)) clearances).map _
      cases first : Newton.Search.Center.Basic.checkCenter elimination left epsilon center clearances <;>
        cases second : Newton.Search.Center.Basic.checkCenter elimination right epsilon center clearances
      · dsimp only
        split
        · rfl
        · exact ih _ _
      · simp only [first, second, Option.map] at agree; cases agree
      · simp only [first, second, Option.map] at agree; cases agree
      · simpa only [first, second, Option.map] using agree
end Purelib.RootIsolation.Newton.Search.Iteration.Replay

end
