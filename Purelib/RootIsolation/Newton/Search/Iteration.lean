module
import Purelib.Polynomial.Dense.Gaussian.Derivative.Evaluation
public import Purelib.Polynomial.Dense.Gaussian.Newton.Basic
import Purelib.Data.Rat.Fraction
public import Purelib.Approximation.Gaussian.Grid.Box
import Purelib.Data.Gaussian.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Clearance.Box.Line.Elimination.Provider
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Elimination.Axis.Certificate
public import Purelib.RootIsolation.Newton.Search.Center.Basic
import Purelib.RootIsolation.Refinement.Basic
import Purelib.RootIsolation.State.Raw
import Purelib.RootIsolation.State.WindingOne.Basic

open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Polynomial.Clearance.Box.Line.Elimination.Provider (AxisClearances)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Polynomial.Elimination.Axis.Certificate.AxisSafeCuts (AxisEliminationCertificate)
open Purelib.RootIsolation.State.Raw (RawWindingState)

open Purelib.Approximation.Gaussian

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

section
@[expose] public section

/-!
# Checked shortcuts for winding-one refinement

Newton iteration supplies candidates, not a convergence assumption.  A
candidate is accepted only after exact finite checks of strict containment,
the requested diagonal bound and winding four.  Eliminant-safe sides supply
the same ambient and boundary clearances as the total extractor.  A bounded
unsuccessful search delegates to the original total track.
-/

namespace Purelib.RootIsolation.Newton.Search.Iteration

/-- A finite speculative search.  Round every proposal before checking and
before its next Newton update, so exact Newton denominators do not accumulate
across successful track refinements.  A rejected candidate receives two more
grid bits, avoiding stagnation at the same rounded point.  Vanishing
derivatives reject the shortcut; they do not affect the enclosing totality. -/
def search {p :
  CoefficientPolynomial} {ambient :
  Box} {degreeBound : Nat}
    (elimination : AxisEliminationCertificate p degreeBound)
    (current : RawWindingState p ambient) (epsilon : Fraction.Rational)
    (attempts extraBits : Nat) (proposal : Canonical)
    (clearances : AxisClearances elimination := .canonical elimination) :
    Option (Refinement current epsilon) :=
  match attempts with
  | 0 => none
  | attempts + 1 =>
      let center := Grid.Box.roundedCenter current.box epsilon extraBits proposal
      match Newton.Search.Center.Basic.checkCenter elimination current epsilon center clearances with
      | some accepted => some accepted
      | none =>
          if Gaussian.Basic.value
              (Dense.Gaussian.Derivative.Evaluation.derivativeEval p center) = 0 then none
          else search elimination current epsilon attempts (extraBits + 2)
            (Gaussian.Basic.value
              (Dense.Gaussian.Newton.Basic.newtonCenter p center)) clearances
termination_by structural attempts

-- Equation proofs compare the shared checks, without executing their
-- polynomial and winding implementations on symbolic arguments.
attribute [local irreducible] Newton.Search.Center.Basic.checkCenter Grid.Box.roundedCenter
  Gaussian.Basic.value Dense.Gaussian.Derivative.Evaluation.derivativeEval
  Dense.Gaussian.Newton.Basic.newtonCenter

/-- A speculative search with no remaining attempts returns no accepted refinement. -/
@[simp] theorem search_zero {p :
  CoefficientPolynomial} {ambient : Box} {degreeBound : Nat}
    (elimination : AxisEliminationCertificate p degreeBound)
    (current : RawWindingState p ambient) (epsilon : Fraction.Rational)
    (extraBits : Nat) (proposal : Canonical) (clearances :
      AxisClearances elimination) :
    search elimination current epsilon 0 extraBits proposal clearances = none := rfl

/-- One search attempt checks the rounded proposal, then either accepts it or continues the original Newton update with
two additional grid bits. -/
theorem search_succ {p :
  CoefficientPolynomial}
  {ambient : Box} {degreeBound : Nat}
    (elimination : AxisEliminationCertificate p degreeBound)
    (current : RawWindingState p ambient) (epsilon : Fraction.Rational)
    (attempts extraBits : Nat) (proposal : Canonical) (clearances :
      AxisClearances elimination) :
    search elimination current epsilon (attempts + 1) extraBits proposal clearances =
      (let center := Grid.Box.roundedCenter current.box epsilon extraBits proposal
       match Newton.Search.Center.Basic.checkCenter elimination current epsilon center clearances with
       | some accepted => some accepted
       | none => if Gaussian.Basic.value
           (Dense.Gaussian.Derivative.Evaluation.derivativeEval p center) = 0 then none
         else search elimination current epsilon attempts (extraBits + 2)
           (Gaussian.Basic.value (Dense.Gaussian.Newton.Basic.newtonCenter p center)) clearances) := rfl

-- Keep proof elaboration at the checked-call boundary.  Its winding and
-- clearance implementations need not be normalized during induction.
attribute [local irreducible] search

/-- Every finite search preserves its accepted geometry when only the
certified clearance constructor changes.  Rejection follows the same next
rounded Newton proposal in both executions. -/
theorem search_box_eq {p :
  CoefficientPolynomial}
  {ambient : Box} {degreeBound : Nat}
    (elimination : AxisEliminationCertificate p degreeBound)
    (current : RawWindingState p ambient) (epsilon : Fraction.Rational)
    (attempts extraBits : Nat) (proposal : Canonical) (left right :
      AxisClearances elimination) :
    (search elimination current epsilon attempts extraBits proposal left).map (fun result =>
      result.state.box) =
      (search elimination current epsilon attempts extraBits proposal right).map (fun result =>
        result.state.box) := by
  induction attempts generalizing extraBits proposal with
  | zero => rw [search_zero, search_zero]
  | succ attempts ih =>
      let center := Grid.Box.roundedCenter current.box epsilon extraBits proposal
      have agree := Newton.Search.Center.Basic.checkCenter_box_eq elimination current epsilon center left right
      rw [search_succ, search_succ]
      change (match Newton.Search.Center.Basic.checkCenter elimination current epsilon center left with
        | some accepted => some accepted
        | none => if Gaussian.Basic.value
            (Dense.Gaussian.Derivative.Evaluation.derivativeEval p center) = 0 then none
          else search elimination current epsilon attempts (extraBits + 2)
            (Gaussian.Basic.value (Dense.Gaussian.Newton.Basic.newtonCenter p center)) left).map _ =
        (match Newton.Search.Center.Basic.checkCenter elimination current epsilon center right with
        | some accepted => some accepted
        | none => if Gaussian.Basic.value
            (Dense.Gaussian.Derivative.Evaluation.derivativeEval p center) = 0 then none
          else search elimination current epsilon attempts (extraBits + 2)
            (Gaussian.Basic.value (Dense.Gaussian.Newton.Basic.newtonCenter p center)) right).map _
      cases leftResult : Newton.Search.Center.Basic.checkCenter elimination current epsilon center left <;>
        cases rightResult : Newton.Search.Center.Basic.checkCenter elimination current epsilon center right
      · dsimp only
        split
        · rfl
        · exact ih _ _
      · simp only [leftResult, rightResult, Option.map] at agree
        cases agree
      · simp only [leftResult, rightResult, Option.map] at agree
        cases agree
      · simpa only [leftResult, rightResult, Option.map] using agree
end Purelib.RootIsolation.Newton.Search.Iteration

end
