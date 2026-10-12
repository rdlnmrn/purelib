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
import Purelib.RootIsolation.Refinement.Basic
import Purelib.RootIsolation.State.Raw
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.RootIsolation.State.WindingOne.Basic

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

namespace Purelib.RootIsolation.Newton.Search.Attempt

attribute [local irreducible] Newton.Search.Center.Basic.checkCenter Grid.Box.roundedCenter
  Gaussian.Basic.value Dense.Gaussian.Derivative.Evaluation.derivativeEval
  Dense.Gaussian.Newton.Basic.newtonCenter
attribute [local irreducible] Newton.Search.Iteration.search

/-- Start a bounded search at the midpoint of the current box. -/
def attempt {p :
  Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient :
  Box} {degreeBound : Nat}
    (elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p degreeBound)
    (current : State.Raw.RawWindingState p ambient) (epsilon : Fraction.Rational)
    (clearances : Clearance.Box.Line.Elimination.Provider.AxisClearances elimination := .canonical elimination) :
    Option (Refinement current epsilon) :=
  Newton.Search.Iteration.search elimination current epsilon 6 0
    ⟨(current.box.xLower + current.box.xUpper) / 2,
      (current.box.yLower + current.box.yUpper) / 2⟩ clearances

/-- The standard six-proposal attempt has clearance-independent geometry. -/
theorem attempt_box_eq {p :
  Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
  {ambient : Box} {degreeBound : Nat}
    (elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p degreeBound)
    (current : State.Raw.RawWindingState p ambient) (epsilon : Fraction.Rational)
    (left right : Clearance.Box.Line.Elimination.Provider.AxisClearances elimination) :
    (attempt elimination current epsilon left).map (fun result => result.state.box) =
      (attempt elimination current epsilon right).map (fun result => result.state.box) :=
  Newton.Search.Iteration.search_box_eq elimination current epsilon 6 0 _ left right
end Purelib.RootIsolation.Newton.Search.Attempt

end
