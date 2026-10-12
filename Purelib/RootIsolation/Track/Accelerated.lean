module
import Purelib.Polynomial.Dense.Gaussian.Derivative.Evaluation
import Purelib.Geometry.Rational.Box.Refinement
public import Purelib.RootIsolation.State.WindingOne.Raw
import Purelib.Polynomial.Dense.Gaussian.Newton.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Grid.Box
import Purelib.Data.Gaussian.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Clearance.Box.Line.Elimination.Provider
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Elimination.Axis.Certificate
public import Purelib.RootIsolation.Newton.Search.Attempt
import Purelib.RootIsolation.Newton.Search.Center.Basic
import Purelib.RootIsolation.Newton.Search.Iteration
import Purelib.RootIsolation.Refinement.Basic
import Purelib.RootIsolation.State.WindingOne.Basic
public import Purelib.RootIsolation.Track.Basic
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.RootIsolation.State.Raw

open Purelib.RootIsolation.Track.Basic (WindingOneTrack)

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

namespace Purelib.RootIsolation.Track.Accelerated

attribute [local irreducible] Newton.Search.Center.Basic.checkCenter Grid.Box.roundedCenter
  Gaussian.Basic.value Dense.Gaussian.Derivative.Evaluation.derivativeEval
  Dense.Gaussian.Newton.Basic.newtonCenter
attribute [local irreducible] Newton.Search.Iteration.search

/-- Preserve the existing total fallback when no shortcut is certified. -/
def refinement {p :
  Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient :
  Box} {degreeBound : Nat}
    (elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p degreeBound)
    (fallback : WindingOneTrack p ambient)
    (current : State.WindingOne.Basic.WindingOneState p ambient)
    (epsilon : Fraction.Rational) (positive : 0 < epsilon)
    (clearances : Clearance.Box.Line.Elimination.Provider.AxisClearances elimination := .canonical elimination) :
    Refinement current.raw epsilon :=
  match Newton.Search.Attempt.attempt elimination current.raw epsilon clearances with
  | some accepted => accepted
  | none =>
      { state := fallback.refine current epsilon positive
        strict := fallback.strict current epsilon positive
        accurate := fallback.accurate current epsilon positive }

/-- The accelerated track has exactly the original initial state and the
same unconditional strict-nesting and accuracy interface. -/
def accelerate {p :
  Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient :
  Box} {degreeBound : Nat}
    (elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p degreeBound)
    (fallback : WindingOneTrack p ambient)
    (clearances : Clearance.Box.Line.Elimination.Provider.AxisClearances elimination := .canonical elimination) :
    WindingOneTrack p ambient where
  initial := fallback.initial
  refine current epsilon positive :=
    (refinement elimination fallback current epsilon positive clearances).state
  nested current epsilon positive :=
    Geometry.Rational.Box.Refinement.StrictInterior.refines
      (refinement elimination fallback current epsilon positive clearances).strict
  strict current epsilon positive :=
    (refinement elimination fallback current epsilon positive clearances).strict
  accurate current epsilon positive :=
    (refinement elimination fallback current epsilon positive clearances).accurate

end Purelib.RootIsolation.Track.Accelerated

end
