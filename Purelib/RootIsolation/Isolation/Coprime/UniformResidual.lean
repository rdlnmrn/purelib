module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Target
import Purelib.RootIsolation.State.WindingOne.Basic
public import Purelib.RootIsolation.Track.Basic
import Purelib.RootIsolation.Winding.Bounds.Residual
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Tactic.Ring

open Purelib.Data.Rat.Fraction.Order

open Purelib.Polynomial.Dense.Gaussian

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

section
public section

/-!
# Quantitative finite bounds for two coprime polynomials

This module extracts the reusable two-polynomial content of the squarefree
derivative-margin argument.  A displayed Bézout certificate gives an explicit
threshold below which a small value of the left polynomial forces a positive
lower bound for the right polynomial.  Applying the estimate to every point
of a sufficiently refined winding-one box supplies boundary clearance and
zero winding for the other polynomial.
-/

namespace Purelib.RootIsolation.Isolation.Coprime.UniformResidual

/-- Refine the original track state at the coefficient-computed uniform residual radius.

The supplied positive threshold and original ambient box determine the finite accuracy request. -/
@[expose] def uniformlySmallState
    {p : Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (track : Track.Basic.WindingOneTrack p ambient)
    (current : State.WindingOne.Basic.WindingOneState p ambient)
    (threshold : Fraction.Rational) (thresholdPositive : 0 < threshold) :
    State.WindingOne.Basic.WindingOneState p ambient :=
  track.refine current (Bounds.Box.Target.uniformResidualRadius p ambient threshold)
    (Bounds.Box.Target.uniformResidualRadius_pos p ambient thresholdPositive)

/-- Every point of an already accurate original winding-one state meets the requested residual threshold.

The state remains on its original polynomial and ambient box. Its retained
squared-diagonal certificate pays the same coefficient-computed uniform
radius, so another strict track refinement is unnecessary.
-/
public theorem residual_lt_of_accurate
    {p : Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (degreePositive : 0 < p.natDegree)
    (state : State.WindingOne.Basic.WindingOneState p ambient)
    {threshold : Fraction.Rational} (thresholdPositive : 0 < threshold)
    (diagonal : state.box.diagonalSq ≤
      (Bounds.Box.Target.uniformResidualRadius p ambient threshold) ^ 2)
    {z : Gaussian.Basic.Canonical} (inside : state.box.Contains z) :
    Gaussian.Norm.Basic.normSq (p.eval z) < threshold := by
  exact Winding.Bounds.Residual.normSq_eval_lt_of_diagonal degreePositive state
    thresholdPositive diagonal inside

/-- Every point of the retained uniform refinement has squared polynomial residual strictly below the requested
threshold.

The original polynomial must have positive degree; the radius budget controls its ambient Lipschitz bound. -/
theorem uniformlySmallState_residual_lt
    {p : Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (degreePositive : 0 < p.natDegree)
    (track : Track.Basic.WindingOneTrack p ambient)
    (current : State.WindingOne.Basic.WindingOneState p ambient)
    {threshold : Fraction.Rational} (thresholdPositive : 0 < threshold)
    {z : Gaussian.Basic.Canonical}
    (inside : (uniformlySmallState track current threshold
      thresholdPositive).box.Contains z) :
    Gaussian.Norm.Basic.normSq (p.eval z) < threshold := by
  exact Winding.Bounds.Residual.normSq_eval_lt_of_diagonal degreePositive
    (uniformlySmallState track current threshold thresholdPositive)
    thresholdPositive (track.accurate current _ _) inside
end Purelib.RootIsolation.Isolation.Coprime.UniformResidual

end
