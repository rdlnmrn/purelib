module
import Purelib.Polynomial.Elimination.Axis.Certificate
import Purelib.Geometry.Rational.Box.Basic
public import Purelib.Polynomial.Clearance.Box.Grid.Four.Basic
public import Purelib.Polynomial.Clearance.Box.Line.Bezout
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Path.Axis
public import Purelib.Polynomial.Elimination.Axis.Cuts
import Purelib.Data.Gaussian.Cast
import Purelib.Data.Gaussian.Cast.Imaginary
import Purelib.Data.Gaussian.Constants
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Path.Components
import Purelib.Polynomial.Dense.Rational.Bezout.Basic

open Purelib.Geometry.Rational

open Purelib.Polynomial

section
/-!
# Constructive eliminant-certified axis cuts

This module isolates the finite interface required from axis elimination: two
displayed nonzero bounded-degree coordinate polynomials, plus a finite Bézout
certificate whenever one evaluates nonzero.  The bounded candidate scan then
computes clear vertical and horizontal cuts and packages the resulting four
clear children.
-/

@[expose] public section

namespace Purelib.Polynomial.Clearance.Box.Grid.Four.Elimination

/-- Execute both bounded searches and obtain the two quantitative clear lines. -/
def buildClearFourGrid {p :
  Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {degreeBound : Nat}
    (elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p degreeBound) (parent :
      Box)
    (proper : parent.Proper) : Clearance.Box.Grid.Four.Basic.ClearFourGrid p parent := by
  let xCut := Elimination.Axis.Cuts.verticalSafeCoordinate elimination parent proper
  let yCut := Elimination.Axis.Cuts.horizontalSafeCoordinate elimination parent proper
  have xSpec := Elimination.Axis.Cuts.verticalSafeCoordinate_spec elimination parent proper
  have ySpec := Elimination.Axis.Cuts.horizontalSafeCoordinate_spec elimination parent proper
  let verticalCoprime := elimination.vertical_coprime xCut xSpec.1
  let horizontalCoprime := elimination.horizontal_coprime yCut ySpec.1
  exact
    { xCut := xCut
      yCut := yCut
      xInside := ⟨xSpec.2.1.le, xSpec.2.2.le⟩
      yInside := ⟨ySpec.2.1.le, ySpec.2.2.le⟩
      verticalClearance := by
        simpa only [Dense.Gaussian.Path.Axis.verticalPathReal, Dense.Gaussian.Path.Axis.verticalPathImag] using
          Clearance.Box.Line.Bezout.verticalOfCoprime p parent xCut verticalCoprime
      horizontalClearance := by
        simpa only [Dense.Gaussian.Path.Axis.horizontalPathReal, Dense.Gaussian.Path.Axis.horizontalPathImag] using
          Clearance.Box.Line.Bezout.horizontalOfCoprime p parent yCut horizontalCoprime }

end Purelib.Polynomial.Clearance.Box.Grid.Four.Elimination

end
