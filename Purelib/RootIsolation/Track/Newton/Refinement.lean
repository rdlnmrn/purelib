module
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
import Purelib.Polynomial.Elimination.Axis.Certificate
public import Purelib.RootIsolation.Newton.Band.Build
import Purelib.RootIsolation.State.WindingOne.Basic
public import Purelib.RootIsolation.State.WindingOne.Raw
import Purelib.Geometry.Rational.Box.Refinement
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Band.Basic
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Anchor
import Purelib.Polynomial.Winding.Box.Basic
import Purelib.RootIsolation.Newton.Band.Basic
import Purelib.RootIsolation.State.Raw

open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic (SquarefreeCertificate)
open Purelib.Polynomial.Elimination.Axis.Certificate.AxisSafeCuts (AxisEliminationCertificate)
open Purelib.RootIsolation.State.WindingOne.Basic (WindingOneState)

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

section
@[expose] public section

/-!
# Choice-free shrinking winding-one tracks

The local Newton-square extractor is stable under iteration because every
returned square carries a new finite boundary-clearance certificate.  This
module packages those repeated finite calls as the numerical track interface
used by box isolation and any independently shrinking finite envelope.
-/

namespace Purelib.RootIsolation.Track.Newton.Refinement

/-- One requested-accuracy refinement of a winding-one state. -/
def refineState
    {p : CoefficientPolynomial} {ambient : Box} {degreeBound :
      Nat}
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (squarefree : SquarefreeCertificate p)
    (elimination : AxisEliminationCertificate p degreeBound)
    (current : WindingOneState p ambient)
    (epsilon : Fraction.Rational) (positive : 0 < epsilon) :
    WindingOneState p ambient := by
  let extracted := Newton.Band.Build.extract degreeAtLeastTwo
    squarefree elimination current.raw positive
  exact
    { box := extracted.box
      refinesAmbient := extracted.refinesAmbient
      proper := extracted.proper
      clearance := extracted.clearance
      rawWindingFour := extracted.rawWindingFour
      ambientLeftClearance := extracted.ambientLeftClearance
      ambientRightClearance := extracted.ambientRightClearance
      ambientBottomClearance := extracted.ambientBottomClearance
      ambientTopClearance := extracted.ambientTopClearance }

/-- The requested Newton refinement remains inside the original winding-one state box. -/
theorem refineState_refines
    {p : CoefficientPolynomial} {ambient : Box} {degreeBound :
      Nat}
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (squarefree : SquarefreeCertificate p)
    (elimination : AxisEliminationCertificate p degreeBound)
    (current : WindingOneState p ambient)
    (epsilon : Fraction.Rational) (positive : 0 < epsilon) :
    (refineState degreeAtLeastTwo squarefree elimination current epsilon
      positive).box.Refines current.box := by
  exact Geometry.Rational.Box.Refinement.StrictInterior.refines
    (Newton.Band.Build.extract degreeAtLeastTwo squarefree
      elimination current.raw positive).strictCurrent

/-- The requested Newton refinement lies strictly inside the original winding-one state box. -/
theorem refineState_strict
    {p : CoefficientPolynomial} {ambient : Box} {degreeBound :
      Nat}
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (squarefree : SquarefreeCertificate p)
    (elimination : AxisEliminationCertificate p degreeBound)
    (current : WindingOneState p ambient)
    (epsilon : Fraction.Rational) (positive : 0 < epsilon) :
    (refineState degreeAtLeastTwo squarefree elimination current epsilon
      positive).box.StrictInterior current.box := by
  exact (Newton.Band.Build.extract degreeAtLeastTwo squarefree
    elimination current.raw positive).strictCurrent

/-- The requested Newton refinement meets the original positive squared-diagonal accuracy bound. -/
theorem refineState_accurate
    {p : CoefficientPolynomial} {ambient : Box} {degreeBound :
      Nat}
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (squarefree : SquarefreeCertificate p)
    (elimination : AxisEliminationCertificate p degreeBound)
    (current : WindingOneState p ambient)
    (epsilon : Fraction.Rational) (positive : 0 < epsilon) :
    (refineState degreeAtLeastTwo squarefree elimination current epsilon
      positive).box.diagonalSq ≤ epsilon ^ 2 := by
  exact (Newton.Band.Build.extract degreeAtLeastTwo squarefree
    elimination current.raw positive).diagonalSq_le
end Purelib.RootIsolation.Track.Newton.Refinement

end
