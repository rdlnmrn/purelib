module
import Purelib.Data.Rat.Fraction
public import Purelib.RootIsolation.State.WindingOne.Raw
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
public import Purelib.Polynomial.Elimination.Axis.Certificate
public import Purelib.RootIsolation.Newton.Band.Basic
import Purelib.RootIsolation.State.Raw
import Purelib.RootIsolation.State.WindingOne.Basic

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Geometry.Rational.Box.Band.Basic
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Anchor
import Purelib.Polynomial.Winding.Box.Basic

open Purelib.RootIsolation.State.WindingOne.Basic (WindingOneState)

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

section
@[expose] public section

/-!
# Constructive small-residual samples with explicit denominator height

A selected Newton band contains a point on a computable square Gaussian grid.
Coordinatewise nearest-integer rounding halves the required mesh width: the
grid denominator is one more than the integer floor of `1 / (2r)`.  This gives
an exact finite denominator certificate for the box-to-residual estimate.
-/

namespace Purelib.RootIsolation.Newton.Band.State

/-- Regard a Newton-band output as the winding-one state that it certifies. -/
def stateOfOutput
    {p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    {squarefree : Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate p}
    {current : State.Raw.RawWindingState p ambient} {epsilon : Fraction.Rational}
    (output : Newton.Band.Basic.Output squarefree current epsilon) :
    WindingOneState p ambient :=
  { box := output.box
    refinesAmbient := output.refinesAmbient
    proper := output.proper
    clearance := output.clearance
    rawWindingFour := output.rawWindingFour
    ambientLeftClearance := output.ambientLeftClearance
    ambientRightClearance := output.ambientRightClearance
    ambientBottomClearance := output.ambientBottomClearance
    ambientTopClearance := output.ambientTopClearance }
end Purelib.RootIsolation.Newton.Band.State

end

section
@[expose] public section

/-! Complete the original Newton-band and winding-state constructors around
a restored exact local extraction. No different cut or track is selected. -/
namespace Purelib.RootIsolation.Newton.Band.State
variable {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box} {degreeBound
  : Nat}
  (degreeAtLeastTwo : 2 ≤ p.natDegree) (squarefree : Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate
    p)
  (elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p degreeBound)
  (current : WindingOneState p ambient) (epsilon : Fraction.Rational) (positive : 0 < epsilon)

/-- The full state retains all four original ambient-line bounds. -/
def state (band : Newton.Band.Basic.Output squarefree current.raw
  epsilon) : WindingOneState p ambient :=
  ⟨band.box, band.refinesAmbient, band.proper, band.clearance, band.rawWindingFour,
    band.ambientLeftClearance, band.ambientRightClearance, band.ambientBottomClearance, band.ambientTopClearance⟩
end Purelib.RootIsolation.Newton.Band.State

end
