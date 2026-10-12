module

import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Derivative.Separation.Basic
public import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Budget.Separated
import Purelib.Polynomial.Elimination.Axis.Certificate
import Purelib.RootIsolation.State.Raw
public import Purelib.RootIsolation.Subdivision.Raw.Request
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Bounds
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

public section

/-!
# Choice-free local Newton-square extraction

A finite raw-winding subdivision first crosses explicit residual, protected
boundary, displacement, and Taylor thresholds.  The exact rational Newton
point then centers a strictly nested winding-one square.  No root is selected
and no completed or infinite carrier is used.
-/

namespace Purelib.RootIsolation.Newton.Extraction.Separated.Source

set_option genInjectivity false in
/-- A retained raw source box meeting the original separated-Newton diagonal threshold.

The source remains indexed by the current box, its original derivative separation and clearance, and the requested
accuracy. -/
structure SeparatedSourceOutput
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (current : State.Raw.RawWindingState p ambient)
    (separation : Dense.Gaussian.Derivative.Separation.Basic.Certificate p current.box)
    (epsilon : Fraction.Rational) where
  /-- The actual refined raw-winding state inside the original current box. -/ source : State.Raw.RawWindingState p
    current.box
  /-- The retained source meets the original separated-Newton diagonal threshold. -/ diagonalSq_le :
    source.box.diagonalSq ≤
    Dense.Gaussian.Newton.Box.Budget.Separated.separatedSourceDiagonalThreshold separation current.box
      current.clearance epsilon

constructive_injectivity SeparatedSourceOutput

/-- Refine the original nonzero-winding state to its separated-Newton source threshold.

The original derivative separation and positive accuracy make the computed threshold positive, so finite raw subdivision
supplies the retained bound. -/
@[expose] def selectSeparatedSource
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box} {degreeBound :
      Nat}
    (current : State.Raw.RawWindingState p ambient) {epsilon : Fraction.Rational}
    (separation : Dense.Gaussian.Derivative.Separation.Basic.Certificate p current.box)
    (elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p degreeBound)
    (epsilonPositive : 0 < epsilon) :
    SeparatedSourceOutput current separation epsilon := by
  let initialState : State.Raw.RawWindingState p current.box :=
    { box := current.box
      refinesAmbient := Box.refines_refl current.box
      proper := current.proper
      clearance := current.clearance
      rawWinding_ne := current.rawWinding_ne }
  let threshold := Dense.Gaussian.Newton.Box.Budget.Separated.separatedSourceDiagonalThreshold separation current.box
    current.clearance epsilon
  have thresholdPositive : 0 < threshold :=
    Dense.Gaussian.Newton.Box.Budget.Separated.separatedSourceDiagonalThreshold_pos separation current.clearance
      current.proper epsilonPositive
  let source := Subdivision.Raw.Request.refineTo elimination initialState threshold
  exact
    { source := source
      diagonalSq_le := Subdivision.Raw.Request.refineTo_diagonalSq_le elimination initialState
        thresholdPositive }
end Purelib.RootIsolation.Newton.Extraction.Separated.Source

end
