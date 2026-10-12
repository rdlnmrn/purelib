module

import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Budget.Squarefree
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
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

/-!
# Finite source selection for Newton extraction

The original raw-winding state is refined once to its computed squarefree
source threshold. The selected state and its quantitative certificate remain
indexed by the original current box and accuracy request.
-/

namespace Purelib.RootIsolation.Newton.Extraction.Source

set_option genInjectivity false in
/-- The retained finite raw-winding source at the requested Newton threshold.

The source is indexed by the original squarefree certificate, current state
and accuracy request. Its actual refined box remains on the original
current box and carries its squared-diagonal threshold certificate. -/
public structure SourceOutput
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (squarefree : Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate p)
    (current : State.Raw.RawWindingState p ambient) (epsilon : Fraction.Rational) where
  /-- The actual refined raw-winding state inside the original current box. -/ source : State.Raw.RawWindingState p
    current.box
  /-- The retained source meets the squarefree Newton threshold computed from the original current clearance and
    request. -/ diagonalSq_le : source.box.diagonalSq ≤
    Dense.Gaussian.Newton.Box.Budget.Squarefree.sourceDiagonalThreshold squarefree current.box current.clearance epsilon

constructive_injectivity SourceOutput

/-- Select the retained raw-winding source with the complete Newton threshold.

The original current box becomes the ambient of one finite raw-subdivision
request. The computed squarefree threshold, positive request and returned
source are retained with their original diagonal-bound certificate. -/
@[expose] public def selectSource
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box} {degreeBound :
      Nat}
    (squarefree : Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate p)
    (elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p degreeBound)
    (current : State.Raw.RawWindingState p ambient) {epsilon : Fraction.Rational}
    (epsilonPositive : 0 < epsilon) :
    SourceOutput squarefree current epsilon := by
  let initialState : State.Raw.RawWindingState p current.box :=
    { box := current.box
      refinesAmbient := Box.refines_refl current.box
      proper := current.proper
      clearance := current.clearance
      rawWinding_ne := current.rawWinding_ne }
  let threshold := Dense.Gaussian.Newton.Box.Budget.Squarefree.sourceDiagonalThreshold squarefree current.box
    current.clearance epsilon
  have thresholdPositive : 0 < threshold :=
    Dense.Gaussian.Newton.Box.Budget.Squarefree.sourceDiagonalThreshold_pos squarefree current.clearance current.proper
      epsilonPositive
  let source := Subdivision.Raw.Request.refineTo elimination initialState threshold
  exact
    { source := source
      diagonalSq_le := Subdivision.Raw.Request.refineTo_diagonalSq_le elimination initialState
        thresholdPositive }

end Purelib.RootIsolation.Newton.Extraction.Source
