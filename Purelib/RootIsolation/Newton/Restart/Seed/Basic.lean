module

public import Purelib.Polynomial.Clearance.Box.Region.Basic
public import Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Taylor
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Residual
public import Purelib.Polynomial.Dense.Gaussian.Derivative.Separation.Squarefree
public import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Anchor
public import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Band.Parameters
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
public import Purelib.Polynomial.Elimination.Axis.Band
import Purelib.Polynomial.Elimination.Axis.Certificate
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Band.Basic
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Evaluation
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Polynomial

section
public section

/-!
# Winding bands from displayed rational residuals

A sufficiently small value of a squarefree polynomial at a displayed
Gaussian-rational sample gives a finite Newton certificate.  When supplied
with explicit rational displacement, Taylor, and containment budgets, the
selected eliminant-safe band has winding four and therefore starts a normal
shrinking track.

Nothing in this module turns a small residual, a winding count, or a Sturm
count into a root.  The only distinguished point is the supplied rational
anchor of `source`.
-/

namespace Purelib.RootIsolation.Newton.Restart

set_option genInjectivity false in
/-- All finite inequalities needed to turn the rational anchor of `source`
into an eliminant-safe winding-four band strictly inside `current`. -/
structure Seed
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient :
      Purelib.Geometry.Rational.Box} {degreeBound : Nat}
    (squarefree : Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate p)
    (elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p degreeBound)
    (current : Clearance.Box.Region.ProtectedAmbient p ambient) where
  /-- The retained rational source box whose anchor supplies the sample. -/ source : Purelib.Geometry.Rational.Box
  /-- The source box refines the current protected box. -/ sourceRefines : source.Refines current.box
  /-- The source anchor's squared residual norm is bounded by its box variation budget. -/ residual :
    Data.Gaussian.Norm.Basic.normSq (p.eval source.anchor) ≤
    Dense.Gaussian.Bounds.Box.Residual.anchorResidualBound p current.box source
  /-- The source variation budget lies below the squarefree derivative threshold. -/ threshold :
    Dense.Gaussian.Bounds.Box.Residual.anchorResidualBound p current.box source ≤
    Dense.Gaussian.Derivative.Separation.Squarefree.derivativeThreshold squarefree current.box
  /-- The retained radius used to select the Newton band. -/ radius : Fraction.Rational
  /-- The retained band radius is strictly positive. -/ radiusPositive : 0 < radius
  /-- The actual residual divided by the derivative margin fits within the squared radius. -/ displacementBudget :
    Data.Gaussian.Norm.Basic.normSq (p.eval source.anchor) /
        Dense.Gaussian.Derivative.Separation.Squarefree.derivativeMargin squarefree current.box ≤ radius ^ 2
  /-- The coefficient-computed band remainder budget fits within the derivative margin. -/ taylorSmall :
    2 * (Dense.Gaussian.Newton.Box.Band.Parameters.extractionBandTaylorCoefficient *
      Dense.Gaussian.Bounds.Box.Taylor.denseTaylorRemainderBound p current.box * radius ^ 2) ≤
        Dense.Gaussian.Derivative.Separation.Squarefree.derivativeMargin squarefree current.box
  /-- The exact eliminant-selected band lies strictly inside the current protected box. -/ bandStrict :
    (Elimination.Axis.Band.selectedBand elimination (Dense.Gaussian.Newton.Box.Anchor.anchorNewtonCenter p source)
      radius
      radiusPositive).box.StrictInterior current.box

-- Preserve the original constructor certificate names of this unchanged nominal datatype.

constructive_injectivity Seed

namespace Seed.mk

end Seed.mk

end Purelib.RootIsolation.Newton.Restart

end
