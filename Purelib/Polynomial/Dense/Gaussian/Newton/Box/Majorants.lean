module

import Purelib.Data.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Taylor
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Geometry.Rational.Box.Bounds
public import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.GCD
import Mathlib.Order.Defs.PartialOrder
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Polynomial

section
@[expose] public section

/-!
# Choice-free local Newton-square extraction

A finite raw-winding subdivision first crosses explicit residual, protected
boundary, displacement, and Taylor thresholds.  The exact rational Newton
point then centers a strictly nested winding-one square.  No root is selected
and no completed or infinite carrier is used.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Newton.Box.Majorants

/-! ## A-priori majorants for progressive-coefficient continuation -/

set_option genInjectivity false in
/-- Finite upper bounds sufficient to run the Newton construction with a
radius and final clearance that can be bounded before the displayed
polynomial is revealed. -/
structure ExtractionMajorants (p :
  Basic.CanonicalCoefficients.CoefficientPolynomial) (ambient : Box) where
  /-- The retained upper bound for the polynomial's box Lipschitz multiplier. -/ lipschitz : Fraction.Rational
  /-- The retained Lipschitz majorant is strictly positive. -/ lipschitz_pos : 0 < lipschitz
  /-- The coefficient-computed box Lipschitz multiplier fits the retained majorant. -/ lipschitz_upper :
    Bounds.Box.denseLipschitzBound p ambient ≤ lipschitz
  /-- The retained Taylor-remainder majorant for the original polynomial and box. -/ taylor : Fraction.Rational
  /-- The retained Taylor majorant is strictly positive. -/ taylor_pos : 0 < taylor
  /-- The coefficient-computed Taylor remainder bound fits the retained majorant. -/ taylor_upper :
    Bounds.Box.Taylor.denseTaylorRemainderBound p ambient ≤ taylor
  /-- The retained uniform upper bound for derivative quadrance on the box. -/ derivative : Fraction.Rational
  /-- The retained derivative majorant is strictly positive. -/ derivative_pos : 0 < derivative
  /-- Derivative evaluation at every contained point satisfies the retained quadrance ceiling. -/ derivative_upper : ∀
    {z : Gaussian.Basic.Canonical}, ambient.Contains z →
    Gaussian.Norm.Basic.normSq ((GCD.derivative p).eval z) ≤ derivative

constructive_injectivity ExtractionMajorants

/-- The coefficient-computed bounds of one displayed polynomial, packaged as
the canonical majorants for quantitative extraction.  This constructor is
useful when no coefficient channel has to be anticipated: all three bounds
are exact finite scans of the current polynomial and box. -/
def exactExtractionMajorants (p :
  Basic.CanonicalCoefficients.CoefficientPolynomial) (ambient : Box) :
    ExtractionMajorants p ambient where
  lipschitz := Bounds.Box.denseLipschitzBound p ambient
  lipschitz_pos := Bounds.Box.denseLipschitzBound_pos p ambient
  lipschitz_upper := le_rfl
  taylor := Bounds.Box.Taylor.denseTaylorRemainderBound p ambient
  taylor_pos := Bounds.Box.Taylor.denseTaylorRemainderBound_pos p ambient
  taylor_upper := le_rfl
  derivative := Bounds.Box.denseEvalNormMajorant
    (GCD.derivative p) ambient
  derivative_pos := Bounds.Box.denseEvalNormMajorant_pos
    (GCD.derivative p) ambient
  derivative_upper := by
    intro z inside
    exact Bounds.Box.normSq_eval_le_denseEvalNormMajorant
      (GCD.derivative p) inside
end Purelib.Polynomial.Dense.Gaussian.Newton.Box.Majorants

end
