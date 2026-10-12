module

import Purelib.Geometry.Rational.Box.Basic
public import Purelib.Polynomial.Clearance.Box.Boundary.Basic
public import Purelib.Polynomial.Clearance.Box.Line.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Winding.Box.Basic

import Purelib.Tactic.QuotientFreeOmega
public import Purelib.Geometry.Rational.Box.Refinement
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Geometry.Rational

open Purelib.Polynomial

/-!
# Certified winding-one states and their original nominal views

The polynomial and fixed ambient box index the retained proper subbox, its positive boundary clearance, raw winding four
and all four ambient line-clearance witnesses.
-/

public section

namespace Purelib.RootIsolation.State.WindingOne.Basic

open Purelib.RootIsolation

set_option genInjectivity false in
/-- A clear winding-one box supported in a fixed ambient box.

The polynomial and fixed ambient box index the retained proper subbox, its positive boundary clearance, raw winding four
and all four ambient line-clearance witnesses. -/
structure WindingOneState (p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) (ambient :
  Box) where
  /-- The retained rational box carrying the winding certificate. -/ box : Box
  /-- The retained box lies within the specified original ambient box. -/ refinesAmbient : box.Refines ambient
  /-- The retained box has strictly positive width and height. -/ proper : box.Proper
  /-- A positive finite boundary-clearance certificate for the original polynomial and retained box. -/ clearance :
    Clearance.Box.Boundary.Basic.BoundaryClearance p box
  /-- The original polynomial has quadrupled winding four on the retained box. -/ rawWindingFour :
    Winding.Box.Basic.quadrupledBoxWinding p box = 4
  /-- The polynomial is clear along the left vertical boundary line throughout the ambient box. -/ ambientLeftClearance
    :
    Clearance.Box.Line.Basic.VerticalLineClearance p ambient box.xLower
  /-- The polynomial is clear along the right vertical boundary line throughout the ambient box. -/
    ambientRightClearance :
    Clearance.Box.Line.Basic.VerticalLineClearance p ambient box.xUpper
  /-- The polynomial is clear along the bottom horizontal boundary line throughout the ambient box. -/
    ambientBottomClearance :
    Clearance.Box.Line.Basic.HorizontalLineClearance p ambient box.yLower
  /-- The polynomial is clear along the top horizontal boundary line throughout the ambient box. -/ ambientTopClearance
    :
    Clearance.Box.Line.Basic.HorizontalLineClearance p ambient box.yUpper

constructive_injectivity WindingOneState

end Purelib.RootIsolation.State.WindingOne.Basic

end
