module

import Purelib.Geometry.Rational.Box.Basic
public import Purelib.Polynomial.Clearance.Box.Refinement.Contracting
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Winding.Box.Basic
public import Purelib.RootIsolation.State.Raw

import Purelib.Tactic.QuotientFreeOmega
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

/-!
# Clear finite four-child subdivision grids

The original current raw-winding state indexes the retained clear four-child grid. Its child boxes and finite winding
sum remain attached to that exact source state.
-/

public section

namespace Purelib.RootIsolation.Subdivision.Raw.Grid

set_option genInjectivity false in
/-- Four clear children with exact raw additivity and uniform contraction.

The original current raw-winding state indexes the retained clear four-child grid. Its child boxes and finite winding
sum remain attached to that exact source state. -/
structure RawFourGrid
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (state : State.Raw.RawWindingState p ambient) where
  /-- The retained lower-left clear child, with its original refinement and contraction certificates. -/ lowerLeft :
    Clearance.Box.Refinement.Contracting.RawChild p ambient state.box
  /-- The retained upper-left clear child, with its original refinement and contraction certificates. -/ upperLeft :
    Clearance.Box.Refinement.Contracting.RawChild p ambient state.box
  /-- The retained lower-right clear child, with its original refinement and contraction certificates. -/ lowerRight :
    Clearance.Box.Refinement.Contracting.RawChild p ambient state.box
  /-- The retained upper-right clear child, with its original refinement and contraction certificates. -/ upperRight :
    Clearance.Box.Refinement.Contracting.RawChild p ambient state.box
  /-- The parent's quadrupled winding equals the sum of the four original retained child windings. -/ additive :
    Winding.Box.Basic.quadrupledBoxWinding p state.box =
    Winding.Box.Basic.quadrupledBoxWinding p lowerLeft.box +
      Winding.Box.Basic.quadrupledBoxWinding p upperLeft.box +
      Winding.Box.Basic.quadrupledBoxWinding p lowerRight.box +
      Winding.Box.Basic.quadrupledBoxWinding p upperRight.box

constructive_injectivity RawFourGrid

end Purelib.RootIsolation.Subdivision.Raw.Grid

end
