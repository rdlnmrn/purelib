module

import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.RootIsolation.State.WindingOne.Basic

import Purelib.Tactic.QuotientFreeOmega
public import Purelib.Geometry.Rational.Box.Bounds
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Refinement
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

/-!
# Shrinking winding-one tracks and their original nominal views

The polynomial and ambient box index the retained initial winding-one state and refinement operation. Each positive
accuracy request carries nestedness, strict interior and squared-diagonal bounds.
-/

public section

namespace Purelib.RootIsolation.Track.Basic

set_option genInjectivity false in
/-- A total finite shrinking track, with strict nesting available in addition
to ordinary nesting and the displayed squared-diagonal request.

The polynomial and ambient box index the retained initial winding-one state and refinement operation. Each positive
accuracy request carries nestedness, strict interior and squared-diagonal bounds. -/
structure WindingOneTrack (p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) (ambient :
  Box) where
  /-- The retained initial winding-one state. -/ initial : State.WindingOne.Basic.WindingOneState p ambient
  /-- Refine any supplied winding-one state to a positive rational accuracy request. -/ refine : (current :
    State.WindingOne.Basic.WindingOneState p ambient) →
    (epsilon : Fraction.Rational) → 0 < epsilon → State.WindingOne.Basic.WindingOneState p ambient
  /-- The refined box lies within the exact preceding box. -/ nested : ∀ current epsilon positive,
    (refine current epsilon positive).box.Refines current.box
  /-- The refined box lies strictly inside the exact preceding box. -/ strict : ∀ current epsilon positive,
    (refine current epsilon positive).box.StrictInterior current.box
  /-- The refined box's squared diagonal is at most the squared requested accuracy. -/ accurate : ∀ current epsilon
    positive,
    (refine current epsilon positive).box.diagonalSq ≤ epsilon ^ 2

constructive_injectivity WindingOneTrack

end Purelib.RootIsolation.Track.Basic

end
