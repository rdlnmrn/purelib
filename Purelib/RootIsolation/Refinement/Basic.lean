module

import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.RootIsolation.State.Raw
public import Purelib.RootIsolation.State.WindingOne.Basic
public import Purelib.Geometry.Rational.Box.Bounds
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Refinement
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

public section

namespace Purelib.RootIsolation

set_option genInjectivity false in
/-- Cached successful refinement with every numerical track obligation.

The original raw-winding current state and rational accuracy request index the retained winding-one result, its strict
interior witness and its squared-diagonal bound. -/
structure Refinement {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (current : State.Raw.RawWindingState p ambient) (epsilon : Fraction.Rational) where
  /-- The retained successful winding-one state for the original polynomial and ambient box. -/ state :
    State.WindingOne.Basic.WindingOneState p ambient
  /-- The retained state box lies strictly inside the input state box. -/ strict : state.box.StrictInterior current.box
  /-- The retained state's squared diagonal meets the requested squared accuracy. -/ accurate : state.box.diagonalSq ≤
    epsilon ^ 2

constructive_injectivity Refinement

namespace Refinement.mk

end Refinement.mk

end Purelib.RootIsolation

end
