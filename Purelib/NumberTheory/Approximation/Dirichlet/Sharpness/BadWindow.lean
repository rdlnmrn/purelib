module

import Purelib.Data.GaussianInt.Pair.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.GaussianInt.Fraction.Basic
import Purelib.NumberTheory.Approximation.Best.Consecutive.Basic
import Purelib.NumberTheory.Approximation.Best.Error
public import Purelib.NumberTheory.Approximation.Dirichlet.Window.SourceBound
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Data

open Purelib.Data.Rat

open Purelib.NumberTheory.Approximation

section
@[expose] public section

/-!
# Finite dynamical Dirichlet-window sharpness

This module states the finite dynamical interface needed for a constructive
analogue of Chevallier's almost-everywhere sharpness argument.  A bad window
contains a displayed rational source, two displayed Gaussian-integral pairs,
their consecutive-best certificate, a strict scale inequality, and the
failure of a proposed sharper threshold.

A Boolean region in an arbitrary finite dynamical state space is sound when
every selected state constructs such a bad window.  The finite stationary
occupation and uniform block-return theorems then give quantitative lower
probabilities of reaching a sound region after a supplied finite burn-in.
No completed complex input, infinite minimal-vector sequence, Haar space,
limit, or ergodic theorem is introduced here.
-/

namespace Purelib.NumberTheory.Approximation.Dirichlet.Sharpness

set_option genInjectivity false in
/-- Fully displayed counterexample to one proposed sharper Dirichlet-window
threshold beyond one supplied natural scale. -/
structure BadWindow (threshold :
  Fraction.Rational) (requestedScale : Nat) where
  /-- The exact rational Gaussian source at which the window inequality fails. -/ source : GaussianInt.Fraction
  /-- The retained lower endpoint pair of the bad window. -/ lower : GaussianInt.Pair.Basic.ConvergentPair
  /-- The retained upper endpoint pair of the bad window. -/ upper : GaussianInt.Pair.Basic.ConvergentPair
  /-- The upper endpoint denominator quadrance exceeds the requested scale. -/ beyondScale : requestedScale <
    Best.Error.denominatorQuadrance upper
  /-- The retained endpoints are consecutive best approximations at the retained source. -/ consecutive :
    Best.Consecutive.Basic.AreConsecutiveBest source.value lower upper
  /-- The proposed threshold times this window quadrance is strictly greater than one. -/ violates : 1 < threshold *
    Dirichlet.Window.SourceBound.dirichletWindowQuadrance source.value lower upper

constructive_injectivity BadWindow

namespace BadWindow.mk

end BadWindow.mk

namespace BadWindow.mk

end BadWindow.mk

end Purelib.NumberTheory.Approximation.Dirichlet.Sharpness

end
