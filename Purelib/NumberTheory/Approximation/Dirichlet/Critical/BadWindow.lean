module
import Purelib.Data.Rat.Fraction
import Purelib.NumberTheory.Approximation.Dirichlet.Critical.Pair
public import Purelib.NumberTheory.Approximation.Dirichlet.Critical.Sharpness
public import Purelib.NumberTheory.Approximation.Dirichlet.Sharpness.BadWindow
import Purelib.Data.GaussianInt.Fraction.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.NumberTheory.Approximation.Best.Error
import Purelib.NumberTheory.Approximation.Dirichlet.Window.SourceBound

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

namespace Purelib.NumberTheory.Approximation.Dirichlet.Critical.BadWindow

/-- The existing Pell construction, repackaged as explicit bad-window data. -/
def criticalBadWindow {threshold :
  Fraction.Rational}
    (certificate : Dirichlet.Critical.Sharpness.IsSharperWindowThreshold threshold)
    (requestedScale : Nat) : Dirichlet.Sharpness.BadWindow threshold requestedScale := by
  let stage := Dirichlet.Critical.Sharpness.sharpnessStage
    threshold requestedScale
  exact
    { source := Dirichlet.Critical.Pair.criticalSource stage
      lower := Dirichlet.Critical.Pair.criticalLowerPair stage
      upper := Dirichlet.Critical.Pair.criticalUpperPair stage
      beyondScale := by
        simpa only [stage] using
          Dirichlet.Critical.Sharpness.requestedScale_lt_criticalUpperDenominatorQuadrance
            threshold requestedScale
      consecutive :=
        Dirichlet.Critical.Pair.criticalPairs_areConsecutiveBest stage
      violates := by
        simpa only [stage] using
          Dirichlet.Critical.Sharpness.one_lt_sharperThreshold_mul_criticalWindow
            certificate requestedScale }

end Purelib.NumberTheory.Approximation.Dirichlet.Critical.BadWindow

end
