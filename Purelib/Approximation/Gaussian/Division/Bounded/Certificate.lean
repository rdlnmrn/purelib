module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic
public import Purelib.Approximation.Gaussian.Enclosure.Residual
import Purelib.Approximation.Gaussian.Name.Coherent
public import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.Small
import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.State
import Purelib.Data.Rat.Fraction

import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Process.Basic

open Purelib.Approximation.Gaussian.Enclosure

open Purelib.Approximation.Gaussian.Name

open Purelib.Approximation.Gaussian.Name.Coherent.Refinement

open Purelib.Data.Rat

section
@[expose] public section

/-!
# Evidence-directed division with reusable state

The dispatcher first reuses an exact decision, then tries inferred finite
provenance, then an optional proved candidate gap, and finally one bounded
numerical request. A small result is inconclusive, not zero. Gap exclusion
is explicitly scoped to the retained branch. Exact provenance concerns
operational identities and is never used as a pointwise candidate gap.

All routes return the retained state. Requested refinements preserve the
retry index and transport optional gap evidence. Exact decisions, including
negative ones, are cached for subsequent numerators and requests.
-/

namespace Purelib.Approximation.Gaussian.Division.Bounded.Certificate

open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)

set_option genInjectivity false in
/-- Cache the inspected ball as well as its persistent candidate bound. -/
structure SmallCertificate (channel :
  Coherent.CoherentNamed) (state : Approximation.Gaussian.Name.Coherent.Refinement.State channel) (threshold :
      Fraction.Rational) where
  /-- The cached ball of the retained original channel state. -/ ball : Approximation.Gaussian.Enclosure.Ball
  /-- The cache equals the original channel's enclosure at its retained source. -/ ball_eq : ball =
    channel.name.process.ball state.source
  /-- Every point of the cached ball satisfies the displayed smallness test. -/ whole_ball : Residual.SmallBall ball
    threshold
  /-- The persistent strict candidate bound for the same original channel state and threshold. -/ candidates :
    Approximation.Gaussian.Name.Coherent.Refinement.Small channel state threshold

constructive_injectivity SmallCertificate

end Purelib.Approximation.Gaussian.Division.Bounded.Certificate

end
