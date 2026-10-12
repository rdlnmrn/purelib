module
import Purelib.Data.Gaussian.Basic
import Purelib.Approximation.Gaussian.Enclosure.Ball.Apart
import Purelib.Approximation.Gaussian.Enclosure.Residual
public import Purelib.Approximation.Gaussian.Process.Basic
public import Purelib.Data.CCL.Encoding.Padding.Residual
public import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Projective.Chordal.DyadicTail
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic

section
@[expose] public section

/-!
# Finite arithmetic output decisions

This module joins progressive finite enclosures to the two overlapping CCL
decisions.  A normalized loop process can always refine once to the uniform
`1/480` squared-error threshold and then emit either a sound unary digit or a
sound redundant sector.  A residual process can always refine once to the
requested padding threshold and then return either a sound small-residual
certificate or positive apartness for affine inversion.

Both constructions are ordinary finite function calls.  In particular, the
residual construction does not ask whether the represented result is exactly
zero.  Repeating it at successively smaller finite padding targets is the
constructive non-return route for an opaque exact rational result.
-/

namespace Purelib.Data.CCL.Encoding.Padding.Process

/-! ## Residual padding or inversion -/

section
open Purelib
open Purelib.Data.CCL.Encoding
open Purelib.Data.Rat in
/-- Refine the retained Gaussian process state to radius-squared accuracy paddingTarget divided by six. -/
def residualState (process :
  Approximation.Gaussian.Process) (state : process.State) (count : Nat) :
    process.State :=
  let target := Padding.Residual.paddingTarget count
  process.refine state (target / 6)
    (Fraction.Order.Field.div_pos_direct
      (Padding.Residual.paddingTarget_pos count) (by decide))

/-- The exact refined residual state's enclosure radius squared is below paddingTarget divided by six. -/
theorem residual_accurate (process :
  Approximation.Gaussian.Process) (state : process.State)
    (count : Nat) :
    (process.ball (residualState process state count)).radiusSq <
      Padding.Residual.paddingTarget count / 6 :=
  process.accurate state _ _

/-- Decide whether the exact refined residual enclosure is small or apart using the retained accuracy certificate.

The refinement, target positivity and radius bound belong to the same supplied process, state and requested padding
count. The result retains the certified residual decision for that exact ball. -/
def decideResidual (process :
  Approximation.Gaussian.Process) (state : process.State) (count : Nat) :
    Approximation.Gaussian.Enclosure.Residual.Decision
      (process.ball (residualState process state count))
      (Padding.Residual.paddingTarget count) :=
  Approximation.Gaussian.Enclosure.Residual.decide _ _
    (Padding.Residual.paddingTarget_pos count)
    (residual_accurate process state count)

section
open Purelib.Data.Gaussian
/-- Every value possible at the refined residual state was possible at its retained source state. -/
theorem residual_persists (process :
  Approximation.Gaussian.Process) (state : process.State)
    (count : Nat) {value : Basic.Canonical}
    (possible : process.Possible (residualState process state count) value) :
    process.Possible state value :=
  process.refine_persists state _ _ possible

/-- A retained small-ball certificate bounds every possible refined residual's squared norm by the exact padding target.
-/
theorem residual_small_sound (process :
  Approximation.Gaussian.Process) (state : process.State)
    (count : Nat)
    (certificate : Approximation.Gaussian.Enclosure.Residual.SmallBall
      (process.ball (residualState process state count))
      (Padding.Residual.paddingTarget count))
    {value : Basic.Canonical}
    (possible : process.Possible (residualState process state count) value) :
    Data.Gaussian.Norm.Basic.normSq value < Padding.Residual.paddingTarget count :=
  Approximation.Gaussian.Enclosure.Residual.normSq_lt_of_contains certificate
    (process.possible_inside possible)

/-- A retained apartness certificate bounds every possible refined residual's squared norm below by its stored positive
lower bound. -/
theorem residual_apart_sound (process :
  Approximation.Gaussian.Process) (state : process.State)
    (count : Nat)
    (certificate : Approximation.Gaussian.Enclosure.Ball.Apart
      (process.ball (residualState process state count)))
    {value : Basic.Canonical}
    (possible : process.Possible (residualState process state count) value) :
    certificate.lowerSq ≤ Data.Gaussian.Norm.Basic.normSq value :=
  certificate.lower (process.possible_inside possible)

end

open Purelib.Data.Gaussian in
open Purelib.Geometry.Projective in
/-- Construct a dyadic loop tail from the exact possible residual and its retained small-ball certificate. -/
def loopTailOfResidualSmall (process :
  Approximation.Gaussian.Process) (state : process.State)
    (count : Nat)
    (certificate : Approximation.Gaussian.Enclosure.Residual.SmallBall
      (process.ball (residualState process state count))
      (Padding.Residual.paddingTarget count))
    (value : Basic.Canonical)
    (possible : process.Possible (residualState process state count) value) :
    Chordal.DyadicTail.LoopTail count :=
  Padding.Residual.loopTailOfSmall certificate value
    (process.possible_inside possible)

end

end Purelib.Data.CCL.Encoding.Padding.Process

end
