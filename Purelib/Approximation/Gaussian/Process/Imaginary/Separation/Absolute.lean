module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic

public import Purelib.Approximation.Gaussian.Process.Imaginary.Separation.Basic
public import Purelib.Data.Rat.Bounds.Abs
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order
import Purelib.Riemann.Integration.LegendreModularMonodromy
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Lattice
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring
meta import Mathlib.Tactic.Linter.Lint

open Purelib.Approximation.Gaussian.Process.Imaginary

open Purelib.Data.Rat

section
@[expose] public section

/-!
# Word-denominator preparation from unsigned imaginary separation

A positive squared imaginary-coordinate gap on retained candidates suffices
for every nonzero integral row. No sign is chosen and no upper-half-plane
claim is made. The existing apartifier and fractional-composition provider
then prepare arbitrary words in either half-plane.
-/

namespace Purelib.Approximation.Gaussian.Process.Imaginary.Separation

open Purelib.Riemann.Integration.LegendreModularMonodromy
open Purelib.Data.Gaussian.Cast (integralGaussian)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic.Canonical

/-- The familiar absolute-coordinate hypothesis supplies the squared datum. -/
def ofAbsolute {tau :
  Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed}
  (state : tau.name.process.State)
    (gap : Fraction.Rational) (positive : 0 < gap)
    (lower : ∀ {value : Gaussian}, tau.name.process.Possible state value → gap ≤ Fraction.abs value.im) :
    Separation tau :=
  { state := state
    gap := gap
    positive := positive
    squared_lower := by
      intro value possible
      have square := Fraction.Order.Arithmetic.pow_le_pow_direct positive.le (lower possible) 2
      rewrite [Bounds.Abs.abs_sq_direct] at square
      exact square }
end Purelib.Approximation.Gaussian.Process.Imaginary.Separation

end
