module
public import Purelib.Approximation.Gaussian.Process.Imaginary.Positive.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic

public import Purelib.Approximation.Gaussian.Process.Imaginary.Separation.Basic
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order
import Purelib.Riemann.Integration.LegendreModularMonodromy
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Basic
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

/-- Forget the sign of a positive imaginary enclosure while retaining its squared separation bound. -/
def ofPositive {tau :
  Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed}
    (certificate : Positive.Basic.PositiveEnclosure tau) : Separation tau :=
  { state := certificate.state
    gap := certificate.lower
    positive := certificate.positive
    squared_lower := fun possible => Fraction.Order.Arithmetic.pow_le_pow_direct
      certificate.positive.le (certificate.inside_lower (tau.name.process.possible_inside possible)) 2 }
end Purelib.Approximation.Gaussian.Process.Imaginary.Separation

end
