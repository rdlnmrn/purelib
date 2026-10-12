module
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Geometry.Projective.Chordal.Probe.Omega
import Purelib.Geometry.Projective.Line.Basic
import Purelib.Geometry.Projective.Line.Gaussian
import Purelib.Measure.Distribution.Basic

import Purelib.Tactic.QuotientFreeOmega
public import Purelib.Measure.Distribution.Moments.Basic
import Purelib.Measure.Distribution.Lp.L2
import Purelib.Measure.Distribution.Moments.Lp
import Purelib.Measure.Distribution.Expectation
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Measure.Weighted.Basic
import Purelib.Data.Rat.Fraction

section
@[expose] public section

/-!
# A nonconstant root-free CCL probe

Squared chordal distance to the distinguished projective point `omega` is an
exact rational observable on every valid homogeneous point.  Its output
separation is not naturally linear in squared chordal distance, but its
*squared* output separation is.  This supplies a concrete nonconstant probe
for the root-free L2 prefix-stability interface.
-/

namespace Purelib.Measure.Distribution.Projective.Chordal

open Purelib in
open Purelib.Data.Rat in
open Purelib.Geometry.Projective in
/-- The chordal omega probe has variance at most one when every original atom's projective point has a nonzero
coordinate. -/
theorem chordalOmegaProbe_variance_le_one {index : Type}
    (distribution : Measure.Distribution index)
    (points : index → Line.GaussianLine)
    (valid : ∀ atom, atom ∈ distribution.atoms →
      Line.Gaussian.Proj.HasNonzeroCoordinate (points atom.item)) :
    distribution.variance (fun item => Chordal.Probe.chordalOmegaProbe (points item)) ≤ 1 :=
  calc
    distribution.variance (fun item => Chordal.Probe.chordalOmegaProbe (points item)) ≤
        distribution.poweredL2
          (fun item => Chordal.Probe.chordalOmegaProbe (points item)) :=
      distribution.variance_le_poweredL2 _
    _ ≤ distribution.expectation (fun _ => 1) := by
      apply distribution.expectation_mono
      intro atom member
      have squareLe := Fraction.Order.Arithmetic.pow_le_pow_direct
        (Chordal.Probe.chordalOmegaProbe_nonnegative (points atom.item))
        (Chordal.Probe.chordalOmegaProbe_le_one (valid atom member)) 2
      simpa only [one_pow] using squareLe
    _ = 1 := distribution.expectation_constant 1
end Purelib.Measure.Distribution.Projective.Chordal

end
