module
import Purelib.Data.Rat.Fraction
public import Purelib.Data.CCL.Encoding.Encoder.Blocks
public import Purelib.Approximation.CCL.Cylinder.Spread
import Purelib.Data.CCL.Encoding.Cylinder.Projective
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Geometry.Projective.Chordal.Probe.Omega
import Purelib.Geometry.Projective.Line.Basic
import Purelib.Measure.CCL.Cylinder.Concentration.Squared
import Purelib.Measure.Distribution.Basic

import Purelib.CCL.Measure.Basic
import Purelib.Data.GaussianInt.Basic
import Purelib.Data.GaussianInt.Fraction.Basic
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Rat.Fraction.Order
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Measure.Weighted.Basic
public import Purelib.Measure.Distribution.Moments.Basic

open Purelib.Data.GaussianInt.Fraction.Basic (SourceEncodingEncoderFracAlias)

section
@[expose] public section

/-!
# Concentration of squared-sensitive probes inside one finite CCL cylinder

For a probe satisfying a squared-separation sensitivity estimate, CCL's
`2^-k` squared-chordal cylinder contraction gives a `factor * 2^-k` second
moment bound directly.  This is the natural rate for nonconstant Lipschitz
observables and avoids selecting a square root.

Every statement concerns an explicitly supplied finite distribution and
finite realization traces.  No measure on an infinite cylinder is formed.
-/

namespace Purelib.Measure.CCL.EncodedPrefix

open Purelib in
open Purelib.Data in
open Purelib.Data.CCL.Encoding in
open Purelib.Geometry.Projective in
open Purelib.Measure in
/-- The chordal omega probe on realizations of one encoded fraction's blocks has variance at most twice that exact
cylinder spread.

The original fraction has nonzero numerator, and every retained atom point projectively realizes its exact encoder
output. -/
theorem encodedChordalOmegaProbeVariance_le {index : Type}
    (fraction : SourceEncodingEncoderFracAlias) (numeratorNonzero : fraction.numerator ≠ 0)
    (distribution : Measure.Distribution index)
    (points : index → Line.GaussianLine)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      Cylinder.Projective.ProjectiveRealizes
        (Encoder.Blocks.encodeBlocks fraction numeratorNonzero).blocks
        (points atom.item)) :
    distribution.variance (fun item => Chordal.Probe.chordalOmegaProbe (points item)) ≤
      2 * Approximation.CCL.Cylinder.cylinderSpread
        (Encoder.Blocks.encodeBlocks fraction numeratorNonzero).blocks :=
  CCL.Cylinder.projectiveRealizedChordalOmegaProbeVariance_le distribution
    (Encoder.Blocks.encodeBlocks fraction numeratorNonzero).blocks
    (Encoder.Blocks.encodeBlocks fraction numeratorNonzero).point
    (Encoder.Blocks.encodeBlocks_realizes fraction numeratorNonzero)
    points pointsRealize

end Purelib.Measure.CCL.EncodedPrefix

end

section
section
@[expose] public section

/-!
# Finite iid sampling certificates from CCL encoder cylinders

A squared-sensitive probe on one finite CCL cylinder has an explicit rational
variance budget.  Substituting that budget into the constructive Chebyshev
sample-count request yields a finite iid sample-mean deviation certificate.
For an actual encoder run, every quantity in the request is executable.
-/

namespace Purelib.Measure.CCL.EncodedPrefix

open Purelib in
open Purelib.Data in
open Purelib.Data.CCL.Encoding in
open Purelib.Data.Rat in
/-- Multiply the supplied sensitivity factor by the exact spread of the original fraction's encoded blocks. -/
def encodedProbeVarianceBudget
    (fraction : SourceEncodingEncoderFracAlias) (numeratorNonzero : fraction.numerator ≠ 0)
    (factor : Fraction.Rational) : Fraction.Rational :=
  factor * Approximation.CCL.Cylinder.cylinderSpread
    (Encoder.Blocks.encodeBlocks fraction numeratorNonzero).blocks

open Purelib in
open Purelib.Data in
open Purelib.Data.Rat in
open Purelib.Measure in
/-- The exact encoded-prefix variance budget is nonnegative when its retained sensitivity factor is nonnegative. -/
theorem encodedProbeVarianceBudget_nonnegative
    (fraction : SourceEncodingEncoderFracAlias) (numeratorNonzero : fraction.numerator ≠ 0)
    (factor : Fraction.Rational) (factorNonnegative : 0 ≤ factor) :
    0 ≤ encodedProbeVarianceBudget fraction numeratorNonzero factor :=
  Fraction.Order.Arithmetic.mul_nonneg_direct factorNonnegative
    (Approximation.CCL.Cylinder.cylinderSpread_nonneg _)
end Purelib.Measure.CCL.EncodedPrefix

end

end
