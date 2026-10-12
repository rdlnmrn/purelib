module
import Purelib.Data.CCL.Encoding.Encoder.Blocks
import Purelib.Data.GaussianInt.Fraction.Basic
public import Purelib.Approximation.CCL.Prefix.ProjectiveObservation
import Purelib.Approximation.Rational.Budget.Dyadic
import Purelib.Data.Rat.Interval.Basic
import Purelib.Geometry.Projective.Chordal.Basic
import Purelib.Measure.Distribution.Basic

public import Purelib.CCL.Measure.Basic
import Purelib.Data.CCL.Encoding.Cylinder.Certificate
import Purelib.Data.Rat.Distance.Basic
import Purelib.Geometry.Projective.Chordal.Probe.Sensitivity
import Purelib.Geometry.Projective.Line.Basic
public import Purelib.Measure.Distribution.Kernel.Basic
import Mathlib.Order.Basic
import Mathlib.Order.Defs.PartialOrder
import Purelib.Data.CCL.Encoding.Block.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.GaussianInt.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib.Data.GaussianInt.Fraction.Basic (SourceEncodingEncoderFracAlias)

open Purelib

open Purelib.Approximation.CCL

open Purelib.Approximation.Rational

open Purelib.Data

open Purelib.Data.CCL.Encoding

open Purelib.Data.CCL.Encoding.Encoder

open Purelib.Data.GaussianInt hiding Coordinate

open Purelib.Data.Rat

open Purelib.Geometry.Projective

open Purelib.Geometry.Projective.Chordal

open Purelib.Geometry.Projective.Line

open Purelib.Geometry.Projective.Line.Basic

section
@[expose] public section

/-!
# Finite measure certificates emitted by the executable CCL encoder

This module is the concrete bridge from `Purelib.CCL.Encoding.Encoder.encodeBlocks` to the
projectively rescaled prefix-measure facade.  It packages each finite encoder
result as an inhabited rational enclosure and lifts a finite input table to a
finite expectation enclosure.

The reconstructed affine input is used only through the encoder's explicit
finite projective-equivalence proof.  No quotient representative is chosen.
-/

namespace Purelib.Approximation.CCL.EncodedPrefix

open Purelib.CCL.Measure (Coordinate)

/-- Rational probe enclosure attached directly to one finite encoder run. -/
def encodedProjectivePrefixProbeBound
    (fraction : SourceEncodingEncoderFracAlias)
    (numeratorNonzero : fraction.numerator ≠ 0)
    (probe : GaussianLine → Coordinate) (factor : Coordinate)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        factor * Chordal.Basic.chordalSq left right) :
    Rat.Interval :=
  (Cylinder.encodedProjectivePrefixCertificate fraction numeratorNonzero).probeBound
    probe factor factorNonnegative sensitive

/-- The encoder-facing enclosure contains the probe value of the exact homogeneous representative computed by
`encodeBlocks`. -/
theorem encodedProjectivePrefixProbeBound_contains_point
    (fraction : SourceEncodingEncoderFracAlias)
    (numeratorNonzero : fraction.numerator ≠ 0)
    (probe : GaussianLine → Coordinate) (factor : Coordinate)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        factor * Chordal.Basic.chordalSq left right) :
    (encodedProjectivePrefixProbeBound fraction numeratorNonzero probe factor
      factorNonnegative sensitive).Contains
        (probe (Blocks.encodeBlocks fraction numeratorNonzero).point) := by
  exact Prefix.completedProjectivePrefixProbeBound_contains
    (Blocks.encodeBlocks fraction numeratorNonzero).blocks
    (Blocks.encodeBlocks fraction numeratorNonzero).point
    (Blocks.encodeBlocks_realizes fraction numeratorNonzero)
    probe factor factorNonnegative sensitive
    (Blocks.encodeBlocks_realizes fraction numeratorNonzero)

/-- The same enclosure contains the probe value of the original affine fraction reconstructed by the encoder. -/
theorem encodedProjectivePrefixProbeBound_contains_value
    (fraction : SourceEncodingEncoderFracAlias)
    (numeratorNonzero : fraction.numerator ≠ 0)
    (probe : GaussianLine → Coordinate) (factor : Coordinate)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        factor * Chordal.Basic.chordalSq left right) :
    (encodedProjectivePrefixProbeBound fraction numeratorNonzero probe factor
      factorNonnegative sensitive).Contains
        (probe (Proj.affine fraction.value)) := by
  have inside := encodedProjectivePrefixProbeBound_contains_point fraction
    numeratorNonzero probe factor factorNonnegative sensitive
  have probeEqual := Probe.probe_eq_of_projectiveEquivalent probe factor sensitive
    (Blocks.encodeBlocks_reconstruct fraction numeratorNonzero)
  rw [probeEqual] at inside
  exact inside

/-- A sufficient emitted block count turns one concrete encoder run into a strict rational accuracy certificate for
every compatible projective value. -/
theorem encodedProjectivePrefixProbeBound_width_lt_requested
    (fraction : SourceEncodingEncoderFracAlias)
    (numeratorNonzero : fraction.numerator ≠ 0)
    (probe : GaussianLine → Coordinate) (factor : Coordinate)
    (factorPositive : 0 < factor)
    (sensitive : ∀ left right,
      Distance.rationalSeparation (probe left) (probe right) ≤
        factor * Chordal.Basic.chordalSq left right)
    (target : Coordinate) (targetPositive : 0 < target)
    (enough : Budget.requiredProbeBlockCount target factor ≤
      (Blocks.encodeBlocks fraction numeratorNonzero).blocks.length) :
    (encodedProjectivePrefixProbeBound fraction numeratorNonzero probe factor
      factorPositive.le sensitive).width < target :=
  Prefix.completedProjectivePrefixProbeBound_width_lt_requested
    (Blocks.encodeBlocks fraction numeratorNonzero).point
    (Blocks.encodeBlocks_realizes fraction numeratorNonzero)
    probe factor factorPositive sensitive target targetPositive enough

/-! ## Finite tables of encoder inputs -/

/-- Push a finite input distribution through the executable certificate packager. Repeated encoded rows remain explicit
weighted rows. -/
def encodedProjectivePrefixDistribution {ι : Type}
    (distribution : Measure.Distribution ι)
    (fraction : ι → SourceEncodingEncoderFracAlias)
    (numeratorNonzero : ∀ item, (fraction item).numerator ≠ 0) :
    Measure.Distribution
      Cylinder.CompletedProjectivePrefixCertificate :=
  distribution.map fun item =>
    Cylinder.encodedProjectivePrefixCertificate (fraction item)
      (numeratorNonzero item)
end Purelib.Approximation.CCL.EncodedPrefix

end
