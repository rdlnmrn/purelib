module
import Purelib.CCL.Measure.Basic
public import Purelib.Data.CCL.Encoding.Encoder.Blocks
import Purelib.Data.GaussianInt.Fraction.Basic
public import Purelib.Geometry.Projective.Chordal.Probe.Omega
import Purelib.Geometry.Projective.Chordal.Probe.OmegaSensitivity
public import Purelib.Geometry.Projective.Chordal.Probe.Sensitivity
import Purelib.Geometry.Projective.Line.Basic
import Purelib.Geometry.Projective.Line.Gaussian

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Gaussian.Basic
import Purelib.Data.GaussianInt.Basic
import Purelib.Data.Rat.Fraction

open Purelib

open Purelib.Data.CCL.Encoding.Encoder

open Purelib.Data.GaussianInt hiding Coordinate

open Purelib.Geometry.Projective.Chordal

open Purelib.Geometry.Projective.Line

open Purelib.Geometry.Projective.Line.Basic

open Purelib.Geometry.Projective.Line.Gaussian

section
@[expose] public section

/-!
# Root-free L2 stability for actual finite CCL encoder tables

This module applies squared-probe prefix stability directly to the block lists
and projective realization certificates computed by `encodeBlocks`.  The
comparison target is the original affine Gaussian fraction, connected to the
computed homogeneous witness by the encoder's explicit reconstruction proof.
-/

namespace Purelib.Approximation.CCL.EncodedPrefix

open Purelib.CCL.Measure (Coordinate)

/-- Every squared-sensitive projective probe takes exactly the same value on the encoder's computed homogeneous point
and on the reconstructed original affine Gaussian fraction. -/
theorem encodedSquaredSensitiveProbe_eq_value
    (fraction : Fraction.Basic.SourceEncodingEncoderFracAlias) (numeratorNonzero : fraction.numerator ≠ 0)
    (probe : GaussianLine → Coordinate) (factor : Coordinate)
    (sensitive : Probe.SquaredProbeSensitive probe factor) :
    probe (Blocks.encodeBlocks fraction numeratorNonzero).point =
      probe (Proj.affine fraction.value) := by
  let encoding := Blocks.encodeBlocks fraction numeratorNonzero
  exact Probe.squaredSensitive_probe_eq_of_projectiveEquivalent probe factor
    sensitive encoding.realizes.valid
    (Proj.affine_hasNonzeroCoordinate fraction.value)
    encoding.reconstruct

/-! ## Concrete nonconstant chordal-observation specializations -/

/-- The encoder's own computed point has exactly the original affine fraction's distance-to-`omega` probe value. -/
theorem encodedChordalOmegaProbe_eq_value
    (fraction : Fraction.Basic.SourceEncodingEncoderFracAlias) (numeratorNonzero : fraction.numerator ≠ 0) :
    Probe.chordalOmegaProbe
        (Blocks.encodeBlocks fraction numeratorNonzero).point =
      Probe.chordalOmegaProbe (Proj.affine fraction.value) :=
  encodedSquaredSensitiveProbe_eq_value fraction numeratorNonzero
    Probe.chordalOmegaProbe 2 Probe.chordalOmegaProbe_squaredSensitive
end Purelib.Approximation.CCL.EncodedPrefix

end
