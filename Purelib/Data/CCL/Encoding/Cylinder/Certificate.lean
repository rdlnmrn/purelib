module
meta import Purelib.Elab.ConstructiveInjectivity
public import Purelib.Data.CCL.Encoding.Encoder.Blocks
import Purelib.Data.GaussianInt.Fraction.Basic
import Purelib.Data.CCL.Encoding.Block.Basic
public import Purelib.Data.CCL.Encoding.Cylinder.Basic
import Purelib.Data.CCL.Encoding.Cylinder.Projective

import Purelib.Geometry.Projective.Line.Basic

import Purelib.Data.Gaussian.Basic
import Purelib.Data.GaussianInt.Basic

section
@[expose] public section

/-!
# Joint finite profile of a completed CCL prefix

A completed-block prefix carries two deliberately separate rational data:

* its fair-bit symbolic cylinder weight, calculated from the raw word; and
* its geometric squared-chordal spread, calculated from block contraction.

Both improve under finite extension, but no theorem identifies them.  A
finite realization certificate also turns the prefix into an inhabited
finite observation, without choosing a point from an eventual intersection.
-/

namespace Purelib.Data.CCL.Encoding.Cylinder

/-! ## Finite laws of heterogeneous completed prefixes -/

open Purelib.Data.CCL.Encoding in
open Purelib.Geometry.Projective in
set_option genInjectivity false in
/-- Retain a completed block list with a projective witness and its exact compatible-tail realization.

The realization belongs to the stored block list and stored point, certifying that the finite cylinder is inhabited
without selecting an unrelated representative. -/
structure CompletedPrefixCertificate where
  /-- The retained completed block list. -/ blocks : List Block
  /-- The retained projective witness for this block list. -/ witness : Line.GaussianLine
  /-- Evidence realizing these exact blocks at the retained witness. -/ witnessRealizes : Cylinder.Basic.Realizes blocks
    witness

constructive_injectivity CompletedPrefixCertificate

end Purelib.Data.CCL.Encoding.Cylinder

end

section
@[expose] public section

/-!
# Finite measure bounds for projectively rescaled CCL prefixes

The integral CCL encoder retains arbitrary nonzero homogeneous rescalings at
intermediate decoding stages.  Its certificates therefore use
`ProjectiveRealizes`, rather than the canonical-tail `Realizes` relation used
by the original prefix profile.  This module gives those exact encoder-facing
certificates the same finite observation and rational-enclosure interface.

No projective normalization, representative choice, completed point, or
infinite continuation is introduced.
-/

namespace Purelib.Data.CCL.Encoding.Cylinder

/-! ## Heterogeneous finite families of encoder-facing certificates -/

open Purelib.Data.CCL.Encoding in
open Purelib.Geometry.Projective in
set_option genInjectivity false in
/-- Retain a completed block list and a witness with its projective-tail realization.

Every step keeps the exact projective representative and its compatible model through the existing realization carrier.
-/
structure CompletedProjectivePrefixCertificate where
  /-- The retained completed block list. -/ blocks : List Block
  /-- The retained projective witness for this block list. -/ witness : Line.GaussianLine
  /-- Evidence realizing these exact blocks at the retained witness. -/ witnessRealizes :
    Cylinder.Projective.ProjectiveRealizes blocks witness

constructive_injectivity CompletedProjectivePrefixCertificate

end Purelib.Data.CCL.Encoding.Cylinder

end

section
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

namespace Purelib.Data.CCL.Encoding.Cylinder

open Purelib.Data in
open Purelib.Data.CCL.Encoding in
/-- Package the completed blocks and projective witness computed for the retained nonzero-numerator fraction. -/
def encodedProjectivePrefixCertificate
    (fraction : GaussianInt.Fraction.Basic.SourceEncodingEncoderFracAlias)
    (numeratorNonzero : fraction.numerator ≠ 0) :
    Cylinder.CompletedProjectivePrefixCertificate where
  blocks := (Encoder.Blocks.encodeBlocks fraction numeratorNonzero).blocks
  witness := (Encoder.Blocks.encodeBlocks fraction numeratorNonzero).point
  witnessRealizes :=
    Encoder.Blocks.encodeBlocks_realizes fraction numeratorNonzero

open Purelib.Data in
open Purelib.Data.CCL.Encoding in
open Purelib.Geometry.Projective in
/-- The packaged encoded witness is projectively equivalent to the original fraction's affine value. -/
theorem encodedProjectivePrefixCertificate_reconstruct
    (fraction : GaussianInt.Fraction.Basic.SourceEncodingEncoderFracAlias)
    (numeratorNonzero : fraction.numerator ≠ 0) :
    (Cylinder.encodedProjectivePrefixCertificate fraction numeratorNonzero).witness
        |>.Equivalent (Line.Proj.affine fraction.value) :=
  Encoder.Blocks.encodeBlocks_reconstruct fraction numeratorNonzero
end Purelib.Data.CCL.Encoding.Cylinder

end

end
