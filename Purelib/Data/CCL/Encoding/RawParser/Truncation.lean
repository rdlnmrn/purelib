module
public import Purelib.Data.CCL.Encoding.Parser.Semantics.State
import Purelib.Data.CCL.Encoding.Parser.State
import Purelib.Data.List.BinaryPrefix.Basic
public import Purelib.Geometry.Projective.Line.Gaussian
import Purelib.Geometry.Projective.Line.Matrix.Gaussian

import Purelib.Geometry.Projective.Line.Basic

section
@[expose] public section

/-!
# Finite-depth laws of CCL truncation points

The symbolic fair-bit distribution on a displayed raw extension frontier can
be pushed through the parser's explicit projective truncation.  The result is
an ordinary finite distribution of constructive projective points.  No claim
is made about a limiting decoder value or a geometric pushforward measure.
-/

namespace Purelib.Data.CCL.Encoding.RawParser

open Purelib.Data.CCL.Encoding
open Purelib.Data.List
open Purelib.Geometry.Projective
/-- Read the projective truncation retained after parsing the exact finite bit word. -/
def rawTruncation (word : BinaryPrefix.CCLMeasureWord) :
  Line.GaussianLine :=
  (Parser.State.parse word).truncation

/-- Every finite raw parser truncation has a nonzero projective coordinate. -/
theorem rawTruncation_hasNonzeroCoordinate (word :
  BinaryPrefix.CCLMeasureWord) :
    Line.Gaussian.Proj.HasNonzeroCoordinate (rawTruncation word) := by
  unfold rawTruncation Data.CCL.Encoding.Parser.State.truncation
  exact Line.Matrix.Gaussian.Mat2.act_hasNonzeroCoordinate
    (Parser.State.parse_det_ne word)
    Line.Gaussian.Proj.omega_hasNonzeroCoordinate
end Purelib.Data.CCL.Encoding.RawParser

end
