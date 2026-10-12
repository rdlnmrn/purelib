module

import Purelib.Data.ComplexContinuedFraction.Encoding.Sector.Basic
import Purelib.Geometry.Projective.Line.Basic
public import Purelib.Geometry.Projective.Line.Gaussian
public import Purelib.Geometry.Projective.SectorBlock.Tail
import Purelib.Tactic.QuotientFreeOmega

import Purelib.Data.Gaussian.Basic
meta import Mathlib.Tactic.Linter.Lint
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib

open Purelib.Data.ComplexContinuedFraction.Encoding

open Purelib.Geometry.Projective.Line.Basic

open Purelib.Geometry.Projective.Line.Gaussian

open Purelib.Geometry.Projective.SectorBlock

section
section
@[expose] public section
namespace Purelib.Geometry.Projective.SectorBlock.Tail

set_option genInjectivity false in
/-- A compatible tail may be carried by any valid homogeneous pair equivalent to the canonical affine or terminal model.
This is the form produced by an integral decoder without choosing a projective normalization. -/
structure ProjectiveTail (sector : Data.ComplexContinuedFraction.Encoding.Sector)
  where
  /-- The displayed homogeneous coordinate pair. -/ point : Geometry.Projective.Line.GaussianLine
  /-- At least one displayed homogeneous coordinate is nonzero. -/ valid : Proj.HasNonzeroCoordinate point
  /-- The affine-or-terminal compatible-tail model for the same sector. -/ model : Tail sector
  /-- The displayed pair is projectively equivalent to the retained model point. -/ equivalent : point.Equivalent
    model.point

constructive_injectivity ProjectiveTail

namespace ProjectiveTail.mk

end ProjectiveTail.mk

end Purelib.Geometry.Projective.SectorBlock.Tail
end
end

end

section
@[expose] public section
namespace Purelib.Geometry.Projective.SectorBlock.Tail
/-- A valid homogeneous representative with its exact compatible-tail model. -/
abbrev SourceEncodingEncoderProjectiveTailAlias :=
  ProjectiveTail
end Purelib.Geometry.Projective.SectorBlock.Tail

end

section
section
@[expose] public section
namespace Purelib.Geometry.Projective.SectorBlock.Tail.ProjectiveTail
section ProjectiveTail

/-- The retained affine-or-terminal model has a nonzero homogeneous coordinate. -/
theorem model_valid {sector :
  Data.ComplexContinuedFraction.Encoding.Sector} (tail : ProjectiveTail sector) :
    Proj.HasNonzeroCoordinate tail.model.point := by
  cases tail.model with
  | omega => exact Proj.omega_hasNonzeroCoordinate
  | affine value source compatible =>
      exact Proj.affine_hasNonzeroCoordinate value

end ProjectiveTail
end Purelib.Geometry.Projective.SectorBlock.Tail.ProjectiveTail
end
end

end

section
section
@[expose] public section
namespace Purelib.Geometry.Projective.SectorBlock.Tail.ProjectiveTail
section ProjectiveTail

/-- Use a compatible tail itself as its certified homogeneous representative.

The stored model is the supplied tail, and the equivalence certificate is reflexive. -/
def ofTail {sector : Data.ComplexContinuedFraction.Encoding.Sector}
  (tail : Tail sector) : ProjectiveTail sector where
  point := tail.point
  valid := by
    cases tail with
    | omega => exact Proj.omega_hasNonzeroCoordinate
    | affine tail value compatible =>
        exact Proj.affine_hasNonzeroCoordinate tail
  model := tail
  equivalent := by
    cases tail <;> rfl
end ProjectiveTail
end Purelib.Geometry.Projective.SectorBlock.Tail.ProjectiveTail
end
end

end
