module
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.ComplexContinuedFraction.Encoding.Sector.Basic
public import Purelib.Geometry.Projective.SectorBlock.Safe.Basic
public import Purelib.Geometry.Projective.SectorBlock.Tail
import Purelib.Geometry.Rational.Sector.Eight.Cell

import Purelib.Tactic.QuotientFreeOmega

open Purelib

open Purelib.Data.ComplexContinuedFraction.Encoding

open Purelib.Geometry.Projective.SectorBlock

open Purelib.Geometry.Rational.Sector.Eight

section
@[expose] public section

/-!
# Completed-block contraction for redundant CCL choices

The canonical contraction theorem stores annulus and disjoint-sector proofs.
For arithmetic output those hypotheses are unnecessarily strong.  A block is
sound and has the same contraction factor whenever its displayed value has
norm at least one and its chosen representative has residual quadrance below
one half.

This parallel structure deliberately leaves the canonical theorem and parser
unchanged.  `ofCanonical` embeds every old compatible block into this wider
arithmetic layer.
-/

namespace Purelib.Geometry.Projective.SectorBlock.Safe.Basic.CompatibleTail
section

/-- Every canonical compatible tail is accepted by the redundant layer. -/
theorem ofCanonical {sector :
  Data.ComplexContinuedFraction.Encoding.Sector} {tail value : Data.Gaussian.Basic.Canonical}
    (compatible :
      Tail.CompatibleTail sector tail value) :
    Safe.Basic.CompatibleTail sector tail value :=
  { equation := compatible.equation
    normLower := by
      simpa only [Data.Gaussian.Norm.Basic.normSq_eq_canonical]
        using compatible.band.1
    safe := Cell.safe_of_canonical
      compatible.band compatible.holds }
end

end Purelib.Geometry.Projective.SectorBlock.Safe.Basic.CompatibleTail

end
