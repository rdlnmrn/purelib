module
import Purelib.Data.Gaussian.Basic
public import Purelib.Data.Gaussian.Field

open Purelib.Data.Gaussian.Basic

section
@[expose] public section

/-! Exact replay of the finite rounded sample search. Integer rounding
witnesses are checked by inequalities, and inverse witnesses by multiplication.
An exhausted trace certifies only this finite attempt. -/

namespace Purelib.Data.Gaussian.Basic.Canonical.Inverse

/-- Retain a Gaussian candidate together with equality to the original point's total
reciprocal.

The subtype keeps the actual candidate and exact reciprocal identity, including the
total inverse convention at zero. -/
abbrev Certificate (point : Canonical) := {candidate : Canonical
  // candidate = point⁻¹}
end Purelib.Data.Gaussian.Basic.Canonical.Inverse

end
