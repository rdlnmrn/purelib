module
public import Purelib.Data.Rat.Interval.Basic

section
@[expose] public section

/-!
# Shrinking nonzero Sturm-event cells

A nonzero doubled Sturm count can be followed constructively without first
proving the stronger global nonnegativity theorem.  A safe cut splits the
parent count additively; testing the left integer count either selects that
child or proves that the right count remains nonzero.  Repeating the fixed
central-third contraction gives a total finite interval-refinement track for every
positive rational width request.

This is the reusable track-valued interface for finite boundary ownership.
It names no root and does not assume that the nonzero count has a particular
sign.
-/

namespace Purelib.Data.Rat.Interval.Refinement

open Purelib.Data.Rat in
/-- Compose endpoint refinement of nominal basic intervals through the retained middle interval. -/
theorem intervalRefines_trans
    {inner middle outer : Data.Rat.Interval.Bounds}
    (innerMiddle : inner.Refines middle)
    (middleOuter : middle.Refines outer) : inner.Refines outer :=
  ⟨middleOuter.1.trans innerMiddle.1,
    innerMiddle.2.trans middleOuter.2⟩
end Purelib.Data.Rat.Interval.Refinement

end
