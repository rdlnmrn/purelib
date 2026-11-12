module

public import Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Range.Strip
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic

/-! # Exact original seed-reference factories across retained budget caches

Both budgets retain equality to the SAME original Range.seedBudget. The
actual point, absolute increment and source seed Owner remain indices.
Transport changes only those complete certified factory arguments; no
reference Owner or budget is computed again.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Range

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.RootContinuation

variable {parameter point : Canonical} {count : Nat}
    {patch : ContinuedNeighborhood (Paths.polynomial parameter) count} (range : Range patch)
    (first last : FixedRootBoxBudget.Budget patch.base.seed.owner)
    (first_eq : first = range.seedBudget) (last_eq : last = range.seedBudget)
    (inside : patch.box.Contains point) (increment : Canonical)
    (firstPaid lastPaid : Norm.Basic.normSq increment ≤ range.stripBound)

/-- Identical original budget factories give equality of the whole seedOwner factory at the same point and offset. -/
theorem seedOwner_congr : range.seedOwner first first_eq inside increment firstPaid =
    range.seedOwner last last_eq inside increment lastPaid := by
  have same : first = last := first_eq.trans last_eq.symm
  cases same
  rfl

/-- Transport a GIVEN reference's full factory to another retained copy of the SAME original seed budget. -/
theorem seedOwner_factory
    (reference : FixedRootBoxBudget.Owner ((Paths.polynomial (parameter + increment)).eval point))
    (factory : reference = range.seedOwner first first_eq inside increment firstPaid) :
    reference = range.seedOwner last last_eq inside increment lastPaid :=
  factory.trans (range.seedOwner_congr first last first_eq last_eq inside increment firstPaid lastPaid)

end Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Range

end
