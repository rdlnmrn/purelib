module
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Measure.Distribution.Basic
import Purelib.Data.Rat.Fraction

public import Purelib.Measure.Content.EssentialBound.Basic
public import Purelib.Measure.Distribution.Content

section
@[expose] public section

/-!
# Finite essential bounds

An essential bound may fail only at displayed zero-weight atoms.  This is the
finite rational replacement for an essential supremum: the bound itself is
explicit data, so no supremum or completed value is selected.
-/

namespace Purelib.Measure
namespace Content
end Content

namespace Distribution

open Purelib.Data.Rat in
/-- Require the observable's magnitude ceiling at every nonzero-weight occurrence of the exact distribution.

The condition uses the original content and retains its weights, so zero-weight occurrences impose no bound. -/
def EssentiallyBoundedBy {α : Type} (distribution : Distribution α)
    (value : α → Fraction.Rational) (ceiling : Fraction.Rational) : Prop :=
  distribution.toContent.EssentiallyBoundedBy value ceiling
end Distribution

end Purelib.Measure

end
