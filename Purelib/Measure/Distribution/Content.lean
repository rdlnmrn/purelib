module
public import Purelib.Measure.Content.Operations
import Purelib.Measure.Distribution.Basic
public import Purelib.Measure.Distribution.Kernel.Basic

import Purelib.Measure.Content.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic

section
section
@[expose] public section

/-!
# Exact finite rational valuations

`FiniteContent` is the normalized-independent core measure object: a displayed
finite weighted list evaluated only against executable Boolean events.
-/

namespace Purelib.Measure
namespace Content
end Content

namespace Distribution

/-- View the distribution's exact retained occurrence list as content without changing any weights. -/
def toContent {α : Type} (distribution : Distribution α) :
    Content α :=
  ⟨distribution.atoms⟩

/-- The content view of a retained distribution has total weight exactly one. -/
@[simp] theorem toContent_total {α : Type}
    (distribution : Distribution α) :
    distribution.toContent.total = 1 :=
  distribution.total_one

end Distribution

end Purelib.Measure

end

end

section
/-!
# Finite pushforward laws for powered Lp and essential maxima

An executable pushforward retains every displayed source row and merely
changes its payload.  Consequently rational L1, natural-powered Lp, finite
almost-everywhere equality, and computed essential maxima all obey exact
change-of-variables laws.  No quotient function space or measurable-map
side condition is needed on a displayed finite table.
-/

@[expose] public section

namespace Purelib.Measure
namespace Distribution

/-- Mapping then taking content gives exactly the content map of the original distribution's retained list. -/
theorem map_toContent {α β : Type} (source : Distribution α)
    (function : α → β) :
    (source.map function).toContent =
      source.toContent.map function := by
  unfold toContent Content.map
  rw [source.map_atoms_eq_mapAtoms function]
end Distribution

end Purelib.Measure

end
