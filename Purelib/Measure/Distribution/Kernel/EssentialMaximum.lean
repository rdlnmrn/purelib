module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Distance.Basic
import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Weighted.EssentialMaximum
import Purelib.Measure.Distribution.Kernel.Basic
import Purelib.Data.List.Event
public import Purelib.Measure.Distribution.EssentialMaximum.Basic
import Purelib.Measure.Weighted.Basic

section
/-!
# Essential maxima on explicit finite products

The computed essential maximum of a separable product factors exactly over
the Cartesian product of two displayed finite contents.  The proof follows
the executable atom-list construction, treating zero weights directly; no
supremum, maximizing choice, or product sigma algebra is used.
-/

@[expose] public section

namespace Purelib.Measure

namespace Distribution

open Purelib
open Purelib.Data.Rat
/-- The essential maximum after binding equals the source essential maximum of the exact conditional essential maxima.

The original binding concatenates scaled conditional occurrence lists. Zero
source weights are skipped; nonzero weights retain each conditional maximum. -/
theorem bind_essentialMaximumMagnitude {α β : Type}
    (source : Measure.Distribution α) (transition : α → Measure.Distribution β)
    (value : β → Fraction.Rational) :
    (source.bind transition).essentialMaximumMagnitude value =
      source.essentialMaximumMagnitude
        (fun item => (transition item).essentialMaximumMagnitude value) := by
  change essentialMaximumMagnitudeOn value
      (bindAtoms source.atoms transition) =
    essentialMaximumMagnitudeOn
      (fun item => essentialMaximumMagnitudeOn value (transition item).atoms)
      source.atoms
  induction source.atoms with
  | nil => rfl
  | cons atom remaining inductionHypothesis =>
      rw [bindAtoms, Measure.essentialMaximumMagnitudeOn_append]
      by_cases atomZero : atom.weight = 0
      · rw [Measure.essentialMaximumMagnitudeOn_scaleAtoms_of_eq_zero _ atom.weight
          atom.nonnegative atomZero, inductionHypothesis]
        rewrite [essentialMaximumMagnitudeOn, if_pos atomZero]
        exact Fraction.Order.Basic.max_eq_right
          (essentialMaximumMagnitudeOn_nonnegative
            (fun item => essentialMaximumMagnitudeOn value
              (transition item).atoms) remaining)
      · rw [Measure.essentialMaximumMagnitudeOn_scaleAtoms_of_ne _ atom.weight
          atom.nonnegative atomZero, inductionHypothesis]
        rewrite [essentialMaximumMagnitudeOn, if_neg atomZero]
        rw [Distance.rationalSeparation_zero_of_nonneg
          (essentialMaximumMagnitudeOn_nonnegative value
            (transition atom.item).atoms)]

/-- The essential distance after binding equals the source essential maximum of the exact conditional essential
distances. -/
theorem bind_essentialMaximumDistance {α β : Type}
    (source : Measure.Distribution α) (transition : α → Measure.Distribution β)
    (left right : β → Fraction.Rational) :
    (source.bind transition).essentialMaximumDistance left right =
      source.essentialMaximumMagnitude (fun item =>
        (transition item).essentialMaximumDistance left right) := by
  unfold essentialMaximumDistance
  exact source.bind_essentialMaximumMagnitude transition
    (fun item => left item - right item)
end Distribution

end Purelib.Measure

end
