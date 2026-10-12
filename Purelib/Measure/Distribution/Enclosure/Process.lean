module
import Purelib.Data.Rat.Fraction
public import Purelib.Approximation.Bound.Process
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Measure.Distribution.Basic
public import Purelib.Measure.Weighted.Enclosure.Process
public import Purelib.Measure.Distribution.Enclosure.Basic
import Purelib.Measure.Weighted.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Measure.Distribution.Expectation
import Purelib.Data.Rat.Interval.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic

section
@[expose] public section

/-!
# Expectations of finitely enclosed observables

A displayed rational enclosure at each displayed probability atom induces a
displayed rational enclosure of the expectation.  Its endpoints are finite
weighted sums and its width is exactly the expectation of the pointwise
widths.  Thus progressively sharper rational data can be propagated through
finite expectation without postulating a completed observable or a limit.
-/

namespace Purelib.Measure

namespace PointwiseEnclosureProcess

open Purelib
open Purelib.Data.Rat
/-- Average the original pointwise interval process into an expectation-bound process using half-tolerance requests.

The state type, original distribution and initial state are retained, and each averaged bound uses those same atom
weights and requested ranges. -/
def toExpectationBoundProcess {α : Type} {distribution : Distribution α}
    (process : Measure.PointwiseEnclosureProcess distribution) : Approximation.BoundProcess where
  State := process.State
  bound state := distribution.enclosedExpectation (process.ranges state)
  initial := process.initial
  request state epsilon positive :=
    process.request state (epsilon / 2)
      (Fraction.Order.Field.div_pos_direct positive (by decide))
  request_refines state epsilon positive := by
    apply distribution.enclosedExpectation_refines
    intro atom member
    exact process.request_refines state (epsilon / 2)
      (Fraction.Order.Field.div_pos_direct positive (by decide))
      atom member
  accurate state epsilon positive := by
    apply distribution.enclosedExpectation_width_lt_of_uniform
      (process.ranges (process.request state (epsilon / 2)
        (Fraction.Order.Field.div_pos_direct positive (by decide))))
      (epsilon / 2) epsilon
    · intro atom member
      exact process.accurate state (epsilon / 2)
        (Fraction.Order.Field.div_pos_direct positive (by decide))
        atom member
    · exact Purelib.Data.Rat.Fraction.Order.Field.half_lt_self positive
  refinesInitial state := by
    apply distribution.enclosedExpectation_refines
    exact process.refinesInitial state

/-- The original expectation of an observable admitted by every retained range lies in the exact expectation-process
bound. -/
theorem expectation_mem {α : Type} {distribution : Distribution α}
    (process : Measure.PointwiseEnclosureProcess distribution)
    (state : process.State) (value : α → Fraction.Rational)
    (inside : ∀ atom, atom ∈ distribution.atoms →
      (process.ranges state atom.item).Contains (value atom.item)) :
    (process.toExpectationBoundProcess.bound state).Contains
      (distribution.expectation value) :=
  distribution.expectation_mem_enclosedExpectation
    (process.ranges state) value inside

/-- Every candidate in the exact requested expectation interval differs from its retained approximation by less than the
positive tolerance in both directions. -/
theorem candidate_close_to_approximation {α : Type}
    {distribution : Distribution α}
    (process : Measure.PointwiseEnclosureProcess distribution)
    (state : process.State) (epsilon : Fraction.Rational) (positive : 0 < epsilon)
    {candidate : Fraction.Rational}
    (inside :
      (process.toExpectationBoundProcess.bound
        (process.toExpectationBoundProcess.request state epsilon positive)).Contains
          candidate) :
    candidate - process.toExpectationBoundProcess.approximate
        state epsilon positive < epsilon ∧
      process.toExpectationBoundProcess.approximate
        state epsilon positive - candidate < epsilon :=
  process.toExpectationBoundProcess.candidate_close_to_approximate
    state epsilon positive inside

end PointwiseEnclosureProcess

end Purelib.Measure

end
