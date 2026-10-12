module
import Purelib.Measure.Weighted.Basic
public import Purelib.Measure.Weighted.Integral
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic

public import Purelib.Data.Rat.Distance.Basic
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic

section
@[expose] public section

/-!
# Finite essential bounds

An essential bound may fail only at displayed zero-weight atoms.  This is the
finite rational replacement for an essential supremum: the bound itself is
explicit data, so no supremum or completed value is selected.
-/

namespace Purelib.Measure

section
open Purelib.Data.Rat
/-- Require each retained occurrence to have zero weight or observable value at most the supplied ceiling. -/
def BoundedAboveOffZeroWeightOn {α : Type} (atoms : List (Weighted α))
    (value : α → Fraction.Rational) (ceiling : Fraction.Rational) : Prop :=
  ∀ atom, atom ∈ atoms →
    atom.weight = 0 ∨ value atom.item ≤ ceiling

/-- Bound the observable's rational distance from zero away from zero-weight retained occurrences. -/
def EssentiallyBoundedByOn {α : Type} (atoms : List (Weighted α))
    (value : α → Fraction.Rational) (ceiling : Fraction.Rational) : Prop :=
  BoundedAboveOffZeroWeightOn atoms
    (fun item => Distance.rationalSeparation (value item) 0) ceiling

/-- Comparison away from zero-weight occurrences bounds the exact finite weighted integrals. -/
theorem expectationWeight_mono_off_zero {α : Type}
    (lower upper : α → Fraction.Rational) :
    ∀ atoms : List (Weighted α),
      (∀ atom, atom ∈ atoms →
        atom.weight = 0 ∨ lower atom.item ≤ upper atom.item) →
      Distribution.expectationWeight atoms lower ≤
        Distribution.expectationWeight atoms upper
  | [], pointwise => le_rfl
  | atom :: remaining, pointwise => by
      have tailPointwise : ∀ candidate, candidate ∈ remaining →
          candidate.weight = 0 ∨
            lower candidate.item ≤ upper candidate.item :=
        fun candidate member =>
          pointwise candidate (List.mem_cons_of_mem atom member)
      have tailBound := expectationWeight_mono_off_zero
        lower upper remaining tailPointwise
      rcases pointwise atom List.mem_cons_self with zero | headBound
      · simp only [Distribution.expectationWeight, zero, zero_mul, zero_add]
        exact tailBound
      · simp only [Distribution.expectationWeight]
        exact add_le_add
          (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
            headBound atom.nonnegative)
          tailBound

end

namespace Content
end Content

namespace Distribution
end Distribution

end Purelib.Measure

end
