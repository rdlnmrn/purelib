module
import Purelib.Algebra.NatCast
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Distance.Basic
import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Content.Basic
import Purelib.Measure.Weighted.Basic
public import Purelib.Measure.SignedContent.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Tactic.Ring

section
@[expose] public section

/-!
# Exact finite Kolmogorov distance

For two finite rational laws, cumulative probabilities can change only at
payloads displayed by one of the two atom tables.  A terminating search finds
the greatest displayed payload below any supplied rational cut.  Consequently
the maximum CDF discrepancy on the finite union of the two support tables
controls every rational cut; no supremum over the rational or real line is
formed.
-/

namespace Purelib.Measure

namespace SignedContent

open Purelib.Data.Rat in
open Purelib.Algebra in
/-- The variation weight of the exact signed occurrence list is at most its length times a common weight-magnitude
ceiling. -/
public theorem variationTotalWeight_le_length_mul_of_bounded
    (atoms : List (SignedWeighted Fraction.Rational)) (ceiling : Fraction.Rational)
    (bounded : ∀ atom, atom ∈ atoms →
      Distance.rationalSeparation atom.weight 0 ≤ ceiling) :
    totalWeight (atoms.map SignedContent.variationAtom) ≤
      (atoms.length : Fraction.Rational) * ceiling := by
  induction atoms with
  | nil =>
      simp only [List.map_nil, totalWeight_nil, List.length_nil,
        Nat.cast_zero, zero_mul]
      exact le_rfl
  | cons atom remaining inductionHypothesis =>
      have tailBounded : ∀ candidate, candidate ∈ remaining →
          Distance.rationalSeparation candidate.weight 0 ≤ ceiling := by
        intro candidate member
        exact bounded candidate (List.mem_cons_of_mem atom member)
      simp only [List.map_cons, totalWeight_cons, List.length_cons,
        NatCast.add, Nat.cast_one]
      calc
        Distance.rationalSeparation atom.weight 0 +
            totalWeight (remaining.map SignedContent.variationAtom) ≤
          ceiling + (remaining.length : Fraction.Rational) * ceiling :=
        add_le_add (bounded atom List.mem_cons_self)
          (inductionHypothesis tailBounded)
        _ = ((remaining.length : Fraction.Rational) + 1) * ceiling := by ring1

end SignedContent

end Purelib.Measure

end
