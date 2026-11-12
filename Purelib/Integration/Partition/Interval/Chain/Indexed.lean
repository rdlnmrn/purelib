module

public import Purelib.Integration.Partition.Interval.Chain
public import Purelib.Algebra.FiniteSum.Fin
import Purelib.Data.List.OfFn.Basic
public import Purelib.Data.Rat.Fraction.Field
import Purelib.Tactic.Ring

/-! # Finite width readbacks of retained interval chains

Original ordered intervals telescope through their exact adjacent endpoints.
The indexed version retains the original finite table, including repeated
or zero-width intervals; no new cut enumeration is selected.
-/

public section

namespace Purelib.Integration.Partition.Interval.Chain

open Purelib.Algebra
open Purelib.Data.List
open Purelib.Data.Rat.Fraction (Rational)

/-- Removing the actual first interval leaves the same retained tail starting at its exact finish. -/
theorem tail {start finish : Rational} {first : Interval} {remaining : List Interval} :
    Chain start finish (first :: remaining) → Chain first.finish finish remaining
  | .cons rest => rest

/-- The original finite table's oriented widths sum to the retained outer endpoint difference.

Exact chain incidence supplies telescoping. Orientation and nonnegativity
remain separate, so repeated or reversed intervals are preserved by this
readback as well.
-/
theorem sum_widths {count : Nat} (intervals : Fin count → Interval) {start finish : Rational}
    (chain : Chain start finish (List.ofFn intervals)) :
    FiniteSum.Fin.sumFin (fun index => (intervals index).finish - (intervals index).start) = finish - start := by
  induction count generalizing start with
  | zero =>
      rewrite [List.ofFn_zero] at chain
      cases chain
      change (0 : Rational) = _
      ring1
  | succ count previous =>
      rewrite [OfFn.Basic.ofFn_succ] at chain
      have first_eq : (intervals 0).start = start := chain.start_eq (Nat.zero_lt_succ _)
      have remaining := chain.tail
      rewrite [FiniteSum.Fin.sumFin_succ,
        previous (fun index => intervals index.succ) remaining, first_eq]
      ring1

end Purelib.Integration.Partition.Interval.Chain

end
