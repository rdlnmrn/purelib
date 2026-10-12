module
import Purelib.Data.List.Membership
public import Purelib.Geometry.Projective.Hermitian.Basic

import Purelib.Tactic.QuotientFreeOmega

public section

open Purelib.Geometry.Projective.Hermitian

/-!
# Removing retained Hermitian forms from finite lists

The executable selector removes the first matching form and retains the order
of all remaining occurrences. Its certificates preserve every different member
and prove a strict length decrease when the selected form occurs.
-/

namespace Purelib.Data.List.Erase

/-- Remove the first occurrence of a displayed Hermitian form from a finite list.

Executable equality selects the first matching head; the unmatched prefix is retained
in order. If the target does not occur, every original entry remains. -/
@[expose] def eraseForm (target : HermitianForm) :
    List HermitianForm → List HermitianForm
  | [] => []
  | form :: remaining =>
      if form = target then remaining else form :: eraseForm target remaining

open Purelib.Data.List
/-- Removing one Hermitian form preserves membership of every different form. -/
theorem mem_eraseForm_of_ne
    {target other : HermitianForm} {forms : List HermitianForm}
    (different : other ≠ target) (member : other ∈ forms) :
    other ∈ eraseForm target forms := by
  induction forms with
  | nil => exact (List.not_mem_nil member).elim
  | cons form remaining inductionHypothesis =>
      by_cases equal : form = target
      · rewrite [eraseForm, if_pos equal]
        rcases Purelib.Data.List.Membership.mem_cons.mp member with head | tail
        · exact (different (head.trans equal)).elim
        · exact tail
      · rewrite [eraseForm, if_neg equal]
        rcases Purelib.Data.List.Membership.mem_cons.mp member with head | tail
        · subst other
          exact List.Mem.head _
        · exact List.Mem.tail form (inductionHypothesis tail)

/-- Removing a Hermitian form known to occur strictly decreases the list length. -/
theorem length_eraseForm_lt
    {target : HermitianForm} {forms : List HermitianForm}
    (member : target ∈ forms) :
    (eraseForm target forms).length < forms.length := by
  induction forms with
  | nil => exact (List.not_mem_nil member).elim
  | cons form remaining inductionHypothesis =>
      by_cases equal : form = target
      · rewrite [eraseForm, if_pos equal]
        exact Nat.lt_succ_self remaining.length
      · have tailMember : target ∈ remaining := by
          rcases Purelib.Data.List.Membership.mem_cons.mp member with head | tail
          · exact (equal head.symm).elim
          · exact tail
        change (eraseForm target (form :: remaining)).length < (form :: remaining).length
        rewrite [eraseForm, if_neg equal]
        exact Nat.succ_lt_succ (inductionHypothesis tailMember)

end Purelib.Data.List.Erase

end
