module
import Purelib.Data.Gaussian.Basic
public import Purelib.Algebra.Power.Gaussian.ExactRoot
import Purelib.Data.Nat.Positive
import Purelib.Data.List.Membership

import Purelib.Tactic.QuotientFreeOmega

open Purelib.Algebra.Power.Gaussian.ExactRoot

open Purelib.Data.Gaussian.Basic

open Purelib.Data.Nat.Positive

open Purelib.Data.List

section
@[expose] public section

/-!
# Finite root families, branch-selected roots, and rational powers

For an exact Gaussian-rational radicand, the polynomial `T^q - y` supplies
the public `q`th-root operation: its finite RFAP decomposition produces
exactly `q` root occurrences, counting displayed multiplicity.  Each
squarefree factor is either an exact rational terminal or a finite family of
independently shrinking CCL tracks.  Any additional displayed rational
candidate can also be checked and promoted immediately to a terminating CCL.
For automatic discovery, the special form `T^q-y` avoids a generic coordinate
Sylvester construction.  A sparse norm equation first enumerates the possible
rational quadrances.  At each one, a finite Lucas recurrence supplies the two
coordinate polynomials.  Their endpoint-divisor candidates are crossed,
deduplicated, and checked by the same exact power test.

The logarithmic formula `exp(log(y) / q)` remains useful, but it selects only
one explicitly anchored branch.  It is therefore named `selectedRoot`, not
the multi-valued `q`th-root operation.  All constructions stay inside finite
CCL arithmetic and never complete an input, logarithm, or root stream.
-/

namespace Purelib.Algebra.Power.Gaussian.ExactRoot.Check

/-- Check a displayed Gaussian candidate for an exact positive-degree power identity.

Success retains the candidate with its equality certificate; failure returns none for that candidate only. -/
def promoteIfExact (input : Canonical) (degree : RootDegree)
    (candidate : Canonical) : Option (Algebra.Power.Gaussian.ExactRoot input degree) :=
  if power : candidate ^ degree.value = input then
    some ⟨candidate, power⟩
  else
    none

/-- An exact power identity makes the candidate check succeed.

The returned root retains the supplied candidate and its power equality. -/
theorem promoteIfExact_eq_some
    (input : Canonical) (degree : RootDegree) (candidate : Canonical)
    (power : candidate ^ degree.value = input) :
    promoteIfExact input degree candidate = some ⟨candidate, power⟩ := by
  rewrite [promoteIfExact, dif_pos power]
  rfl

/-- A false power identity makes the candidate check return none.

The negative result concerns only the displayed Gaussian candidate. -/
theorem promoteIfExact_eq_none
    (input : Canonical) (degree : RootDegree) (candidate : Canonical)
    (power : candidate ^ degree.value ≠ input) :
    promoteIfExact input degree candidate = none := by
  rewrite [promoteIfExact, dif_neg power]
  rfl

/-- Filter a finite candidate list into certified exact roots.

Each successful check retains its candidate in the original order; repeated successful candidates remain repeated. -/
def promoteCandidates (input : Canonical) (degree : RootDegree) :
    List Canonical → List (Algebra.Power.Gaussian.ExactRoot input degree)
  | [] => []
  | candidate :: remaining =>
      match promoteIfExact input degree candidate with
      | some root => root :: promoteCandidates input degree remaining
      | none => promoteCandidates input degree remaining

/-- The points retained by exact-root promotion form a sublist of the candidates.

Promotion preserves candidate order and introduces no new points. -/
theorem promoteCandidates_points_sublist
    (input : Canonical) (degree : RootDegree) :
    (candidates : List Canonical) →
      List.Sublist
        ((promoteCandidates input degree candidates).map Algebra.Power.Gaussian.ExactRoot.point)
        candidates
  | [] => List.Sublist.slnil
  | candidate :: remaining => by
      rw [promoteCandidates]
      split
      · rename_i root promoted
        have pointEqual : root.point = candidate := by
          rw [promoteIfExact] at promoted
          split at promoted
          · exact congrArg Algebra.Power.Gaussian.ExactRoot.point (Option.some.inj promoted.symm)
          · contradiction
        rw [List.map_cons, pointEqual]
        exact List.Sublist.cons_cons candidate
          (promoteCandidates_points_sublist input degree remaining)
      · exact List.Sublist.cons candidate
          (promoteCandidates_points_sublist input degree remaining)

/-- Every exact root occurring in the candidate list survives promotion.

A supplied power equality certifies the point independently of the other finite candidates. -/
theorem mem_promoteCandidates_of_mem
    (input : Canonical) (degree : RootDegree) (candidate : Canonical)
    (power : candidate ^ degree.value = input) :
    (candidates : List Canonical) → candidate ∈ candidates →
      candidate ∈
        (promoteCandidates input degree candidates).map Algebra.Power.Gaussian.ExactRoot.point
  | [], member => (List.not_mem_nil member).elim
  | head :: remaining, member => by
      rw [promoteCandidates]
      split
      · rename_i promoted promotion
        have pointEqual : promoted.point = head := by
          rw [promoteIfExact] at promotion
          split at promotion
          · exact congrArg Algebra.Power.Gaussian.ExactRoot.point (Option.some.inj promotion.symm)
          · contradiction
        rewrite [List.map_cons]
        apply Membership.mem_cons.mpr
        rcases Membership.mem_cons.mp member with equal | tailMember
        · left
          exact equal.trans pointEqual.symm
        · right
          exact mem_promoteCandidates_of_mem input degree candidate power
            remaining tailMember
      · rcases Membership.mem_cons.mp member with equal | tailMember
        · subst head
          rename_i promotion
          rw [promoteIfExact, dif_pos power] at promotion
          contradiction
        · exact mem_promoteCandidates_of_mem input degree candidate power
            remaining tailMember
end Purelib.Algebra.Power.Gaussian.ExactRoot.Check

end
