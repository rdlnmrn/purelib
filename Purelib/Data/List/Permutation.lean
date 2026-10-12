module

import Purelib.Data.List.OfFn.Basic
-- Exposed extraction outcomes retain the original membership certificates.
public import Purelib.Data.List.Membership
import Purelib.Data.List.Append
import Purelib.Data.List.Flatten
import Init.Data.Fin.Fold
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Data.List

/-!
# List permutation certificates

Positive certificates use the constructors of `List.Perm`. In particular, flat-map
transport does not use the generic `filterMap_eq_map` proof route, and the
positive checker does not use generic erase lemmas or a choice-based
propositional decision instance. All searches recurse on displayed lists.
Negative certificates use structural finite-list length preservation and
common-head cancellation. Cancellation follows the displayed permutation and
retains an explicit intermediate occurrence in every composition step.
-/

public section

namespace Purelib.Data.List.Permutation

universe u v
variable {Alpha : Type u} {Beta : Type v}

/-- Every displayed list permutes to itself. -/
theorem refl : (values : List Alpha) → List.Perm values values
  | [] => .nil
  | head :: tail => .cons head (Purelib.Data.List.Permutation.refl tail)

/-- Reverse a retained permutation certificate between two lists. -/
theorem symm {left right : List Alpha} (permutation : List.Perm left right) : List.Perm right left := by
  induction permutation with
  | nil => exact .nil
  | cons head tail ih => exact .cons head ih
  | swap first second tail => exact .swap second first tail
  | trans first second ihFirst ihSecond => exact .trans ihSecond ihFirst

/-- Appending the same displayed prefix preserves a permutation of the tails. -/
theorem append_left (before : List Alpha) {left right : List Alpha} (permutation : List.Perm left right) :
    List.Perm (before ++ left) (before ++ right) := by
  induction before with
  | nil => exact permutation
  | cons head tail ih => exact .cons head ih

/-- Moving a displayed entry across a finite prefix preserves list permutation. -/
theorem move_head (head : Alpha) (before after : List Alpha) :
    List.Perm (head :: (before ++ after)) (before ++ head :: after) := by
  induction before with
  | nil => exact Permutation.refl _
  | cons first tail ih => exact .trans (.swap first head _) (.cons first ih)

/-- Exchanging two displayed list blocks preserves their combined multiplicities.

The original tail remains unchanged. Structural induction moves each head
past the second displayed block, retaining all occurrences in both blocks. -/
theorem append_swap (first second tail : List Alpha) : List.Perm (first ++ second ++ tail) (second ++ first ++ tail) :=
  by
  induction first with
  | nil =>
      have emptyRight : second ++ [] = second := by
        induction second with
        | nil => rfl
        | cons head remaining ih => exact congrArg (List.cons head) ih
      rewrite [List.nil_append, emptyRight]
      exact Permutation.refl _
  | cons head remaining ih =>
      exact (List.Perm.cons head ih).trans (by
        simpa only [List.cons_append, Append.append_assoc] using Permutation.move_head head second (remaining ++ tail))

/-- A list permutation induces a permutation of its finite flat-map outputs.

Each source occurrence contributes its complete retained output block. Induction on
the permutation composes block moves without changing their contents. -/
theorem flatMap (values : Alpha → List Beta) {left right : List Alpha} (permutation : List.Perm left right) :
    List.Perm (left.flatMap values) (right.flatMap values) := by
  induction permutation with
  | nil => exact .nil
  | cons head tail ih => exact Permutation.append_left (values head) ih
  | swap first second tail =>
      simpa only [Flatten.flatMap_cons, Append.append_assoc] using Permutation.append_swap (values second) (values
        first) (tail.flatMap values)
  | trans first second ihFirst ihSecond => exact .trans ihFirst ihSecond

/-- A permutation preserves and reflects membership of every displayed entry.

Induction on the retained permutation transports the original membership
constructors. Adjacent swaps change only the position of the first two
occurrences, retaining every occurrence in their common tail. -/
theorem mem_iff {left right : List Alpha} (permutation : List.Perm left right) (value : Alpha) :
    value ∈ left ↔ value ∈ right := by
  induction permutation with
  | nil => exact Iff.rfl
  | cons head tail ih =>
      constructor
      · intro member
        cases member with
        | head => exact List.Mem.head _
        | tail _ member => exact List.Mem.tail head (ih.mp member)
      · intro member
        cases member with
        | head => exact List.Mem.head _
        | tail _ member => exact List.Mem.tail head (ih.mpr member)
  | swap first second remaining =>
      constructor
      · intro member
        cases member with
        | head => exact List.Mem.tail first (List.Mem.head remaining)
        | tail _ member =>
            cases member with
            | head => exact List.Mem.head _
            | tail _ member => exact List.Mem.tail first (List.Mem.tail second member)
      · intro member
        cases member with
        | head => exact List.Mem.tail second (List.Mem.head remaining)
        | tail _ member =>
            cases member with
            | head => exact List.Mem.head _
            | tail _ member => exact List.Mem.tail second (List.Mem.tail first member)
  | trans first second ihFirst ihSecond => exact ihFirst.trans ihSecond

/-- A permutation preserves the length of its displayed lists.

Each retained head contributes one successor on both sides, and adjacent
swaps retain the same two entries. Composition transports the scalar length
equality through the intermediate list. -/
theorem length_eq {left right : List Alpha} (permutation : List.Perm left right) :
    left.length = right.length := by
  induction permutation with
  | nil => rfl
  | cons head tail ih => exact congrArg Nat.succ ih
  | swap first second remaining => rfl
  | trans first second ihFirst ihSecond => exact ihFirst.trans ihSecond

/-- Removing the same displayed occurrence preserves the remaining permutation.

The two inputs retain explicit prefixes and suffixes around the original
occurrence. Permutation induction transports those decompositions, including
a witnessed intermediate occurrence in each composition step. -/
private theorem remove_same {value : Alpha} {beforeLeft beforeRight afterLeft afterRight : List Alpha} :
    List.Perm (beforeLeft ++ value :: afterLeft) (beforeRight ++ value :: afterRight) →
      List.Perm (beforeLeft ++ afterLeft) (beforeRight ++ afterRight) := by
  suffices ∀ left right (_ : List.Perm left right) {beforeLeft beforeRight afterLeft afterRight},
      beforeLeft ++ value :: afterLeft = left → beforeRight ++ value :: afterRight = right →
        List.Perm (beforeLeft ++ afterLeft) (beforeRight ++ afterRight) from
    (this _ _ · rfl rfl)
  intro left right permutation
  induction permutation using List.Perm.recOnSwap' with
    intro beforeLeft beforeRight afterLeft afterRight leftEq rightEq
  | nil =>
      cases beforeLeft with
      | nil => nomatch leftEq
      | cons head tail => nomatch leftEq
  | cons head permutation ih =>
      cases beforeLeft <;> cases beforeRight <;>
        dsimp at leftEq rightEq <;> injections <;> subst_vars
      · exact permutation
      · exact permutation.trans (Permutation.symm (Permutation.move_head _ _ _))
      · exact (Permutation.move_head _ _ _).trans permutation
      · exact (ih rfl rfl).cons _
  | swap' first second permutation ih =>
      obtain _ | ⟨headLeft, _ | ⟨nextLeft, beforeLeft⟩⟩ := beforeLeft
        <;> obtain _ | ⟨headRight, _ | ⟨nextRight, beforeRight⟩⟩ := beforeRight
        <;> dsimp at leftEq rightEq <;> injections <;> subst_vars
        <;> try exact permutation.cons _
      · exact (permutation.trans (Permutation.symm (Permutation.move_head _ _ _))).cons headRight
      · exact ((permutation.trans (Permutation.symm (Permutation.move_head _ _ _))).cons _).trans (.swap _ _ _)
      · exact ((Permutation.move_head _ _ _).trans permutation).cons headLeft
      · exact (List.Perm.swap _ _ _).trans (((Permutation.move_head _ _ _).trans permutation).cons headRight)
      · exact (ih rfl rfl).swap' _ _
  | trans first second ihFirst ihSecond =>
      subst leftEq rightEq
      have member : value ∈ beforeLeft ++ value :: afterLeft :=
        Membership.mem_append.mpr (Or.inr (List.Mem.head afterLeft))
      obtain ⟨beforeMiddle, afterMiddle, equal⟩ :=
        Membership.split_of_mem ((Permutation.mem_iff first value).mp member)
      cases equal
      exact (ihFirst rfl rfl).trans (ihSecond rfl rfl)

/-- Cancelling a common displayed head preserves permutation of the tails.

The original head is removed from both retained lists. No equality decision
or selected replacement occurrence is needed to transport their permutation. -/
theorem cons_inv {head : Alpha} {left right : List Alpha}
    (permutation : List.Perm (head :: left) (head :: right)) : List.Perm left right :=
  remove_same (beforeLeft := []) (beforeRight := []) permutation

/-- A permutation transports duplicate-freeness to its target list.

Each original head remains distinct from the transported tail. Adjacent
swaps retain the same two inequalities and their unchanged duplicate-free
tail, while composition transports the original certificate successively. -/
theorem nodup {left right : List Alpha} (permutation : List.Perm left right) (unique : left.Nodup) : right.Nodup := by
  induction permutation with
  | nil => exact .nil
  | cons head tail ih =>
      rcases List.pairwise_cons.mp unique with ⟨fresh, remaining⟩
      exact List.pairwise_cons.mpr ⟨fun value member => fresh value ((Permutation.mem_iff tail value).mpr member), ih
        remaining⟩
  | swap first second remaining =>
      rcases List.pairwise_cons.mp unique with ⟨firstFresh, restUnique⟩
      rcases List.pairwise_cons.mp restUnique with ⟨secondFresh, tailUnique⟩
      apply List.pairwise_cons.mpr
      constructor
      · intro value member
        rcases Membership.mem_cons.mp member with equal | member
        · cases equal
          exact Ne.symm (firstFresh first List.mem_cons_self)
        · exact secondFresh value member
      · exact List.pairwise_cons.mpr ⟨fun value member => firstFresh value (List.mem_cons_of_mem _ member), tailUnique⟩
  | trans first second ihFirst ihSecond => exact ihSecond (ihFirst unique)

open Purelib.Data.List.Permutation in
/-- Duplicate-freeness of an appended list certifies its two original blocks.

The retained blocks are individually duplicate-free. Every occurrence in
the first block differs from every occurrence in the second, with the
cross-block inequality supplied by the original list's head relations. -/
theorem nodup_append_parts : ∀ {left right : List Alpha}, (left ++ right).Nodup →
    left.Nodup ∧ right.Nodup ∧ ∀ first ∈ left, ∀ second ∈ right, first ≠ second
  | [], _, unique => ⟨.nil, unique, fun _ member => (List.not_mem_nil member).elim⟩
  | head :: tail, right, unique => by
      rcases List.pairwise_cons.mp unique with ⟨headFresh, remaining⟩
      rcases nodup_append_parts remaining with ⟨tailUnique, rightUnique, cross⟩
      refine ⟨List.pairwise_cons.mpr ⟨fun value member => headFresh value (Membership.mem_append.mpr (Or.inl member)),
        tailUnique⟩,
        rightUnique, ?_⟩
      intro first member second secondMember
      rcases Membership.mem_cons.mp member with equal | member
      · cases equal
        exact headFresh second (Membership.mem_append.mpr (Or.inr secondMember))
      · exact cross first member second secondMember

/-- Duplicate-free lists with the same members retain a permutation certificate.

Membership supplies an actual split of the target at each retained source head.
Moving that occurrence to the front and using both freshness certificates
reduces the claim to the original two tails. -/
theorem of_nodup_mem_iff : ∀ {left right : List Alpha},
    left.Nodup → right.Nodup → (∀ value, value ∈ left ↔ value ∈ right) →
    List.Perm left right
  | [], right, _, _, members => by
      cases right with
      | nil => exact .nil
      | cons head tail => exact False.elim (List.not_mem_nil ((members head).mpr (List.Mem.head tail)))
  | head :: tail, right, leftUnique, rightUnique, members => by
      obtain ⟨before, after, split⟩ := Membership.split_of_mem ((members head).mp (List.Mem.head tail))
      cases split
      have moved : List.Perm (before ++ head :: after) (head :: (before ++ after)) :=
        Permutation.symm (Permutation.move_head head before after)
      have rightParts := List.pairwise_cons.mp (Permutation.nodup moved rightUnique)
      have leftParts := List.pairwise_cons.mp leftUnique
      have tails : ∀ value, value ∈ tail ↔ value ∈ before ++ after := by
        intro value
        constructor
        · intro member
          have inRight := (Permutation.mem_iff moved value).mp
            ((members value).mp (List.Mem.tail head member))
          cases inRight with
          | head => exact False.elim (leftParts.1 head member rfl)
          | tail _ retained => exact retained
        · intro member
          have inLeft := (members value).mpr ((Permutation.mem_iff moved value).mpr
            (List.Mem.tail head member))
          cases inLeft with
          | head => exact False.elim (rightParts.1 head member rfl)
          | tail _ retained => exact retained
      exact (List.Perm.cons head (of_nodup_mem_iff leftParts.2 rightParts.2 tails)).trans
        (Permutation.symm moved)

/-- A retained permutation preserves a product with associative commutative multiplication.

The finite product uses the supplied multiplication and unit. Explicit scalar
associativity and commutativity identify the adjacent swapped heads; composition
then transports the same original product through the intermediate list. -/
theorem prod_eq [Mul Alpha] [One Alpha]
    (mulAssoc : ∀ first second third : Alpha,
      (first * second) * third = first * (second * third))
    (mulComm : ∀ first second : Alpha, first * second = second * first)
    {left right : List Alpha} (permutation : List.Perm left right) : left.prod = right.prod := by
  induction permutation with
  | nil => rfl
  | cons head permutation ih => exact congrArg (fun value => head * value) ih
  | swap first second tail =>
      change second * (first * tail.prod) = first * (second * tail.prod)
      exact (mulAssoc second first tail.prod).symm.trans
        ((congrArg (fun value => value * tail.prod) (mulComm second first)).trans
          (mulAssoc first second tail.prod))
  | trans first second ihFirst ihSecond => exact ihFirst.trans ihSecond

/-- Every entry of a materialized finite family retains its original source index.

Membership follows the original bounded right-fold loop used by List.ofFn.
Each step prepends the original indexed value and retains the existing
accumulator, without changing the materialized family or its index bounds. -/
theorem ofFn_mem {size : Nat} (value : Fin size → Alpha) (index : Fin size) : value index ∈ List.ofFn value := by
  have cacheMember : ∀ (fuel : Nat) (bound : fuel ≤ size) (cache : List Alpha)
      {entry : Alpha}, entry ∈ cache →
        entry ∈ Fin.foldr.loop size (fun index tail => value index :: tail) fuel bound cache := by
    intro fuel
    induction fuel with
    | zero => intro bound cache entry member; exact member
    | succ fuel ih =>
        intro bound cache entry member
        change entry ∈ Fin.foldr.loop size (fun index tail => value index :: tail)
          fuel (Nat.le_of_lt bound) (value ⟨fuel, bound⟩ :: cache)
        exact ih _ _ (List.Mem.tail _ member)
  have indexedMember : ∀ (fuel : Nat) (bound : fuel ≤ size) (cache : List Alpha),
      index.val < fuel →
        value index ∈ Fin.foldr.loop size (fun index tail => value index :: tail) fuel bound cache := by
    intro fuel
    induction fuel with
    | zero =>
        intro bound cache impossible
        exact (Nat.not_lt_zero index.val impossible).elim
    | succ fuel ih =>
        intro bound cache retained
        change value index ∈ Fin.foldr.loop size (fun index tail => value index :: tail)
          fuel (Nat.le_of_lt bound) (value ⟨fuel, bound⟩ :: cache)
        by_cases last : index.val = fuel
        · have equal : (⟨fuel, bound⟩ : Fin size) = index := Fin.ext last.symm
          rw [← equal]
          exact cacheMember fuel (Nat.le_of_lt bound) _ (List.Mem.head cache)
        · exact ih _ _ (Nat.lt_of_le_of_ne (Nat.le_of_lt_succ retained) last)
  change value index ∈ Fin.foldr.loop size (fun index tail => value index :: tail)
    size (Nat.le_refl size) []
  exact indexedMember size (Nat.le_refl size) [] index.isLt

set_option genInjectivity false in
/-- Retain a list with one selected occurrence removed and its permutation certificate.

The remaining list is executable data. The stored permutation moves exactly the
requested occurrence to the front of the original list. -/
private structure Extraction (needle : Alpha) (values : List Alpha) where
  /-- The original list with the selected matching occurrence removed. -/ remaining : List Alpha
  /-- Moving the selected occurrence to the front permutes the original list to this retained remainder. -/ ordering :
    List.Perm values (needle :: remaining)

constructive_injectivity Extraction

open Purelib.Data.List.Permutation in
set_option genInjectivity false in
/-- Return a certified occurrence extraction or evidence that the requested value is
absent.

Both outcomes concern the exact input list and target. Successful extraction retains
the remaining list and its ordering certificate. -/
private inductive ExtractionResult (needle : Alpha) (values : List Alpha) where
  /-- The requested value has no occurrence in the original list. -/ | missing (absent : needle ∉ values)
  /-- Retain the computed remainder and its extraction permutation. -/ | found (extraction : Extraction needle values)

constructive_injectivity ExtractionResult

open Purelib.Data.List.Permutation in
/-- Scan a finite list for one occurrence and retain the certified remainder.

Decidable equality selects the first matching head. Failure proves absence from the
entire input; success preserves all remaining occurrences and their order. -/
private def extract [DecidableEq Alpha] (needle : Alpha) : (values : List Alpha) → ExtractionResult needle values
  | [] => .missing (fun member => List.not_mem_nil member)
  | head :: tail =>
      if equal : head = needle then .found ⟨tail, by cases equal; exact Permutation.refl _⟩
      else
        match Purelib.Data.List.Permutation.extract needle tail with
        | .missing absent => .missing (by
            intro member
            rcases Membership.mem_cons.mp member with same | remaining
            · exact equal same.symm
            · exact absent remaining)
        | .found found => .found
            ⟨head :: found.remaining, (List.Perm.cons head found.ordering).trans (.swap _ _ _)⟩

/-- Retain a permutation proof between the two supplied finite lists.

The certificate refers to the exact source and target lists, preserving occurrence
multiplicity without identifying their order. -/
structure Certificate (left right : List Alpha) : Type u where
  /-- The two indexed lists have exactly the same occurrences up to permutation. -/ permutation : List.Perm left right

set_option genInjectivity false in
/-- Retain a finite obstruction to permutation of two displayed lists.

An unmatched target suffix or a missing source occurrence closes the obstruction.
Matched steps preserve the actual extraction remainder and the recursive failure
certificate. -/
inductive Invalid : List Alpha → List Alpha → Type u where
  /-- The source is exhausted while the target still contains a displayed occurrence. -/ | excess (head : Alpha) (tail :
    List Alpha) : Purelib.Data.List.Permutation.Invalid [] (head :: tail)
  /-- The next source occurrence is absent from the retained target list. -/ | missing (head : Alpha) (tail right : List
    Alpha) (absent : head ∉ right) : Purelib.Data.List.Permutation.Invalid (head :: tail) right
  /-- A matched occurrence leaves the displayed remainder with its own retained obstruction. -/ | matched (head : Alpha)
    (tail right remaining : List Alpha)
      (ordering : List.Perm right (head :: remaining)) (invalid : Purelib.Data.List.Permutation.Invalid tail remaining)
        : Purelib.Data.List.Permutation.Invalid (head :: tail) right

constructive_injectivity Invalid

open Purelib.Data.List.Permutation
/-- Every retained permutation obstruction rules out permutation of its indexed lists.

Induction through matched extraction steps transports a hypothetical permutation to
the retained remainder until the explicit excess or missing occurrence contradicts
it. -/
theorem Invalid.notPerm {left right : List Alpha} (invalid : Invalid left right) : ¬ List.Perm left right := by
  induction invalid with
  | excess head tail =>
      intro permutation
      exact Nat.noConfusion (Permutation.length_eq permutation)
  | missing head tail right absent =>
      intro permutation
      exact absent ((Permutation.mem_iff permutation head).mp List.mem_cons_self)
  | matched head tail right remaining ordering invalid ih =>
      intro permutation
      exact ih (Permutation.cons_inv (permutation.trans ordering))

/-- Decide permutation by repeatedly extracting matching occurrences from the target
list.

Success returns a certificate for the exact input lists. Failure retains an indexed
obstruction, including each actual remainder used by the recursive finite check. -/
@[expose] def certify [DecidableEq Alpha] : (left right : List Alpha) → Except (Invalid left right) (Certificate left
  right)
  | [], [] => .ok ⟨.nil⟩
  | [], head :: tail => .error (.excess head tail)
  | head :: tail, right =>
      let rec extractHere : (values : List Alpha) →
          Except { token : Unit // head ∉ values }
            { remaining : List Alpha // List.Perm values (head :: remaining) }
        | [] => .error ⟨(), fun member => List.not_mem_nil member⟩
        | first :: rest =>
            if equal : first = head then
              .ok ⟨rest, by cases equal; exact Permutation.refl _⟩
            else
              match extractHere rest with
              | .error ⟨_, absent⟩ => .error ⟨(), by
                  intro member
                  rcases Membership.mem_cons.mp member with same | remaining
                  · exact equal same.symm
                  · exact absent remaining⟩
              | .ok ⟨remaining, ordering⟩ => .ok
                  ⟨first :: remaining,
                    (List.Perm.cons first ordering).trans (.swap _ _ _)⟩
      match extractHere right with
      | .error ⟨_, absent⟩ => .error (.missing head tail right absent)
      | .ok ⟨remaining, ordering⟩ =>
          match Purelib.Data.List.Permutation.certify tail remaining with
          | .error invalid => .error (.matched head tail right remaining ordering invalid)
          | .ok certificate => .ok
              ⟨(List.Perm.cons head certificate.permutation).trans (Permutation.symm ordering)⟩

end Purelib.Data.List.Permutation

end
