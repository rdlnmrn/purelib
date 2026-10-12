module
import Purelib.Data.List.Map
import Purelib.Data.List.Nodup
public import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.List.Flatten

/-!
# Lengths of retained Gaussian coordinate products

Every real occurrence is paired with every imaginary occurrence by the
original nested flat-map and map. The length certificate counts those
ordered pairs without identifying or removing repetitions.
-/
namespace Purelib.Data.List.Cartesian

open Purelib.Data.List

open Purelib.Data.Gaussian.Basic
open Purelib.Data.Rat.Fraction

/-- The list of Gaussian pairs from two rational coordinate lists has product length.

Nested flatMap and map retain every ordered coordinate pair, including
multiplicities, so the resulting length is the product of the two input lengths. -/
public theorem cartesianCandidates_length
    (realCandidates imaginaryCandidates : List Rational) :
    (realCandidates.flatMap fun real =>
      imaginaryCandidates.map fun imaginary =>
        ({ re := real, im := imaginary } : Canonical)).length =
      realCandidates.length * imaginaryCandidates.length :=
  Flatten.length_flatMap_map realCandidates imaginaryCandidates
    (fun real imaginary => ({ re := real, im := imaginary } : Canonical))

/-- Enumerate the ordered Cartesian product of two retained lists.

The original left spine determines the outer order; each right occurrence is
paired with that left entry, preserving every multiplicity. -/
@[expose] public def productList {Alpha Beta : Type} (left : List Alpha) (right : List Beta) : List (Alpha × Beta) :=
  left.flatMap (fun first => right.map (fun last => (first, last)))

/-- Product membership retains both original component occurrences.

Each direction uses the displayed flat-map and map witnesses, with no
choice of another enumeration or removal of repeated entries. -/
public theorem productList_mem {Alpha Beta : Type} {left : List Alpha} {right : List Beta} {pair : Alpha × Beta} :
    pair ∈ productList left right ↔ pair.1 ∈ left ∧ pair.2 ∈ right := by
  constructor
  · intro member
    obtain ⟨first, firstMember, member⟩ := Flatten.mem_flatMap.mp member
    obtain ⟨last, lastMember, equal⟩ := Map.mem_map.mp member
    cases equal
    exact ⟨firstMember, lastMember⟩
  · intro members
    exact Flatten.mem_flatMap.mpr ⟨pair.1, members.1,
      Map.mem_map.mpr ⟨pair.2, members.2, rfl⟩⟩

/-- The ordered Cartesian product has the product of the retained list lengths.

The original flat-map and map retain each occurrence and multiplicity. -/
public theorem productList_length {Alpha Beta : Type} (left : List Alpha) (right : List Beta) :
    (productList left right).length = left.length * right.length :=
  Flatten.length_flatMap_map left right (fun first last => (first, last))

/-- The ordered product of two duplicate-free lists is duplicate-free.

The original head and tail certificates distinguish the left coordinates;
injectivity of pairing distinguishes the retained right coordinates. -/
public theorem productList_nodup {Alpha Beta : Type} (left : List Alpha) (right : List Beta)
    (leftUnique : left.Nodup) (rightUnique : right.Nodup) : (productList left right).Nodup := by
  induction left with
  | nil => exact List.nodup_nil
  | cons head tail ih =>
      obtain ⟨headFresh, tailUnique⟩ := List.pairwise_cons.mp leftUnique
      refine Nodup.nodup_append
        (Nodup.nodup_map_of_injective (fun _ _ equal => congrArg Prod.snd equal) rightUnique)
        (ih tailUnique) ?_
      intro first firstMember last lastMember equal
      obtain ⟨_, _, same⟩ := Map.mem_map.mp firstMember
      have headEq : head = last.1 := congrArg Prod.fst (same.trans equal)
      exact headFresh last.1 (productList_mem.mp lastMember).1 headEq

end Purelib.Data.List.Cartesian
