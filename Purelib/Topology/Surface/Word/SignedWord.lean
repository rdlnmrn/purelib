module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Vector.Basic
import Purelib.Data.Int.Arithmetic

public import Purelib.Topology.Surface.Word.Pairing

public section

/-!
# Finite signed letters and exact occurrence counts

These counts distinguish the two orientations of every generator. In
particular, an edge lookup cannot discharge multiplicity by membership alone.
-/

namespace Purelib.Topology.Surface.Word.SignedWord
open Purelib
open Purelib.Topology.Surface.Word

set_option genInjectivity false in
/-- An original finite generator index with an explicit traversal orientation.

The bounded index identifies the retained generator, while the Boolean field
records the orientation of this ordered occurrence. Constructor certificates
identify both original fields without changing the finite generator bound. -/
structure SignedGenerator (count : Nat) where
  /-- Original bounded generator index. -/ index : Fin count
  /-- Whether the occurrence traverses its generator negatively. -/ reversed : Bool
  -- Closed occurrence checks reduce the original equality procedure.
  deriving @[expose] DecidableEq

constructive_injectivity SignedGenerator

namespace SignedGenerator

variable {count : Nat}

open Purelib.Data.Int

/-- Materialize the signed unit coefficient row of a generator occurrence.

The original bounded generator index selects one coefficient slot. Its
retained orientation chooses positive or negative one, and every other
slot is zero in the same finite vector. -/
@[expose] def coefficients (letter : SignedWord.SignedGenerator count) : Pairing.Coefficients count :=
  Data.Vector.Basic.vectorOfFn fun index =>
    if index = letter.index then (if letter.reversed then -1 else 1) else 0

/-- Shift the retained generator index past a new leading slot without changing orientation. -/
@[expose] def shift (letter : SignedWord.SignedGenerator count) : SignedWord.SignedGenerator (count + 1) :=
  ⟨letter.index.succ, letter.reversed⟩

/-- Shifting signed generators preserves their identity injectively. -/
theorem shift_injective {first second : SignedWord.SignedGenerator count} (equal : first.shift = second.shift) : first =
  second := by
  have indices := congrArg SignedWord.SignedGenerator.index equal
  have orientations := congrArg SignedWord.SignedGenerator.reversed equal
  cases first with
  | mk firstIndex firstReversed =>
      cases second with
      | mk secondIndex secondReversed =>
          exact congrArg₂ SignedWord.SignedGenerator.mk (Fin.ext (Nat.succ.inj (congrArg Fin.val indices))) orientations

section
open Purelib.Topology.Surface.Word.SignedWord.SignedGenerator
/-- Count exact signed occurrences in the original ordered word.

Each original letter contributes its zero-or-one identity indicator. The
recursive tail count retains the order and multiplicity of the supplied
finite word, including the two distinct generator orientations. -/
@[expose] def occurrences (needle : SignedWord.SignedGenerator count) : List (SignedWord.SignedGenerator count) → Nat
  | [] => 0
  | letter :: rest => (if letter = needle then 1 else 0) + occurrences needle rest

/-- Occurrence-preserving word permutations preserve each signed multiplicity.

Induction on the supplied finite permutation retains each original signed
letter. An adjacent swap only exchanges the two scalar head indicators;
their unchanged tail count is transported by natural addition laws. -/
theorem occurrences_perm (needle : SignedWord.SignedGenerator count) {first second : List (SignedWord.SignedGenerator
  count)}
    (ordering : List.Perm first second) : occurrences needle first = occurrences needle second := by
  induction ordering with
  | nil => rfl
  | cons head tail ih => exact congrArg (fun total => (if head = needle then 1 else 0) + total) ih
  | swap first second rest =>
      change (if second = needle then 1 else 0) +
        ((if first = needle then 1 else 0) + occurrences needle rest) =
        (if first = needle then 1 else 0) +
          ((if second = needle then 1 else 0) + occurrences needle rest)
      exact Nat.add_left_comm _ _ _
  | trans first second ihFirst ihSecond => exact ihFirst.trans ihSecond

/-- Shifted words contain neither orientation of the newly inserted zero index.

Every retained shifted index has a successor natural value. Projecting a
putative equality with the new zero index would identify that successor
with zero, independently of the original traversal orientation. -/
theorem occurrences_shift_zero (reversed : Bool) (word : List (SignedWord.SignedGenerator count)) :
    occurrences ⟨0, reversed⟩ (word.map SignedGenerator.shift) = 0 := by
  induction word with
  | nil => rfl
  | cons letter rest ih =>
      have different : letter.shift ≠ (⟨0, reversed⟩ : SignedWord.SignedGenerator (count + 1)) := by
        intro equal
        have values := congrArg (fun value => value.index.val) equal
        exact Nat.noConfusion values
      rewrite [List.map_cons, occurrences, if_neg different, ih]
      rfl

/-- Shifting both a signed letter and the word preserves its multiplicity. -/
theorem occurrences_shift (needle : SignedWord.SignedGenerator count) (word : List (SignedWord.SignedGenerator count)) :
    occurrences needle.shift (word.map SignedGenerator.shift) = occurrences needle word := by
  induction word with
  | nil => rfl
  | cons letter rest ih =>
      rw [List.map_cons, occurrences, occurrences, ih]
      by_cases equal : letter = needle
      · rw [if_pos equal, if_pos (congrArg SignedGenerator.shift equal)]
      · rw [if_neg equal, if_neg (fun same => equal (SignedGenerator.shift_injective same))]

end

/-- A letter's coefficient is its positive indicator minus its negative indicator.

The retained finite index first selects the coefficient slot. At that same
index, the original orientation selects one of the two signed constructor
indicators; a different index makes both indicators zero. -/
theorem coefficient_eq_counts (letter : SignedWord.SignedGenerator count) (index : Fin count) :
    letter.coefficients index =
      (if letter = ⟨index, false⟩ then 1 else 0) - (if letter = ⟨index, true⟩ then 1 else 0) := by
  rw [SignedGenerator.coefficients, Data.Vector.Basic.vectorOfFn_apply]
  cases letter with
  | mk position reversed =>
      by_cases same : position = index
      · cases same
        cases reversed with
        | false =>
            have notNegative : SignedWord.SignedGenerator.mk index false ≠
                SignedWord.SignedGenerator.mk index true := fun equal =>
              Bool.noConfusion (congrArg SignedWord.SignedGenerator.reversed equal)
            change (if index = index then (1 : Int) else 0) =
              (if SignedWord.SignedGenerator.mk index false =
                  SignedWord.SignedGenerator.mk index false then 1 else 0) -
                (if SignedWord.SignedGenerator.mk index false =
                    SignedWord.SignedGenerator.mk index true then 1 else 0)
            rw [if_pos (Eq.refl index),
              if_pos (Eq.refl (SignedWord.SignedGenerator.mk index false)),
              if_neg notNegative]
            rfl
        | true =>
            have notPositive : SignedWord.SignedGenerator.mk index true ≠
                SignedWord.SignedGenerator.mk index false := fun equal =>
              Bool.noConfusion (congrArg SignedWord.SignedGenerator.reversed equal)
            change (if index = index then (-1 : Int) else 0) =
              (if SignedWord.SignedGenerator.mk index true =
                  SignedWord.SignedGenerator.mk index false then 1 else 0) -
                (if SignedWord.SignedGenerator.mk index true =
                    SignedWord.SignedGenerator.mk index true then 1 else 0)
            rw [if_pos (Eq.refl index), if_neg notPositive,
              if_pos (Eq.refl (SignedWord.SignedGenerator.mk index true))]
            rfl
      · have notPositive : SignedWord.SignedGenerator.mk position reversed ≠
            SignedWord.SignedGenerator.mk index false := fun equal =>
          same (congrArg SignedWord.SignedGenerator.index equal)
        have notNegative : SignedWord.SignedGenerator.mk position reversed ≠
            SignedWord.SignedGenerator.mk index true := fun equal =>
          same (congrArg SignedWord.SignedGenerator.index equal)
        rw [if_neg (fun equal => same equal.symm),
          if_neg notPositive, if_neg notNegative]
        rfl

open Purelib.Topology.Surface.Word.SignedWord.SignedGenerator in
/-- A word's total coefficient is its positive multiplicity minus its negative multiplicity.

Each original head letter contributes its two orientation indicators, and
the retained tail contributes its original occurrence counts. Natural casts
preserve these scalar sums; integer addition and negation regroup their difference. -/
theorem total_eq_counts (word : List (SignedWord.SignedGenerator count)) (index : Fin count) :
    Pairing.totalAt (word.map SignedGenerator.coefficients) index =
      (occurrences ⟨index, false⟩ word : Int) - (occurrences ⟨index, true⟩ word : Int) := by
  induction word with
  | nil => rfl
  | cons letter rest ih =>
      rw [List.map_cons, Pairing.totalAt, ih, SignedGenerator.coefficient_eq_counts, occurrences, occurrences,
        Int.natCast_add, Int.natCast_add]
      have indicator (p : Prop) [Decidable p] : ((if p then 1 else 0 : Nat) : Int) = if p then 1 else 0 := by
        by_cases truth : p
        · rw [if_pos truth, if_pos truth]; rfl
        · rw [if_neg truth, if_neg truth]; rfl
      rw [indicator, indicator]
      let positive : Int := if letter = ⟨index, false⟩ then 1 else 0
      let negative : Int := if letter = ⟨index, true⟩ then 1 else 0
      let tailPositive : Int := occurrences ⟨index, false⟩ rest
      let tailNegative : Int := occurrences ⟨index, true⟩ rest
      change (positive + -negative) + (tailPositive + -tailNegative) =
        (positive + tailPositive) + -(negative + tailNegative)
      rewrite [Arithmetic.neg_add, Arithmetic.add_assoc,
        ← Arithmetic.add_assoc (-negative) tailPositive (-tailNegative),
        Arithmetic.add_comm (-negative) tailPositive,
        Arithmetic.add_assoc tailPositive (-negative) (-tailNegative),
        ← Arithmetic.add_assoc]
      rfl

/-- A signed unit row has zero coefficient product at distinct indices.

At most one of the two retained indices can equal the letter's original
generator index. The coefficient at the other index is zero, so direct
integer zero-product laws close either scalar branch. -/
theorem coefficients_mul_of_ne (letter : SignedWord.SignedGenerator count) {row column : Fin count} (different : row ≠
  column) :
    letter.coefficients row * letter.coefficients column = 0 := by
  rw [SignedGenerator.coefficients, Data.Vector.Basic.vectorOfFn_apply, Data.Vector.Basic.vectorOfFn_apply]
  by_cases atRow : row = letter.index
  · have notColumn : column ≠ letter.index := fun equal => different (atRow.trans equal.symm)
    rewrite [if_neg notColumn]
    exact (Arithmetic.mul_comm _ 0).trans (Arithmetic.zero_mul _)
  · rewrite [if_neg atRow]
    exact Arithmetic.zero_mul _

open Purelib.Topology.Surface.Word.SignedWord.SignedGenerator in
/-- A signed letter counted exactly once occurs in the original word.

Structural induction retains the original list. Equality with the displayed
head supplies its membership constructor; otherwise the unchanged tail has
the same unit count and supplies the tail membership constructor. -/
theorem mem_of_occurrences_eq_one {needle : SignedWord.SignedGenerator count}
    {word : List (SignedWord.SignedGenerator count)} (count_eq : occurrences needle word = 1) : needle ∈ word := by
  induction word with
  | nil => exact Nat.noConfusion count_eq
  | cons letter rest inductionHypothesis =>
      change (if letter = needle then 1 else 0) + occurrences needle rest = 1 at count_eq
      by_cases same : letter = needle
      · cases same
        exact List.Mem.head rest
      · rewrite [if_neg same, Nat.zero_add] at count_eq
        exact List.Mem.tail letter (inductionHypothesis count_eq)

end SignedGenerator

end Purelib.Topology.Surface.Word.SignedWord
