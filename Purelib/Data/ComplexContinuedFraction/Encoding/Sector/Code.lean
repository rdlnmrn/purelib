module
import Purelib.Data.List.Filter
import Purelib.Data.List.Membership

public import Purelib.Data.ComplexContinuedFraction.Encoding.Sector.Basic
import Purelib.Data.List.BinaryPrefix.Basic
public import Purelib.Data.List.BinaryPrefix.Decision

import Mathlib.Order.Basic
meta import Purelib.Elab.Deriving.Repr
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Choice-free finite eight-sector table

The predicates and selector are the exact finite table from the CCL-1 paper,
specialized to explicit constructive fractions.  The geometric estimates are
proved from displayed polynomial identities and direct order lemmas; no
linear-programming tactic or inherited ordered-field compatibility theorem is
part of their dependency closure.
-/

public section

namespace Purelib.Data.ComplexContinuedFraction.Encoding.Sector
section Sector

-- Retain the original Sector.Sector nominal path.
open Purelib.Data.ComplexContinuedFraction.Encoding in
/-- Encode the retained sector as its three-bit index in counterclockwise order from east. -/
@[expose] def code : Sector →
  List Bool
  | .east => [false, false, false]
  | .northEast => [false, false, true]
  | .north => [false, true, false]
  | .northWest => [false, true, true]
  | .west => [true, false, false]
  | .southWest => [true, false, true]
  | .south => [true, true, false]
  | .southEast => [true, true, true]

-- Retain the original Sector.Sector nominal path.
open Purelib.Data.ComplexContinuedFraction.Encoding in
/-- Every retained sector code has exactly three bits. -/
@[simp] theorem code_length (sector :
  Sector) : sector.code.length = 3 := by
  cases sector <;> rfl
end Sector

end Purelib.Data.ComplexContinuedFraction.Encoding.Sector

/-!
# Finite raw-prefix parser over constructive Gaussian fractions

The completed-block encoder is not enough for a persistent root name: a
request may stop inside a unary header or after only one or two sector bits.
This module records exactly that unfinished syntax, the finite decoder
product, and the finite list of already completed block constraints.  It is
the state needed by the box/CCL next-bit controller; no stream, completion,
or collection of compatible points is formed.
-/

namespace Purelib.Data.ComplexContinuedFraction.Encoding.Sector.Code

set_option genInjectivity false in
/-- Retain zero, one or two leading bits of an unfinished three-bit sector code.

Each constructor stores exactly the bits already read, so finite candidate enumeration preserves the prefix and its
length. -/
inductive SectorBits where
  /-- An unfinished sector code with no retained bits. -/ | zero
  /-- An unfinished sector code retaining its first bit. -/ | one (first : Bool)
  /-- An unfinished sector code retaining its first and second bits. -/ | two (first second : Bool)
deriving DecidableEq

constructive_injectivity SectorBits

derive_exposed_repr Purelib.Data.ComplexContinuedFraction.Encoding.Sector.Code.SectorBits

namespace SectorBits.one

end SectorBits.one
namespace SectorBits.two

end SectorBits.two
namespace SectorBits

open Purelib.Data.ComplexContinuedFraction.Encoding in
open Purelib.Data.List in
/-- Read the exact retained unfinished sector-bit word. -/
@[expose] def word : Sector.Code.SectorBits
  → BinaryPrefix.Basic.SourceEncodingRawParserWordAlias
  | .zero => []
  | .one first => [first]
  | .two first second => [first, second]

open Purelib.Data.ComplexContinuedFraction.Encoding in
/-- The retained sector-bit word has length zero, one or two according to its constructor. -/
@[simp] theorem word_length : ∀ bits :
  Sector.Code.SectorBits,
    bits.word.length = match bits with
      | .zero => 0
      | .one _ => 1
      | .two _ _ => 2
  | .zero => rfl
  | .one _ => rfl
  | .two _ _ => rfl

end SectorBits

section
open Purelib.Data.ComplexContinuedFraction.Encoding
/-- Enumerate the eight sectors in the exact order of their three-bit binary codes. -/
@[expose] def sectorTable : List Sector
  :=
  [.east, .northEast, .north, .northWest,
    .west, .southWest, .south, .southEast]

open Purelib.Data.List in
/-- Filter the retained sector table by the exact unfinished code prefix.

The result keeps table order and includes all sectors whose full code starts with the stored bits; no completion is
selected prematurely. -/
@[expose] def sectorCandidates (bits :
  Sector.Code.SectorBits) : List Sector :=
  Sector.Code.sectorTable.filter fun sector => BinaryPrefix.Decision.isWordPrefix bits.word (code
    sector)

/-- An unfinished sector code leaves exactly eight, four or two candidates according to its retained prefix length. -/
theorem sectorCandidates_length (bits :
  Sector.Code.SectorBits) :
    (Sector.Code.sectorCandidates bits).length = match bits with
      | .zero => 8
      | .one _ => 4
      | .two _ _ => 2 := by
  cases bits with
  | zero => decide
  | one first => cases first <;> decide
  | two first second => cases first <;> cases second <;> decide

/-- The empty sector prefix retains the full ordered sector table. -/
@[simp] theorem sectorCandidates_zero :
    Sector.Code.sectorCandidates .zero = Sector.Code.sectorTable := by
  decide

/-- A leading false bit retains east, northeast, north and northwest in that order. -/
@[simp] theorem sectorCandidates_one_false :
    Sector.Code.sectorCandidates (.one false) =
      [.east, .northEast, .north, .northWest] := by
  decide

/-- A leading true bit retains west, southwest, south and southeast in that order. -/
@[simp] theorem sectorCandidates_one_true :
    Sector.Code.sectorCandidates (.one true) =
      [.west, .southWest, .south, .southEast] := by
  decide

/-- The two false bits retain east and northeast. -/
@[simp] theorem sectorCandidates_two_false_false :
    Sector.Code.sectorCandidates (.two false false) = [.east, .northEast] := by
  decide

/-- The false-true prefix retains north and northwest. -/
@[simp] theorem sectorCandidates_two_false_true :
    Sector.Code.sectorCandidates (.two false true) = [.north, .northWest] := by
  decide

/-- The true-false prefix retains west and southwest. -/
@[simp] theorem sectorCandidates_two_true_false :
    Sector.Code.sectorCandidates (.two true false) = [.west, .southWest] := by
  decide

/-- The two true bits retain south and southeast. -/
@[simp] theorem sectorCandidates_two_true_true :
    Sector.Code.sectorCandidates (.two true true) = [.south, .southEast] := by
  decide

/-- Decode the exact three retained bits into their unique sector. -/
@[expose] def sectorOfBits : Bool → Bool → Bool →
  Sector
  | false, false, false => .east
  | false, false, true => .northEast
  | false, true, false => .north
  | false, true, true => .northWest
  | true, false, false => .west
  | true, false, true => .southWest
  | true, true, false => .south
  | true, true, true => .southEast

/-- Encoding the decoded sector recovers the same three bits. -/
@[simp] theorem sectorOfBits_code (first second third
  : Bool) :
    (Sector.Code.sectorOfBits first second third).code = [first, second, third] := by
  cases first <;> cases second <;> cases third <;> rfl

open Purelib.Data.List in
/-- Filtering the table by a complete three-bit code leaves exactly its decoded sector. -/
theorem completed_sectorCandidates (first second third
  : Bool) :
    Sector.Code.sectorTable.filter
        (fun sector => BinaryPrefix.Decision.isWordPrefix [first, second, third] sector.code) =
      [Sector.Code.sectorOfBits first second third] := by
  cases first <;> cases second <;> cases third <;> decide
end

end Purelib.Data.ComplexContinuedFraction.Encoding.Sector.Code

/-!
# Finite candidates for a local CCL terminal

A represented value can stop immediately before the third sector bit only
when its normalized tail is exactly one of the two sector representatives
compatible with the already-read two-bit fragment.  This module makes those
two candidates explicit.  It is the bounded replacement for repeatedly
excluding arbitrary rational terminal samples.
-/

namespace Purelib.Data.ComplexContinuedFraction.Encoding.Sector.Code.Boundary

open Purelib.Data.ComplexContinuedFraction.Encoding
/-- Every candidate for an empty prefix remains a candidate after some one-bit extension. -/
theorem sectorCandidate_zero_child
    (sector : Sector) (member : sector ∈ Sector.Code.sectorCandidates .zero) :
    ∃ bit, sector ∈ Sector.Code.sectorCandidates (.one bit) := by
  cases sector with
  | east => exact ⟨false, by decide⟩
  | northEast => exact ⟨false, by decide⟩
  | north => exact ⟨false, by decide⟩
  | northWest => exact ⟨false, by decide⟩
  | west => exact ⟨true, by decide⟩
  | southWest => exact ⟨true, by decide⟩
  | south => exact ⟨true, by decide⟩
  | southEast => exact ⟨true, by decide⟩

/-- Every candidate for a one-bit prefix remains a candidate after some two-bit extension. -/
theorem sectorCandidate_one_child
    (first : Bool) (sector : Sector)
    (member : sector ∈ Sector.Code.sectorCandidates (.one first)) :
    ∃ bit, sector ∈ Sector.Code.sectorCandidates (.two first bit) := by
  cases first <;> cases sector
  all_goals first
    | exact ⟨false, by decide⟩
    | exact ⟨true, by decide⟩
    | exact False.elim (by revert member; decide)

end Purelib.Data.ComplexContinuedFraction.Encoding.Sector.Code.Boundary

/-!
# Affine semantics of constructive raw-parser states

Parser constraints are evaluated on the current affine tail.  These finite
algebraic lemmas prove that decoder homographies compose in parser order and
that completing a raw block preserves the represented original input.
-/

namespace Purelib.Data.ComplexContinuedFraction.Encoding.Sector.Code

open Purelib.Data.ComplexContinuedFraction.Encoding in
/-- The sector decoded from three bits belongs to the candidates for its first two bits. -/
theorem sectorOfBits_mem_two_candidates (first second
  third : Bool) :
    Sector.Code.sectorOfBits first second third ∈
      Sector.Code.sectorCandidates (.two first second) := by
  cases first <;> cases second <;> cases third <;> decide

open Purelib.Data.ComplexContinuedFraction.Encoding in
open Purelib.Data.List in
/-- Extending an unfinished code prefix can only remove candidates. -/
theorem sectorCandidates_mono
    {earlier later : Sector.Code.SectorBits}
    (codePrefix : BinaryPrefix.Decision.isWordPrefix earlier.word later.word = true)
    {sector : Sector}
    (member : sector ∈ Sector.Code.sectorCandidates later) :
    sector ∈ Sector.Code.sectorCandidates earlier := by
  rcases Purelib.Data.List.Filter.mem_filter.mp member with ⟨tableMember, laterPrefix⟩
  apply Purelib.Data.List.Filter.mem_filter.mpr
  refine ⟨tableMember, ?_⟩
  exact BinaryPrefix.Decision.isWordPrefix_trans codePrefix laterPrefix
end Purelib.Data.ComplexContinuedFraction.Encoding.Sector.Code

end
