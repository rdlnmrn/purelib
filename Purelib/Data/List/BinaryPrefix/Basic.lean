module
import Purelib.Data.List.Append

section
public section
namespace Purelib.Data.List.BinaryPrefix.Basic
/-- A finite Boolean word represented by its explicit ordered list of bits. -/
abbrev SourceEncodingEncoderWordAlias := List Bool
end Purelib.Data.List.BinaryPrefix.Basic

end

section
section
section
public section
namespace Purelib.Data.List.BinaryPrefix.Basic
/-- A finite Boolean word represented by its explicit ordered list of bits. -/
abbrev SourceEncodingCylinderWordAlias := List Bool

end Purelib.Data.List.BinaryPrefix.Basic
end
end

end

section
section
section
public section
namespace Purelib.Data.List.BinaryPrefix.Basic
/-- A finite Boolean word represented by its explicit ordered list of bits. -/
abbrev SourceEncodingDecoderWordAlias := List Bool

end Purelib.Data.List.BinaryPrefix.Basic
end
end

end

section
section
section
public section
namespace Purelib.Data.List.BinaryPrefix.Basic

open Purelib.Data.List
/-- A finite Boolean word represented by its explicit ordered list of bits. -/
abbrev SourceEncodingPrefixMinimaxWordAlias := List Bool
end Purelib.Data.List.BinaryPrefix.Basic
end

end

section
section
section
section
section
section
section
section
section
section
section
section
public section
namespace Purelib.Data.List.BinaryPrefix.Basic

/-- A finite Boolean word represented by its explicit ordered list of bits. -/
abbrev SourceEncodingPrefixTowerWordAlias := List Bool
end Purelib.Data.List.BinaryPrefix.Basic
end
end

end

section
section
section
section
section
public section
namespace Purelib.Data.List.BinaryPrefix.Basic
/-- A finite Boolean word represented by its explicit ordered list of bits. -/
abbrev SourceEncodingRawParserSemanticsWordAlias := List Bool

end Purelib.Data.List.BinaryPrefix.Basic
end

end

section
section
section
section
public section
namespace Purelib.Data.List.BinaryPrefix.Basic
/-- A finite Boolean word represented by its explicit ordered list of bits. -/
abbrev SourceEncodingRawParserWordAlias := List Bool
end Purelib.Data.List.BinaryPrefix.Basic
end

end

section
section
section
section
section
section
public section
namespace Purelib.Data.List.BinaryPrefix.Basic
/-- A finite Boolean word represented by its explicit ordered list of bits. -/
abbrev SourceEncodingTerminalPaddingWordAlias := List Bool

end Purelib.Data.List.BinaryPrefix.Basic
end

end

section
section
section
section
section
section
section
public section
namespace Purelib.Data.List.BinaryPrefix.Basic

/-- A finite Boolean word represented by its explicit ordered list of bits. -/
abbrev SourceEncodingTransducerWordAlias := List Bool
end Purelib.Data.List.BinaryPrefix.Basic
end

end

section
section
section
section
section
section
section
section
section
public section
namespace Purelib.Data.List.BinaryPrefix.Basic
/-- A finite Boolean word represented by its explicit ordered list of bits. -/
abbrev SourcePersistentCCLWordAlias := List Bool
end Purelib.Data.List.BinaryPrefix.Basic
end

end

section
section
section
section
section
section
section
section
section
section
public section
namespace Purelib.Data.List.BinaryPrefix.Basic
/-- A finite Boolean word represented by its explicit ordered list of bits. -/
abbrev SourcePersistentStrictWordAlias := List Bool

end Purelib.Data.List.BinaryPrefix.Basic
end

end

section
section
section
public section
namespace Purelib.Data.List.BinaryPrefix.Basic

open Purelib.Data.List.BinaryPrefix.Basic in
/-- Compute the longest common prefix of two finite Boolean words.

Equal leading bits are retained recursively. The first disagreement or an exhausted
input ends the shared prefix. -/
@[expose] def lcp :
    SourceEncodingPrefixMinimaxWordAlias → SourceEncodingPrefixMinimaxWordAlias →
      SourceEncodingPrefixMinimaxWordAlias
  | [], _ => []
  | leftBit :: leftRest, right =>
      List.casesOn right [] fun rightBit rightRest =>
        if leftBit = rightBit then
          leftBit :: lcp leftRest rightRest
        else []

end Purelib.Data.List.BinaryPrefix.Basic
end

end

section
section
section
public section
namespace Purelib.Data.List.BinaryPrefix.Basic

open Purelib.Data.List.BinaryPrefix in
open Purelib.Data.List.BinaryPrefix.Basic in
/-- Extending a rejected right prefix does not change its common prefix with the left
word.

The supplied stem must fail to be a prefix of the left word. Their first disagreement
or left exhaustion therefore occurs before any appended suffix is examined. -/
theorem lcp_append_right_of_not_prefix (left stem suffix :
  SourceEncodingPrefixMinimaxWordAlias)
    (notPrefix : ¬stem.IsPrefix left) :
    lcp left (stem ++ suffix) = lcp left stem := by
  induction stem generalizing left with
  | nil => exact (notPrefix List.nil_prefix).elim
  | cons prefixBit prefixRest ih =>
      cases left with
      | nil => rfl
      | cons leftBit leftRest =>
          change (if leftBit = prefixBit then
              leftBit :: lcp leftRest (prefixRest ++ suffix) else []) =
            (if leftBit = prefixBit then leftBit :: lcp leftRest prefixRest else [])
          by_cases equal : leftBit = prefixBit
          · have tailNotPrefix : ¬prefixRest.IsPrefix leftRest := by
              intro tailPrefix
              rcases tailPrefix with ⟨remaining, identity⟩
              apply notPrefix
              cases equal
              exact ⟨remaining, congrArg (List.cons prefixBit) identity⟩
            rw [if_pos equal, if_pos equal]
            exact congrArg (List.cons leftBit) (ih leftRest tailNotPrefix)
          · rw [if_neg equal, if_neg equal]

end Purelib.Data.List.BinaryPrefix.Basic
end

end

section
section
section
public section
namespace Purelib.Data.List.BinaryPrefix.Basic

open Purelib.Data.List.BinaryPrefix in
open Purelib.Data.List.BinaryPrefix.Basic in
/-- Prepending the same stem to both words prepends it to their longest common prefix. -/
theorem lcp_append_same (stem left right :
  SourceEncodingPrefixMinimaxWordAlias) :
    lcp (stem ++ left) (stem ++ right) = stem ++ lcp left right := by
  induction stem with
  | nil => rfl
  | cons bit remaining ih =>
      change (if bit = bit then
          bit :: lcp (remaining ++ left) (remaining ++ right) else []) =
        bit :: (remaining ++ lcp left right)
      rw [if_pos (rfl : bit = bit)]
      exact congrArg (List.cons bit) ih

end Purelib.Data.List.BinaryPrefix.Basic
end

end

section
section
section
public section
namespace Purelib.Data.List.BinaryPrefix.Basic

open Purelib.Data.List.BinaryPrefix in
open Purelib.Data.List.BinaryPrefix.Basic in
/-- The empty left word has empty common prefix with every right word. -/
@[simp] theorem lcp_nil_left (word : SourceEncodingPrefixMinimaxWordAlias) :
  lcp [] word = [] := rfl
end Purelib.Data.List.BinaryPrefix.Basic
end

end

section
section
section
public section
namespace Purelib.Data.List.BinaryPrefix.Basic
open Purelib.Data.List.BinaryPrefix in
open Purelib.Data.List.BinaryPrefix.Basic in
/-- Every left word has empty common prefix with the empty right word. -/
@[simp] theorem lcp_nil_right (word : SourceEncodingPrefixMinimaxWordAlias)
  : lcp word [] = [] := by
  cases word <;> rfl
end Purelib.Data.List.BinaryPrefix.Basic
end

end

section
section
section
public section
namespace Purelib.Data.List.BinaryPrefix.Basic

open Purelib.Data.List.BinaryPrefix in
open Purelib.Data.List.BinaryPrefix.Basic in
/-- The computed longest common prefix is a prefix of the left input. -/
theorem lcp_prefix_left (left right : SourceEncodingPrefixMinimaxWordAlias)
  :
    (lcp left right).IsPrefix left := by
  induction left generalizing right with
  | nil => exact ⟨[], rfl⟩
  | cons leftBit leftRest ih =>
      cases right with
      | nil => exact ⟨leftBit :: leftRest, rfl⟩
      | cons rightBit rightRest =>
          change (if leftBit = rightBit then leftBit :: lcp leftRest rightRest else []).IsPrefix _
          by_cases equal : leftBit = rightBit
          · rw [if_pos equal]
            rcases ih rightRest with ⟨suffix, identity⟩
            exact ⟨suffix, congrArg (List.cons leftBit) identity⟩
          · rw [if_neg equal]
            exact ⟨leftBit :: leftRest, rfl⟩

end Purelib.Data.List.BinaryPrefix.Basic
end

end

section
section
section
public section
namespace Purelib.Data.List.BinaryPrefix.Basic

open Purelib.Data.List.BinaryPrefix in
open Purelib.Data.List.BinaryPrefix.Basic in
/-- The computed longest common prefix is a prefix of the right input. -/
theorem lcp_prefix_right (left right : SourceEncodingPrefixMinimaxWordAlias)
  :
    (lcp left right).IsPrefix right := by
  induction left generalizing right with
  | nil => exact ⟨right, rfl⟩
  | cons leftBit leftRest ih =>
      cases right with
      | nil => exact ⟨[], rfl⟩
      | cons rightBit rightRest =>
          change (if leftBit = rightBit then leftBit :: lcp leftRest rightRest else []).IsPrefix _
          by_cases equal : leftBit = rightBit
          · rw [if_pos equal]
            rcases ih rightRest with ⟨suffix, identity⟩
            cases equal
            exact ⟨suffix, congrArg (List.cons leftBit) identity⟩
          · rw [if_neg equal]
            exact ⟨rightBit :: rightRest, rfl⟩

end Purelib.Data.List.BinaryPrefix.Basic
end

end

section
section
section
section
section
section
section
section
public section
namespace Purelib.Data.List.BinaryPrefix

/-- A finite Boolean word represented by its explicit ordered list of bits. -/
abbrev CCLMeasureWord := List Bool
end Purelib.Data.List.BinaryPrefix
end

end

section
section
public section
namespace Purelib.CCL.Boundary.Formula
end Purelib.CCL.Boundary.Formula
end

end
