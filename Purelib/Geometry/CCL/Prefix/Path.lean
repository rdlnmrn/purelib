module

public import Purelib.Geometry.CCL.Prefix.Step
import Purelib.Data.List.Append
import Purelib.Geometry.Rational.Box.Refinement

/-!
# Finite proper-box continuation of retained raw CCL prefixes

Structural recursion on the requested bit count constructs successive
proper prefix extensions. The retained path keeps each actual geometric
step and its caches, the exact new suffix and the enclosure refinement laws.
-/

public section

namespace Purelib.Geometry.CCL.Prefix

open Purelib.Data
open Purelib.Data.CCL
open Purelib.Geometry

set_option genInjectivity false in
/-- Retain the actual sequence of proper geometric extensions for one original prefix and finite bit request.

Each step owns its original earlier enclosure, child formulas, rational
sample and sign payments. The remaining path starts at that step's exact
returned enclosure, preserving every earlier word and actual cache.
-/
inductive Path : (previous : Encoding.Prefix.Enclosure) → Nat → Type where
  /-- A zero-bit request retains the original enclosure unchanged. -/ | nil (previous : Encoding.Prefix.Enclosure) :
    Path previous 0
  /-- Retain one actual next-bit construction and its exact remaining continuation. -/ | cons
    {previous : Encoding.Prefix.Enclosure} {count : Nat} (step : Step previous) (remaining : Path step.next count) :
    Path previous (count + 1)

namespace Path

/-- Compute a finite proper-box continuation by structural recursion on the exact additional-bit request. -/
def build (previous : Encoding.Prefix.Enclosure) (count : Nat) : Path previous count :=
  match count with
  | 0 => .nil previous
  | count + 1 =>
      let step := Step.build previous
      .cons step (build step.next count)
termination_by structural count

/-- Read the actual last retained enclosure without repeating any geometric step. -/
@[expose] def result {previous : Encoding.Prefix.Enclosure} {count : Nat} (path : Path previous count) :
    Encoding.Prefix.Enclosure :=
  match path with
  | .nil original => original
  | .cons _ remaining => remaining.result

/-- Read the actual newly selected Boolean suffix in its original order. -/
@[expose] def bits {previous : Encoding.Prefix.Enclosure} {count : Nat} (path : Path previous count) : List Bool :=
  match path with
  | .nil _ => []
  | .cons step remaining => step.choice.bit :: remaining.bits

/-- The retained new suffix has exactly the requested additional-bit length. -/
theorem bits_length {previous : Encoding.Prefix.Enclosure} {count : Nat} (path : Path previous count) :
    path.bits.length = count := by
  induction path with
  | nil _ => rfl
  | cons _ _ retained => exact congrArg Nat.succ retained

/-- The actual final word is the exact previously exposed word followed by the retained new suffix. -/
theorem result_word {previous : Encoding.Prefix.Enclosure} {count : Nat} (path : Path previous count) :
    path.result.word = previous.word ++ path.bits := by
  induction path with
  | nil original => exact (List.Append.append_nil original.word).symm
  | @cons original _ step remaining retained =>
      change remaining.result.word = _
      calc
        remaining.result.word = step.next.word ++ remaining.bits := retained
        _ = (original.word ++ [step.choice.bit]) ++ remaining.bits :=
          congrArg (fun word => word ++ remaining.bits) step.wordEq
        _ = _ := List.Append.append_assoc _ _ _

/-- The actual final word extends the exact original exposed prefix. -/
theorem wordPrefix {previous : Encoding.Prefix.Enclosure} {count : Nat} (path : Path previous count) :
    previous.word.IsPrefix path.result.word := ⟨path.bits, path.result_word.symm⟩

/-- The actual exposed word length increases by exactly the additional-bit request. -/
theorem wordLength {previous : Encoding.Prefix.Enclosure} {count : Nat} (path : Path previous count) :
    path.result.word.length = previous.word.length + count := by
  rewrite [path.result_word, List.Append.length_append, path.bits_length]
  rfl

/-- The actual final enclosure refines the original retained box. -/
theorem refines {previous : Encoding.Prefix.Enclosure} {count : Nat} (path : Path previous count) :
    path.result.box.Refines previous.box := by
  induction path with
  | nil original => exact Rational.Box.refines_refl original.box
  | cons step _ retained =>
      exact retained.trans (Rational.Box.Refinement.StrictInterior.refines step.extension.nested)

/-- A nonzero additional-bit request returns a box strictly inside the original proper enclosure. -/
theorem nested {previous : Encoding.Prefix.Enclosure} {count : Nat} (path : Path previous count)
    (nonzero : count ≠ 0) : path.result.box.StrictInterior previous.box := by
  cases path with
  | nil _ => exact (nonzero rfl).elim
  | cons step remaining =>
      exact Rational.Box.Refinement.StrictInterior.of_refines step.extension.nested remaining.refines

/-- Every point of the final enclosure retains the exact original raw-prefix representation. -/
theorem earlierRepresented {previous : Encoding.Prefix.Enclosure} {count : Nat} (path : Path previous count)
    {point : Gaussian.Basic.Canonical} (inside : path.result.box.Contains point) :
    Encoding.Parser.Semantics.Prefix.Represented previous.word point :=
  previous.represented (path.refines.contains inside)

/-- A nonzero additional-bit request excludes the zero input throughout the actual final enclosure. -/
theorem point_nonzero {previous : Encoding.Prefix.Enclosure} {count : Nat} (path : Path previous count)
    (nonzero : count ≠ 0) {point : Gaussian.Basic.Canonical} (inside : path.result.box.Contains point) : point ≠ 0 := by
  cases path with
  | nil _ => exact (nonzero rfl).elim
  | cons step remaining => exact step.point_nonzero (remaining.refines.contains inside)

end Path

end Purelib.Geometry.CCL.Prefix
