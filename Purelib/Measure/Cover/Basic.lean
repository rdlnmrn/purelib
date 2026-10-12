module
import Purelib.Data.List.Fold
import Purelib.Data.List.Map
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction

public import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic

@[expose] public section

/-!
# Generic finite cover certificates

A cover scheme specifies primitive finite cells, their nonnegative rational
cost, and their pointwise coverage relation.  A cover is only a displayed
cell list.  Effective nullity returns one such finite certificate for each
positive rational budget; it forms no collection of every cover and takes no
infimum.
-/

namespace Purelib.Measure

set_option genInjectivity false in
open Purelib.Data.Rat in
/-- Primitive cells with a coverage relation and nonnegative rational cost.

The scheme fixes what each individual cell covers and supplies its cost bound. It imposes no topology, countability or
closure conditions on the carrier or cells. -/
structure CoverScheme (α Cell : Type) where
  /-- The pointwise relation saying that a cell covers a point. -/ covers : Cell → α → Prop
  /-- The displayed rational cost of one cell. -/ weight : Cell → Fraction.Rational
  /-- Every cell has nonnegative cost. -/ weight_nonnegative : ∀ cell, 0 ≤ weight cell

constructive_injectivity CoverScheme

set_option genInjectivity false in
/-- A finite list of cells from one retained cover scheme.

The list need not cover any particular predicate. Coverage evidence is expressed separately by `Cover.Covers`. -/
structure Cover {α Cell : Type} (scheme : CoverScheme α Cell) where
  /-- The ordered finite list of cells, including any repetitions. -/ cells : List Cell

constructive_injectivity Cover

namespace Cover

open Purelib.Data.Rat in
/-- Sum the rational costs of all displayed cell occurrences. -/
def content {α Cell : Type} {scheme : CoverScheme α Cell}
    (cover : Cover scheme) : Fraction.Rational :=
  (cover.cells.map scheme.weight).sum

/-- The content of every finite cover list is nonnegative. -/
theorem content_nonneg {α Cell : Type} {scheme : CoverScheme α Cell}
    (cover : Cover scheme) : 0 ≤ cover.content := by
  rcases cover with ⟨cells⟩
  induction cells with
  | nil => exact le_rfl
  | cons cell remaining inductionHypothesis =>
      simp only [content, List.map_cons, List.sum_cons]
      exact add_nonneg (scheme.weight_nonnegative cell) inductionHypothesis

/-- Every point satisfying the predicate belongs to a cell in the displayed list.

The witness selects an actual list member and proves the scheme's coverage relation for that member. -/
def Covers {α Cell : Type} {scheme : CoverScheme α Cell}
    (cover : Cover scheme) (predicate : α → Prop) : Prop :=
  ∀ point, predicate point →
    ∃ cell, cell ∈ cover.cells ∧ scheme.covers cell point

/-- Concatenate the two cell lists from the same cover scheme. -/
def append {α Cell : Type} {scheme : CoverScheme α Cell}
    (left right : Cover scheme) : Cover scheme :=
  ⟨left.cells ++ right.cells⟩

open Purelib.Data.List in
/-- The cost of concatenated covers is the sum of their costs. -/
theorem content_append {α Cell : Type} {scheme : CoverScheme α Cell}
    (left right : Cover scheme) :
    (left.append right).content = left.content + right.content := by
  rw [content, append, Map.map_append]
  exact Fold.sum_append (fun value => zero_add value)
    (fun first second third => add_assoc first second third) _ _

/-- Concatenating two covers covers the disjunction of their predicates. -/
theorem append_covers_or {α Cell : Type} {scheme : CoverScheme α Cell}
    {left right : Cover scheme} {first second : α → Prop}
    (leftCovers : left.Covers first) (rightCovers : right.Covers second) :
    (left.append right).Covers (fun point => first point ∨ second point) := by
  intro point member
  rcases member with firstMember | secondMember
  · rcases leftCovers point firstMember with ⟨cell, cellMember, covered⟩
    exact ⟨cell, List.mem_append_left _ cellMember, covered⟩
  · rcases rightCovers point secondMember with ⟨cell, cellMember, covered⟩
    exact ⟨cell, List.mem_append_right _ cellMember, covered⟩

end Cover
namespace EffectiveNull
end EffectiveNull
namespace NullPredicate
end NullPredicate

end Purelib.Measure

end
