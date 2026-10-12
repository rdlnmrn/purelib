module
import Purelib.Data.List.Fold
import Purelib.Data.List.Map
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Basic
import Purelib.Geometry.Rational.Box.Basic
public import Purelib.Geometry.Rational.Box.Content
public import Purelib.Measure.Cover.Basic
import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Content.Basic
import Purelib.Measure.Classified.Basic
import Purelib.Measure.Filtration.Basic
import Purelib.Measure.Distribution.Partition.Basic
import Purelib.Measure.Distribution.Partition.Positive
import Purelib.Measure.EventAlgebra.Simple.Basic
import Purelib.Measure.Event.Chain
import Purelib.Approximation.OneSided.Basic
import Purelib.Measure.Classified.FixedLawProcess
import Purelib.Approximation.OneSided.Located
import Purelib.Measure.EventAlgebra.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic

@[expose] public section

/-!
# Finite rational content of RFAP boxes

Axis-aligned rational boxes have an exact executable area.  Finite covers and
effective nullity are request protocols returning only displayed box lists;
no outer-measure infimum or collection of all covers is formed.
-/

namespace Purelib.Measure.Box.Cover

open Purelib in
open Purelib.Data.Gaussian in
open Purelib.Geometry.Rational in
/-- Use exact rational-box containment and rectangular content as a finite cover scheme for Gaussian rational points. -/
def boxCoverScheme : Measure.CoverScheme Basic.Canonical Box where
  covers box point := box.Contains point
  weight := Box.Content.boxContent
  weight_nonnegative := Box.Content.boxContent_nonneg

set_option genInjectivity false in
open Purelib.Geometry.Rational in
/-- Retain an ordered finite list of rational boxes.

Coverage is certified separately for a supplied predicate, and content counts every retained box occurrence without
merging overlaps. -/
structure BoxCover where
  /-- The exact ordered finite box list, retaining every occurrence. -/ boxes : List Box

constructive_injectivity BoxCover

namespace BoxCover

open Purelib.Data.Rat in
open Purelib.Geometry.Rational in
open Purelib.Measure in
/-- Sum the rectangular contents of every box in the exact retained list. -/
def content (cover : Box.Cover.BoxCover) :
  Fraction.Rational :=
  (cover.boxes.map Box.Content.boxContent).sum

open Purelib.Geometry.Rational in
open Purelib.Measure in
/-- The content of every exact finite box cover is nonnegative. -/
theorem content_nonneg (cover : Box.Cover.BoxCover) :
  0 ≤ cover.content := by
  rcases cover with ⟨boxes⟩
  induction boxes with
  | nil => exact le_rfl
  | cons box remaining inductionHypothesis =>
      change 0 ≤ Box.Content.boxContent box + (remaining.map Box.Content.boxContent).sum
      exact add_nonneg (Box.Content.boxContent_nonneg box) inductionHypothesis

open Purelib in
open Purelib.Measure in
/-- Read the same exact box list as a cover for the rational-box cover scheme. -/
def toCover (cover : Box.Cover.BoxCover) :
    Measure.Cover Box.Cover.boxCoverScheme :=
  ⟨cover.boxes⟩

section
open Purelib.Measure
/-- The generic-cover readback preserves the exact original box-cover content. -/
theorem toCover_content (cover : Box.Cover.BoxCover) :
    cover.toCover.content = cover.content := rfl

/-- Append the two original ordered box lists into one cover. -/
def append (left right : Box.Cover.BoxCover) :
  Box.Cover.BoxCover :=
  ⟨left.boxes ++ right.boxes⟩

end

open Purelib.Measure in
open Purelib.Data.List in
/-- Appending exact box covers adds their original contents. -/
theorem content_append (left right :
  Box.Cover.BoxCover) :
    (left.append right).content = left.content + right.content := by
  rw [Box.Cover.BoxCover.content, Box.Cover.BoxCover.append, Map.map_append]
  exact Fold.sum_append (fun value => zero_add value)
    (fun first second third => add_assoc first second third) _ _

open Purelib.Data.Gaussian
open Purelib.Measure
/-- Require each point satisfying the predicate to belong to some box in the exact retained list. -/
def Covers (cover : Box.Cover.BoxCover) (predicate :
  Basic.Canonical → Prop) : Prop :=
  ∀ point, predicate point →
    ∃ box, box ∈ cover.boxes ∧ box.Contains point

/-- Appending two certified box covers covers the disjunction of their exact predicates. -/
theorem append_covers_or {left right :
  Box.Cover.BoxCover}
    {first second : Basic.Canonical → Prop}
    (leftCovers : left.Covers first) (rightCovers : right.Covers second) :
    (left.append right).Covers (fun point => first point ∨ second point) := by
  intro point member
  rcases member with firstMember | secondMember
  · rcases leftCovers point firstMember with ⟨box, boxMember, inside⟩
    exact ⟨box, List.mem_append_left _ boxMember, inside⟩
  · rcases rightCovers point secondMember with ⟨box, boxMember, inside⟩
    exact ⟨box, List.mem_append_right _ boxMember, inside⟩

/-- Transfer coverage of the original predicate to the generic cover on the same exact box list. -/
theorem toCover_covers {cover : Box.Cover.BoxCover}
    {predicate : Basic.Canonical → Prop} (covers : cover.Covers predicate) :
    cover.toCover.Covers predicate :=
  covers

end BoxCover
end Purelib.Measure.Box.Cover

end
