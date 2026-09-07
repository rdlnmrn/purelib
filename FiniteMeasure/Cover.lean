import mathlib.Tactic.QuotientFreeRing
import FiniteMeasure.Bounds

/-!
# Generic finite cover certificates

A cover scheme specifies primitive finite cells, their nonnegative rational
cost, and their pointwise coverage relation.  A cover is only a displayed
cell list.  Effective nullity returns one such finite certificate for each
positive rational budget; it forms no collection of every cover and takes no
infimum.
-/

namespace FiniteMeasure

/-- Primitive cells, rational costs, and pointwise coverage for one finite
cover calculus. -/
structure CoverScheme (α Cell : Type) where
  covers : Cell → α → Prop
  weight : Cell → Coordinate
  weight_nonnegative : ∀ cell, 0 ≤ weight cell

/-- One displayed finite cover in a supplied cover scheme. -/
structure FiniteCover {α Cell : Type} (scheme : CoverScheme α Cell) where
  cells : List Cell

namespace FiniteCover

/-- Exact rational cost of the displayed cell list. -/
def content {α Cell : Type} {scheme : CoverScheme α Cell}
    (cover : FiniteCover scheme) : Coordinate :=
  (cover.cells.map scheme.weight).sum

theorem content_nonneg {α Cell : Type} {scheme : CoverScheme α Cell}
    (cover : FiniteCover scheme) : 0 ≤ cover.content := by
  rcases cover with ⟨cells⟩
  induction cells with
  | nil => exact le_rfl
  | cons cell remaining inductionHypothesis =>
      simp only [content, List.map_cons, List.sum_cons]
      exact add_nonneg (scheme.weight_nonnegative cell) inductionHypothesis

/-- Pointwise coverage of one predicate by the displayed cells. -/
def Covers {α Cell : Type} {scheme : CoverScheme α Cell}
    (cover : FiniteCover scheme) (predicate : α → Prop) : Prop :=
  ∀ point, predicate point →
    ∃ cell, cell ∈ cover.cells ∧ scheme.covers cell point

/-- Concatenate two displayed finite covers. -/
def append {α Cell : Type} {scheme : CoverScheme α Cell}
    (left right : FiniteCover scheme) : FiniteCover scheme :=
  ⟨left.cells ++ right.cells⟩

theorem content_append {α Cell : Type} {scheme : CoverScheme α Cell}
    (left right : FiniteCover scheme) :
    (left.append right).content = left.content + right.content := by
  simp only [content, append, List.map_append, List.sum_append]

theorem append_covers_or {α Cell : Type} {scheme : CoverScheme α Cell}
    {left right : FiniteCover scheme} {first second : α → Prop}
    (leftCovers : left.Covers first) (rightCovers : right.Covers second) :
    (left.append right).Covers (fun point => first point ∨ second point) := by
  intro point member
  rcases member with firstMember | secondMember
  · rcases leftCovers point firstMember with ⟨cell, cellMember, covered⟩
    exact ⟨cell, List.mem_append_left _ cellMember, covered⟩
  · rcases rightCovers point secondMember with ⟨cell, cellMember, covered⟩
    exact ⟨cell, List.mem_append_right _ cellMember, covered⟩

end FiniteCover

/-- Every positive rational budget computes one finite cover certificate
strictly below that budget. -/
structure EffectiveNull {α Cell : Type} (scheme : CoverScheme α Cell)
    (predicate : α → Prop) where
  request : (epsilon : Coordinate) → 0 < epsilon → FiniteCover scheme
  covers : ∀ epsilon positive, (request epsilon positive).Covers predicate
  small : ∀ epsilon positive,
    (request epsilon positive).content < epsilon

namespace EffectiveNull

/-- The empty predicate needs no cells. -/
def empty {α Cell : Type} (scheme : CoverScheme α Cell) :
    EffectiveNull scheme (fun _ => False) where
  request _ _ := ⟨[]⟩
  covers epsilon positive := by
    intro point impossible
    exact impossible.elim
  small epsilon positive := by
    simpa only [FiniteCover.content, List.map_nil, List.sum_nil] using positive

/-- Restrict an effective cover protocol along an explicit implication. -/
def mono {α Cell : Type} {scheme : CoverScheme α Cell}
    {smaller larger : α → Prop}
    (large : EffectiveNull scheme larger)
    (subset : ∀ point, smaller point → larger point) :
    EffectiveNull scheme smaller where
  request := large.request
  covers epsilon positive := by
    intro point member
    exact large.covers epsilon positive point (subset point member)
  small := large.small

/-- Finite union of two effective cover protocols, with explicit half-budget
allocation. -/
def or {α Cell : Type} {scheme : CoverScheme α Cell}
    {first second : α → Prop}
    (left : EffectiveNull scheme first)
    (right : EffectiveNull scheme second) :
    EffectiveNull scheme (fun point => first point ∨ second point) where
  request epsilon positive :=
    let half := epsilon / 2
    let halfPositive := RFAP.ConstructiveFraction.div_pos_direct positive
      (by decide : (0 : Coordinate) < 2)
    (left.request half halfPositive).append
      (right.request half halfPositive)
  covers epsilon positive := by
    exact FiniteCover.append_covers_or
      (left.covers (epsilon / 2)
        (RFAP.ConstructiveFraction.div_pos_direct positive (by decide)))
      (right.covers (epsilon / 2)
        (RFAP.ConstructiveFraction.div_pos_direct positive (by decide)))
  small epsilon positive := by
    rw [FiniteCover.content_append]
    have halfPositive : (0 : Coordinate) < epsilon / 2 :=
      RFAP.ConstructiveFraction.div_pos_direct positive (by decide)
    have leftSmall := left.small (epsilon / 2) halfPositive
    have rightSmall := right.small (epsilon / 2) halfPositive
    calc
      (left.request (epsilon / 2) halfPositive).content +
          (right.request (epsilon / 2) halfPositive).content <
        epsilon / 2 + epsilon / 2 :=
        RFAP.ConstructiveFraction.add_lt_add_direct leftSmall rightSmall
      _ = epsilon := by
        calc
          epsilon / 2 + epsilon / 2 = (epsilon / 2) * 2 := by ring1
          _ = epsilon :=
            RFAP.ConstructiveFraction.div_mul_cancel_of_ne epsilon 2
              (by decide)

end EffectiveNull

/-- One predicate packaged with its generic finite-cover protocol. -/
structure NullPredicate {α Cell : Type} (scheme : CoverScheme α Cell) where
  predicate : α → Prop
  effective : EffectiveNull scheme predicate

namespace NullPredicate

/-- Pointwise union of a displayed finite predicate family. -/
def union {α Cell : Type} {scheme : CoverScheme α Cell} :
    List (NullPredicate scheme) → α → Prop
  | [], _ => False
  | member :: remaining, point =>
      member.predicate point ∨ union remaining point

/-- Every displayed finite family of effectively null predicates remains
effectively null. -/
def finiteUnion {α Cell : Type} {scheme : CoverScheme α Cell} :
    (family : List (NullPredicate scheme)) →
      EffectiveNull scheme (union family)
  | [] => EffectiveNull.empty scheme
  | member :: remaining =>
      member.effective.or (finiteUnion remaining)

end NullPredicate

end FiniteMeasure
