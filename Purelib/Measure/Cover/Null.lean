module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
public import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Data.Rat.Fraction.Order.Field

import Purelib.Data.Rat.Fraction.Field

public import Purelib.Measure.Cover.Basic
import Purelib.Tactic.Ring

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
namespace Cover
end Cover

set_option genInjectivity false in
open Purelib.Data.Rat in
/-- A finite cover protocol for every positive rational budget.

Each request returns actual cells covering the predicate, together with a strict bound on their total cost. The protocol
does not require a single cover to work at every budget. -/
structure EffectiveNull {α Cell : Type} (scheme : CoverScheme α Cell)
    (predicate : α → Prop) where
  /-- Compute a finite cover at the requested positive rational budget. -/ request : (epsilon : Fraction.Rational) → 0 <
    epsilon → Cover scheme
  /-- Each requested cell list covers every point satisfying the predicate. -/ covers : ∀ epsilon positive, (request
    epsilon positive).Covers predicate
  /-- The content of the requested cell list is strictly below its budget. -/ small : ∀ epsilon positive,
    (request epsilon positive).content < epsilon

constructive_injectivity EffectiveNull

namespace EffectiveNull

/-- Cover the empty predicate with the empty cell list at every positive budget. -/
def empty {α Cell : Type} (scheme : CoverScheme α Cell) :
    EffectiveNull scheme (fun _ => False) where
  request _ _ := ⟨[]⟩
  covers epsilon positive := by
    intro point impossible
    exact impossible.elim
  small epsilon positive := by
    simpa only [Cover.content, List.map_nil, List.sum_nil] using positive

/-- Restrict a finite cover protocol along a pointwise implication.

The smaller predicate uses exactly the original requested covers and cost bounds. The implication transports only their
coverage evidence. -/
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

open Purelib.Data.Rat in
/-- Combine two nullity protocols by splitting each budget in half.

Both protocols receive the same positive half-budget, and their returned cell lists are concatenated. The resulting
cover covers the disjunction and has total content strictly below the original budget. -/
def or {α Cell : Type} {scheme : CoverScheme α Cell}
    {first second : α → Prop}
    (left : EffectiveNull scheme first)
    (right : EffectiveNull scheme second) :
    EffectiveNull scheme (fun point => first point ∨ second point) where
  request epsilon positive :=
    let half := epsilon / 2
    let halfPositive := Fraction.Order.Field.div_pos_direct positive
      (by decide : (0 : Fraction.Rational) < 2)
    (left.request half halfPositive).append
      (right.request half halfPositive)
  covers epsilon positive := by
    exact Cover.append_covers_or
      (left.covers (epsilon / 2)
        (Fraction.Order.Field.div_pos_direct positive (by decide)))
      (right.covers (epsilon / 2)
        (Fraction.Order.Field.div_pos_direct positive (by decide)))
  small epsilon positive := by
    rw [Cover.content_append]
    have halfPositive : (0 : Fraction.Rational) < epsilon / 2 :=
      Fraction.Order.Field.div_pos_direct positive (by decide)
    have leftSmall := left.small (epsilon / 2) halfPositive
    have rightSmall := right.small (epsilon / 2) halfPositive
    calc
      (left.request (epsilon / 2) halfPositive).content +
          (right.request (epsilon / 2) halfPositive).content <
        epsilon / 2 + epsilon / 2 :=
        Fraction.Order.Arithmetic.add_lt_add_direct leftSmall rightSmall
      _ = epsilon := by
        calc
          epsilon / 2 + epsilon / 2 = (epsilon / 2) * 2 := by ring1
          _ = epsilon :=
            Fraction.Field.div_mul_cancel_of_ne epsilon 2
              (by decide)

end EffectiveNull

set_option genInjectivity false in
/-- A predicate paired with its finite cover protocol.

The retained protocol covers this exact predicate below every positive rational budget, using the fixed cell scheme. -/
structure NullPredicate {α Cell : Type} (scheme : CoverScheme α Cell) where
  /-- The predicate equipped with effective nullity evidence. -/ predicate : α → Prop
  /-- The finite cover protocol for the retained predicate. -/ effective : EffectiveNull scheme predicate

constructive_injectivity NullPredicate

namespace NullPredicate

/-- Take the pointwise disjunction of a finite list of retained predicates.

The empty list denotes the false predicate. Each list occurrence contributes its predicate in the displayed order. -/
def union {α Cell : Type} {scheme : CoverScheme α Cell} :
    List (NullPredicate scheme) → α → Prop
  | [], _ => False
  | member :: remaining, point =>
      member.predicate point ∨ union remaining point

/-- Build a nullity protocol for a finite union of retained null predicates.

The recursion combines the head protocol with the protocol for the remaining list by halving the available budget. The
empty list uses the empty cover. -/
def effectiveUnion {α Cell : Type} {scheme : CoverScheme α Cell} :
    (family : List (NullPredicate scheme)) →
      EffectiveNull scheme (union family)
  | [] => EffectiveNull.empty scheme
  | member :: remaining =>
      member.effective.or (effectiveUnion remaining)

end NullPredicate

end Purelib.Measure

end
