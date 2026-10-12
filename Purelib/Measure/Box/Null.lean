module
import Purelib.Data.List.Membership
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Box.Content
import Purelib.Geometry.Rational.Box.Point
public import Purelib.Measure.Box.Cover
public import Purelib.Measure.Cover.Null
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Measure.Cover.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Tactic.Ring

open Purelib.Measure.Box.Cover (BoxCover)

@[expose] public section

/-!
# Finite rational content of RFAP boxes

Axis-aligned rational boxes have an exact executable area.  Finite covers and
effective nullity are request protocols returning only displayed box lists;
no outer-measure infimum or collection of all covers is formed.
-/

namespace Purelib.Measure.Box.Null

set_option genInjectivity false in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Measure in
/-- Provide a finite rational-box cover of the exact predicate below every positive content tolerance.

The executable request and both coverage and strict-content certificates refer to the same retained requested box list.
-/
structure EffectiveNull (predicate : Basic.Canonical → Prop) where
  /-- The exact finite box cover computed for a supplied positive rational tolerance. -/ request : (epsilon :
    Fraction.Rational) → 0 < epsilon → BoxCover
  /-- Every requested original cover contains every point of the exact predicate. -/ covers : ∀ epsilon positive,
    (request epsilon positive).Covers predicate
  /-- Each requested exact cover has content strictly below its supplied tolerance. -/ small : ∀ epsilon positive,
    (request epsilon positive).content < epsilon

constructive_injectivity EffectiveNull

namespace EffectiveNull

open Purelib in
open Purelib.Data.Gaussian in
open Purelib.Measure in
/-- Read the exact box-cover requests as an effective-null certificate for the generic rational-box scheme. -/
def toGeneric {predicate : Basic.Canonical → Prop}
    (null : Box.Null.EffectiveNull predicate) :
    Measure.EffectiveNull Box.Cover.boxCoverScheme predicate where
  request epsilon positive :=
    (null.request epsilon positive).toCover
  covers epsilon positive :=
    BoxCover.toCover_covers (null.covers epsilon positive)
  small epsilon positive := by
    rw [BoxCover.toCover_content]
    exact null.small epsilon positive

open Purelib.Measure in
/-- Certify the empty predicate as effectively null using the empty box list at every request. -/
def empty : Box.Null.EffectiveNull (fun _ =>
  False) where
  request _ _ := ⟨[]⟩
  covers epsilon positive := by
    intro point impossible
    exact impossible.elim
  small epsilon positive := by
    simpa only [BoxCover.content, List.map_nil, List.sum_nil] using positive

open Purelib.Data.Gaussian in
open Purelib.Measure in
/-- Reuse an effective-null request family for a predicate contained in its original predicate. -/
def mono {smaller larger : Basic.Canonical → Prop}
    (large : Box.Null.EffectiveNull larger)
    (subset : ∀ point, smaller point → larger point) :
    Box.Null.EffectiveNull smaller where
  request := large.request
  covers epsilon positive := by
    intro point member
    exact large.covers epsilon positive point (subset point member)
  small := large.small

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Measure in
/-- Cover the disjunction of two effectively null predicates by appending their exact half-tolerance covers. -/
def or {first second : Basic.Canonical → Prop}
    (left : Box.Null.EffectiveNull first) (right : Box.Null.EffectiveNull second) :
    Box.Null.EffectiveNull (fun point => first point ∨ second point) where
  request epsilon positive :=
    let half := epsilon / 2
    let halfPositive := Fraction.Order.Field.div_pos_direct positive
      (by decide : (0 : Fraction.Rational) < 2)
    (left.request half halfPositive).append
      (right.request half halfPositive)
  covers epsilon positive := by
    exact BoxCover.append_covers_or
      (left.covers (epsilon / 2)
        (Fraction.Order.Field.div_pos_direct positive (by decide)))
      (right.covers (epsilon / 2)
        (Fraction.Order.Field.div_pos_direct positive (by decide)))
  small epsilon positive := by
    rw [BoxCover.content_append]
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

/-! ## Displayed finite null families -/

set_option genInjectivity false in
open Purelib.Data.Gaussian in
open Purelib.Measure in
/-- Retain a Gaussian-rational predicate with an effective-null box-cover procedure for that same predicate. -/
structure NullPredicate where
  /-- The exact Gaussian-rational predicate retained with its certificate. -/ predicate : Basic.Canonical → Prop
  /-- The effective-null procedure covering that same retained predicate. -/ effective :
    EffectiveNull predicate

constructive_injectivity NullPredicate

namespace NullPredicate

open Purelib.Data.Gaussian in
open Purelib.Measure in
/-- Form the finite disjunction of the exact predicates in the retained list. -/
def union : List Box.Null.NullPredicate →
  Basic.Canonical → Prop
  | [], _ => False
  | member :: remaining, point =>
      member.predicate point ∨ union remaining point

open Purelib.Measure in
/-- Construct effective-null covers for the exact finite predicate union by recursive half-tolerance allocation. -/
def effectiveUnion : (family : List
  Box.Null.NullPredicate) → Box.Null.EffectiveNull (Box.Null.NullPredicate.union
  family)
  | [] => Box.Null.EffectiveNull.empty
  | member :: remaining =>
      member.effective.or (effectiveUnion remaining)

end NullPredicate

open Purelib.Data.Gaussian in
open Purelib.Geometry.Rational in
open Purelib.Measure in
/-- Cover one exact Gaussian rational point by its degenerate zero-content point box at every tolerance. -/
def singletonNull (point : Basic.Canonical) :
    EffectiveNull (fun candidate => candidate = point) where
  request _ _ := ⟨[Box.Point.pointBox point]⟩
  covers epsilon positive := by
    intro candidate equal
    subst candidate
    exact ⟨Box.Point.pointBox point, List.mem_cons_self, Box.Point.pointBox_contains point⟩
  small epsilon positive := by
    simpa only [BoxCover.content, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, Box.Content.pointBox_content, add_zero] using positive

open Purelib.Data.Gaussian
open Purelib.Measure
/-- Construct effective-null covers for membership in the exact finite point list. -/
def pointsNull : (points : List Basic.Canonical) →
    EffectiveNull (fun candidate => candidate ∈ points)
  | [] => EffectiveNull.mono EffectiveNull.empty
      (fun _ member => (List.not_mem_nil member).elim)
  | point :: remaining =>
      EffectiveNull.mono
        ((singletonNull point).or (pointsNull remaining))
        (by
          intro candidate member
          exact Purelib.Data.List.Membership.mem_cons.mp member)

/-- Require effective-null covers of the exact set where the supplied predicate fails. -/
def HoldsExceptNull (predicate : Basic.Canonical → Prop) : Type :=
  EffectiveNull (fun point => ¬predicate point)

/-- Require effective-null covers of the exact pointwise disagreement set of the supplied functions. -/
def EqualExceptNull {β : Type} (left right : Basic.Canonical → β) : Type :=
  EffectiveNull (fun point => left point ≠ right point)

/-- A function equals itself except on an effectively null empty disagreement set. -/
def equalExceptNull_refl {β : Type} (value : Basic.Canonical → β) :
    EqualExceptNull value value :=
  EffectiveNull.mono EffectiveNull.empty
    (fun _ notEqual => (notEqual rfl).elim)

/-- Reverse an equality-except-null certificate using the same original disagreement covers. -/
def equalExceptNull_symm {β : Type} {left right : Basic.Canonical → β}
    (equal : EqualExceptNull left right) : EqualExceptNull right left :=
  EffectiveNull.mono equal (fun _ notEqual equalReverse =>
    notEqual equalReverse.symm)

/-- Compose equality-except-null certificates using decidable equality in the codomain and covers of the two original
disagreement sets. -/
def equalExceptNull_trans {β : Type} [DecidableEq β]
    {first second third : Basic.Canonical → β}
    (firstSecond : EqualExceptNull first second)
    (secondThird : EqualExceptNull second third) :
    EqualExceptNull first third := by
  apply EffectiveNull.mono (firstSecond.or secondThird)
  intro point firstThird
  by_cases firstSecondEqual : first point = second point
  · exact Or.inr (fun secondThirdEqual =>
      firstThird (firstSecondEqual.trans secondThirdEqual))
  · exact Or.inl firstSecondEqual

end Purelib.Measure.Box.Null

end
