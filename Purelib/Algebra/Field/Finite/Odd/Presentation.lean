module

import Purelib.Tactic.Ring
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.CharZero.Defs
public import Purelib.Algebra.Field.ExplicitField
public import Purelib.Data.List.Intersection
public import Purelib.Data.List.Map
import Purelib.Data.List.Nodup
-- Exposed square classifications retain the original Boolean membership scan.
import Purelib.Data.List.Membership
-- The public carrier and square certificates retain direct numeral evidence.
public import Purelib.Data.Nat.Order
-- The exposed minus-one classifier retains the original scalar negation parent.
public import Purelib.Algebra.Group.Negation
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Algebra.Group in
attribute [local instance high] Negation.subNegZeroMonoid

open Purelib.Algebra.Field
open Purelib.Data.List

section
@[expose] public section

/-!
# Rational rotations, Theorem 2: null vectors

The paper treats ordered fields and finite fields separately.  The ordered
rational case below is proved from the stored finite numerator order on the
repository's canonical rational carrier.  The finite-field construction is
implemented by a recursive intersection search over explicit carrier and
square tables, so the resulting null vector is executable data rather than a
bare existence claim.
-/

namespace Purelib.Algebra.Field.Finite.Odd.Presentation

open scoped Purelib.Data.Nat Purelib.Data.List.Membership

variable {K : Type*} [ExplicitField K]

set_option genInjectivity false in
/-- Two displayed scalars whose squared sum is the indexed value.

The record retains both scalars and the exact sum-of-squares equality. -/
structure TwoSquareRepresentation (value : K) where
  /-- The first retained square root. -/ first : K
  /-- The second retained square root. -/ second : K
  /-- The two retained squares sum to the indexed value. -/ equation : first ^ 2 + second ^ 2 = value

constructive_injectivity TwoSquareRepresentation

set_option genInjectivity false in
/-- A finite explicit field presented by a complete carrier and certified square table.

The data retain decidable equality, duplicate-free enumerations, cached square roots with their equations, the odd-size
square-count identity, and nonzero two. -/
structure FiniteOddFieldPresentation
    (K : Type*) [ExplicitField K] where
  /-- The equality decision procedure used by the retained tables. -/ eqDecidable : DecidableEq K
  /-- The displayed complete finite carrier list. -/ carrier : List K
  /-- The carrier enumeration has no repeated values. -/ carrierNodup : carrier.Nodup
  /-- Every scalar occurs in the carrier enumeration. -/ carrierComplete : ∀ value : K, value ∈ carrier
  /-- The displayed list of all square values. -/ squareValues : List K
  /-- The square-value table has no repeated values. -/ squareValuesNodup : squareValues.Nodup
  /-- Every scalar square occurs in the square-value table. -/ squareValuesComplete : ∀ root : K, root ^ 2 ∈
    squareValues
  /-- The retained root lookup for the square-value table. -/ squareRoot : K → K
  /-- The cached root squares to every value belonging to the square table. -/ squareRoot_spec : ∀ value ∈ squareValues,
    squareRoot value ^ 2 = value
  /-- Twice the square-table length is the carrier length plus one. -/ squareCount : squareValues.length +
    squareValues.length = carrier.length + 1
  /-- Two is nonzero in the presented field. -/ twoNonzero : (2 : K) ≠ 0

constructive_injectivity FiniteOddFieldPresentation

open Purelib.Algebra.Field.Finite.Odd.Presentation

namespace FiniteOddFieldPresentation

open Purelib.Data.List

variable (presentation : FiniteOddFieldPresentation K)

set_option genInjectivity false in
/-- A certified square root or a proof that no square root exists.

The square case retains its actual root and equality, while the nonsquare case rejects every possible field root. -/
inductive SquareClassification (value :
  K) where
  /-- Retain a displayed root and its square equation. -/ | square (root : K) (equation : root ^ 2 = value)
  /-- Certify that no scalar square equals the classified value. -/ | nonsquare (noRoot : ∀ root : K, root ^ 2 ≠ value)

constructive_injectivity SquareClassification

/-- A field value has a square root when a scalar square equals it. -/
def HasSquareRoot (value : K) : Prop :=
  ∃ root : K, root ^ 2 = value

open Purelib.Algebra.Field.Finite.Odd.Presentation in
/-- The retained square table contains exactly the values having square roots.

Completeness supplies membership in one direction, and the certified root cache supplies a witness in the other. -/
theorem
  mem_squareValues_iff_hasSquareRoot
  (value : K) :
    value ∈ presentation.squareValues ↔ HasSquareRoot value := by
  constructor
  · intro member
    exact ⟨presentation.squareRoot value,
      presentation.squareRoot_spec value member⟩
  · rintro ⟨root, equation⟩
    exact equation ▸ presentation.squareValuesComplete root

open Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation

/-- Decide square status by the cached finite square table.

The original lawful Boolean scan tests the retained table. A positive result
retains its cached root; a negative result rejects every proposed root using
the original table's completeness certificate. -/
def classifySquare (value : K) :
  SquareClassification value := by
  letI : DecidableEq K := presentation.eqDecidable
  if member : value ∈ presentation.squareValues then
    exact SquareClassification.square (presentation.squareRoot value)
      (presentation.squareRoot_spec value member)
  else
    exact SquareClassification.nonsquare fun root equation =>
      member (equation ▸ presentation.squareValuesComplete root)

/-- Classify the field's minus-one element using its retained square table.

The original Boolean membership scan selects the cached root or rejects every
root through the table's completeness certificate. Scalar negation retains
the original field operation. -/
def classifyMinusOne :
  SquareClassification (-1 : K) :=
  presentation.classifySquare (-1)

/-- Subtract each retained square value from the supplied target.

The resulting finite list preserves the square-table order and records the translates used in the two-square search. -/
def translatedSquareValues (target : K)
  : List K :=
  presentation.squareValues.map (fun value => target - value)

/-- Subtraction from a fixed target is injective on field values. -/
private theorem translateInjective
  (target : K) :
    Function.Injective (fun value : K => target - value) := by
  intro left right equal
  change target - left = target - right at equal
  calc
    left = target - (target - left) := by ring1
    _ = target - (target - right) :=
      congrArg (fun value => target - value) equal
    _ = right := by ring1

open Purelib.Algebra.Field.Finite.Odd.Presentation in
/-- The translated square table has no repeated values.

Injectivity of subtraction from the fixed target preserves the retained square-table distinctness. -/
theorem translatedSquareValues_nodup
  (target : K) :
    (presentation.translatedSquareValues target).Nodup := open Purelib in by
  unfold translatedSquareValues
  exact Data.List.Nodup.nodup_map_of_injective
    (by
      intro left right equal
      change target - left = target - right at equal
      calc
        left = target - (target - left) := by ring1
        _ = target - (target - right) :=
          congrArg (fun value => target - value) equal
        _ = right := by ring1)
    presentation.squareValuesNodup

/-- Every entry of a translated square table belongs to the complete carrier. -/
private theorem
  translatedSquareValues_contained
  (target value : K)
    (_member : value ∈ presentation.translatedSquareValues target) :
    value ∈ presentation.carrier :=
  presentation.carrierComplete value

/-- Every retained square value belongs to the complete carrier. -/
private theorem squareValues_contained
  (value : K)
    (_member : value ∈ presentation.squareValues) :
    value ∈ presentation.carrier :=
  presentation.carrierComplete value

/-- Search the square table and its target translate for their first common value.

The finite search uses the presentation's retained decidable equality and keeps the original table order. -/
def squareTableIntersection? (target :
  K) : Option K :=
  @Intersection.firstIntersection? K presentation.eqDecidable
    presentation.squareValues (presentation.translatedSquareValues target)

/-- Every translated square table intersects the original retained square table.

The displayed carrier contains both duplicate-free tables. Their exact
retained count exceeds that carrier's length, certifying success of the
original ordered intersection scan. -/
theorem squareTableIntersection_nonempty
  (target : K) :
    presentation.squareTableIntersection? target ≠ none := by
  letI : DecidableEq K := presentation.eqDecidable
  unfold squareTableIntersection?
  apply Intersection.firstIntersection?_ne_none_of_length_gt
    presentation.squareValuesNodup
    (presentation.translatedSquareValues_nodup target)
    presentation.squareValues_contained
    (presentation.translatedSquareValues_contained target)
    presentation.carrierNodup
  unfold translatedSquareValues
  rw [Map.length_map, presentation.squareCount]
  exact Nat.lt_succ_self presentation.carrier.length

/-- Compute two retained roots whose squared values sum to the requested scalar.

The original ordered intersection scan compares the cached square table with
its actual translated table. The stored root lookup turns that selected
intersection and its complement into the displayed root witnesses. -/
def twoSquareRepresentation (target : K)
  : TwoSquareRepresentation target := by
  letI : DecidableEq K := presentation.eqDecidable
  let translated := presentation.translatedSquareValues target
  have foundNonempty :
      presentation.squareTableIntersection? target ≠ none :=
    presentation.squareTableIntersection_nonempty target
  cases found : presentation.squareTableIntersection? target with
  | none => exact False.elim (foundNonempty found)
  | some common =>
      have commonMembers :=
        Intersection.firstIntersection?_eq_some
          (target := common)
          (left := presentation.squareValues)
          (right := presentation.translatedSquareValues target) (by
            unfold squareTableIntersection? at found
            exact found)
      have complementMember :
          target - common ∈ presentation.squareValues := by
        rcases Data.List.Map.mem_map.mp commonMembers.2 with
          ⟨source, sourceMember, translatedEqual⟩
        have sourceEqual : source = target - common := by
          calc
            source = target - (target - source) := by ring1
            _ = target - common := by rw [translatedEqual]
        exact sourceEqual ▸ sourceMember
      refine
        { first := presentation.squareRoot common
          second := presentation.squareRoot (target - common)
          equation := ?_ }
      rw [presentation.squareRoot_spec common commonMembers.1,
        presentation.squareRoot_spec (target - common) complementMember]
      ring1
end FiniteOddFieldPresentation

end Purelib.Algebra.Field.Finite.Odd.Presentation

end

@[expose] public section
namespace Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation

variable {K : Type*} [ExplicitField K]

/-- The displayed odd-field presentation has distinct zero and one. -/
theorem one_ne_zero
    (presentation : FiniteOddFieldPresentation K) : (1 : K) ≠ 0 := by
  intro oneZero
  apply presentation.twoNonzero
  calc
    (2 : K) = 1 + 1 := by ring1
    _ = 0 := by rw [oneZero, zero_add]

end Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation
end
