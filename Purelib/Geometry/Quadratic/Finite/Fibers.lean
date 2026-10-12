module

public import Purelib.Algebra.Field.Finite.Odd.SquareFibers
import Purelib.Algebra.Field.Finite.Odd.Presentation
import Purelib.Algebra.Quadratic.Pair.Basic
public import Purelib.Algebra.Quadratic.Pair.Coordinates
import Purelib.Data.List.Bijection
import Purelib.Data.List.Flatten
import Purelib.Data.List.Append
import Purelib.Data.List.Membership
import Purelib.Data.List.Filter
import Purelib.Data.List.Map
import Purelib.Data.List.Nodup
import Purelib.Data.Nat.Order
import Purelib.Data.Nat.Subtraction
import Purelib.Algebra.Group.Negation
import Init.Core
import Init.Data.List.Lemmas
import Init.Prelude
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Purelib.Algebra.Field.ExplicitField
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Algebra.Field (ExplicitField)

open scoped Purelib.Data.Nat

-- Retain the field's subtraction parent and its original negation operation.
open Purelib.Algebra.Group in
attribute [local instance high] Negation.subNegZeroMonoid

open Purelib

open Purelib.Algebra.Field.Finite.Odd

open Purelib.Algebra.Field.Finite.Odd.Presentation

open Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation

open Purelib.Algebra.Quadratic

open Purelib.Algebra.Quadratic.Pair

open Purelib.Data.List

open Purelib.Data.List.Bijection

open Purelib.Data.Nat

section
@[expose] public section
namespace Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation
variable {K : Type*} [ExplicitField K]
section
variable (presentation : Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation K)

/-- The carrier size minus one is the number of nonroots of zero. -/
private theorem carrier_predecessor
  (presentation : Presentation.FiniteOddFieldPresentation K) :
    presentation.carrier.length - 1 =
      presentation.squareNonrootCount 0 := by
  have partition := presentation.squareRootCount_add_squareNonrootCount 0
  rw [presentation.squareRootCount_zero] at partition
  calc
    presentation.carrier.length - 1 =
        (1 + presentation.squareNonrootCount 0) - 1 := by rw [partition]
    _ = presentation.squareNonrootCount 0 := by
      rw [Subtraction.add_sub_cancel_left]
end
end Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation

end

section
@[expose] public section
namespace Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation
variable {K : Type*} [ExplicitField K]
section
variable (presentation : Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation K)

/-- The `q` affine parameters followed by the exceptional parameter at infinity. `Option` keeps the two pieces disjoint
without a quotient. -/
def circleParameters : List (Option K)
  :=
  presentation.carrier.map some ++ [none]
end
end Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation

end

section
@[expose] public section
namespace Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation
variable {K : Type*} [ExplicitField K]
section
variable (presentation : Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation K)

/-- The affine circle parameters together with infinity have `q + 1` entries. -/
theorem circleParameters_length :
    presentation.circleParameters.length = presentation.carrier.length + 1 := by
  unfold circleParameters
  rw [Append.length_append, Map.length_map]
  rfl
end
end Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation

end

section
@[expose] public section
namespace Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation
variable {K : Type*} [ExplicitField K]
section
variable (presentation : Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation K)

/-- The displayed circle parameters have no duplicates. -/
theorem circleParameters_nodup :
  presentation.circleParameters.Nodup := by
  unfold circleParameters
  apply Nodup.nodup_append
  · apply Data.List.Nodup.nodup_map_of_injective
    · intro left right equal
      injection equal
    · exact presentation.carrierNodup
  · exact Nodup.nodup_singleton none
  · intro left leftMember right rightMember equal
    rcases Map.mem_map.mp leftMember with
      ⟨parameter, _, parameterEqual⟩
    rcases Membership.mem_cons.mp rightMember with rightEqual | impossible
    · have contradiction : some parameter = none :=
        parameterEqual.trans (equal.trans rightEqual)
      nomatch contradiction
    · nomatch impossible
end
end Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation

end

section
@[expose] public section
namespace Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation
variable {K : Type*} [ExplicitField K]
section
variable (presentation : Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation K)

/-- Filtering an explicitly nonzero list removes no entries. -/
private theorem filter_nonzero_eq_self
  (eqDecidable : DecidableEq K) :
    ∀ {values : List K}, (∀ value ∈ values, value ≠ 0) →
      (letI : DecidableEq K := eqDecidable
       values.filter fun value => value ≠ 0) = values
  | [], _ => rfl
  | head :: tail, allNonzero => by
      letI : DecidableEq K := eqDecidable
      rw [Filter.filter_cons_of_pos
        (predicate := fun value : K => decide (value ≠ 0))
        (decide_eq_true (allNonzero head List.mem_cons_self))]
      rw [filter_nonzero_eq_self eqDecidable
        (fun value member =>
        allNonzero value (List.mem_cons_of_mem head member))]
end
end Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation

end

section
@[expose] public section
namespace Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation
variable {K : Type*} [ExplicitField K]
section
variable (presentation : Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation K)

/-- Removing zero from a duplicate-free list containing zero decreases its length by one. -/
private theorem
  filter_nonzero_length_add_one
  (eqDecidable : DecidableEq K) :
    ∀ {values : List K}, values.Nodup → 0 ∈ values →
      (letI : DecidableEq K := eqDecidable
       (values.filter fun value => value ≠ 0).length + 1) = values.length
  | [], _, impossible => nomatch impossible
  | head :: tail, nodup, zeroMember => by
      letI : DecidableEq K := eqDecidable
      cases eqDecidable head 0 with
      | isTrue headZero =>
          have tailNonzero : ∀ value ∈ tail, value ≠ 0 := by
            intro value member valueZero
            apply (List.pairwise_cons.mp nodup).1 value member
            exact headZero.trans valueZero.symm
          rw [Filter.filter_cons_of_neg
            (predicate := fun value : K => decide (value ≠ 0))
            (fun accepted => (of_decide_eq_true accepted) headZero)]
          rw [filter_nonzero_eq_self eqDecidable
            tailNonzero]
          rfl
      | isFalse headNonzero =>
          have tailMember : 0 ∈ tail := by
            rcases Membership.mem_cons.mp zeroMember with headMember | member
            · exact False.elim (headNonzero headMember.symm)
            · exact member
          rw [Filter.filter_cons_of_pos
            (predicate := fun value : K => decide (value ≠ 0))
            (decide_eq_true headNonzero)]
          have induction :=
            filter_nonzero_length_add_one
            eqDecidable
            (List.pairwise_cons.mp nodup).2 tailMember
          exact congrArg Nat.succ induction
end
end Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation

end

section
@[expose] public section
namespace Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation
variable {K : Type*} [ExplicitField K]
section
variable (presentation : Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation K)

/-- The first coordinate of a pair with nonzero coordinate product is nonzero. -/
private theorem
  first_ne_zero_of_product_eq {value :
  K}
    (valueNonzero : value ≠ 0) (pair : Algebra.Quadratic.Pair K (1 : K))
    (product : pair.re * pair.im = value) : pair.re ≠ 0 := by
  intro firstZero
  apply valueNonzero
  calc
    value = pair.re * pair.im := product.symm
    _ = 0 := by rw [firstZero, zero_mul]
end
end Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation

end

section
@[expose] public section
namespace Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation
variable {K : Type*} [ExplicitField K]
section
variable (presentation : Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation K)

/-- Interchange the first two summands in a right-associated natural sum. -/
private theorem nat_add_swap_first
  (first second third : Nat) :
    first + (second + third) = second + (first + third) := by
  calc
    first + (second + third) = (first + second) + third :=
      (Nat.add_assoc first second third).symm
    _ = (second + first) + third :=
      congrArg (fun value => value + third) (Nat.add_comm first second)
    _ = second + (first + third) := Nat.add_assoc second first third
end
end Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation

end

section
@[expose] public section
namespace Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation
variable {K : Type*} [ExplicitField K]
section
variable (presentation : Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation K)

/-- Move the first summand to the end of a right-associated natural sum. -/
private theorem nat_add_rotate_first
  (first second third : Nat) :
    first + (second + third) = second + (third + first) := by
  calc
    first + (second + third) = second + (first + third) :=
      nat_add_swap_first first second third
    _ = second + (third + first) :=
      congrArg (fun value => second + value) (Nat.add_comm first third)
end
end Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation

end

section
@[expose] public section
namespace Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation
variable {K : Type*} [ExplicitField K]
section
variable (presentation : Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation K)

/-- Interchange the first two summands and reassociate to the left. -/
private theorem nat_add_swap_first_flat
  (first second third : Nat) :
    first + (second + third) = (second + first) + third := by
  calc
    first + (second + third) = (first + second) + third :=
      (Nat.add_assoc first second third).symm
    _ = (second + first) + third :=
      congrArg (fun value => value + third) (Nat.add_comm first second)
end
end Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation

end

section
@[expose] public section
namespace Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation
variable {K : Type*} [ExplicitField K]
section
variable (presentation : Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation K)

/-- An additive natural-number equation gives the corresponding truncated-subtraction equation. -/
private theorem nat_eq_sub_of_add_eq
  {left subtracted total : Nat}
    (equal : left + subtracted = total) : left = total - subtracted := by
  calc
    left = (left + subtracted) - subtracted :=
      (Subtraction.add_sub_cancel_right left subtracted).symm
    _ = total - subtracted :=
      congrArg (fun value => value - subtracted) equal
end
end Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation

end

section
@[expose] public section
namespace Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation
variable {K : Type*} [ExplicitField K]
section
variable (presentation : Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation K)

/-- The displayed nonzero field carrier, computed by a direct finite filter. -/
def nonzeroScalars : List K := by
  letI : DecidableEq K := presentation.eqDecidable
  exact presentation.carrier.filter fun value => value ≠ 0
end
end Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation

end

section
@[expose] public section
namespace Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation
variable {K : Type*} [ExplicitField K]
section
variable (presentation : Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation K)

/-- A retained nonzero scalar has its original carrier occurrence and nonvanishing.

The Boolean filter retains exactly the nonzero occurrences of the displayed
carrier. The certificate preserves the presentation's original equality decision. -/
theorem mem_nonzeroScalars_iff (value :
  K) :
    value ∈ presentation.nonzeroScalars ↔
      value ≠ 0 ∧ value ∈ presentation.carrier := by
  letI : DecidableEq K := presentation.eqDecidable
  unfold nonzeroScalars
  constructor
  · intro member
    have retained := Filter.mem_filter.mp member
    exact ⟨of_decide_eq_true retained.2, retained.1⟩
  · rintro ⟨nonzero, member⟩
    exact Filter.mem_filter.mpr ⟨member, decide_eq_true nonzero⟩
end
end Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation

end

section
@[expose] public section
namespace Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation
variable {K : Type*} [ExplicitField K]
section
variable (presentation : Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation K)

/-- The nonzero scalar carrier has `q - 1` entries. -/
theorem nonzeroScalars_length :
    presentation.nonzeroScalars.length = presentation.carrier.length - 1 := by
  letI : DecidableEq K := presentation.eqDecidable
  unfold nonzeroScalars
  have count := filter_nonzero_length_add_one
    presentation.eqDecidable
    presentation.carrierNodup (presentation.carrierComplete 0)
  calc
    (presentation.carrier.filter fun value => value ≠ 0).length =
        ((presentation.carrier.filter fun value => value ≠ 0).length + 1) - 1 := by
      rw [Subtraction.add_sub_cancel_right]
    _ = presentation.carrier.length - 1 := congrArg (fun length => length - 1) count
end
end Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation

end

section
@[expose] public section
namespace Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation
variable {K : Type*} [ExplicitField K]
section
variable (presentation : Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation K)

/-- The filtered nonzero scalar carrier has no duplicates. -/
theorem nonzeroScalars_nodup :
  presentation.nonzeroScalars.Nodup := by
  letI : DecidableEq K := presentation.eqDecidable
  unfold nonzeroScalars
  exact Filter.pairwise_filter _ presentation.carrierNodup
end
end Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation

end

section
@[expose] public section
namespace Purelib.Rotations
variable {K : Type*} [ExplicitField K]
namespace FiniteOddFieldPresentation
variable (presentation : Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation K)

end FiniteOddFieldPresentation
end Purelib.Rotations

end

section
@[expose] public section
namespace Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation
variable {K : Type*} [ExplicitField K]
section
variable (presentation : Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation K)

/-- The pair computed by the cached two-square search. -/
def representedPair (value : K) :
  Algebra.Quadratic.Pair K (1 : K) :=
  let representation := presentation.twoSquareRepresentation value
  ⟨representation.first, representation.second⟩
end
end Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation

end

section
@[expose] public section
namespace Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation
variable {K : Type*} [ExplicitField K]
section
variable (presentation : Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation K)

/-- The pair computed by the two-square search has the requested quadrance. -/
theorem representedPair_quadrance (value
  : K) :
    (presentation.representedPair value).quadrance = value := by
  unfold representedPair Pair.quadrance
  exact (presentation.twoSquareRepresentation value).equation
end
end Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation

end

section
@[expose] public section
namespace Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation
variable {K : Type*} [ExplicitField K]
section
variable (presentation : Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation K)

/-- A square root of minus one in the displayed odd field is nonzero. -/
theorem root_ne_zero (presentation :
  Presentation.FiniteOddFieldPresentation K)
    {root : K} (rootSquare : root ^ 2 = -1) :
    root ≠ 0 := by
  intro rootZero
  apply Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation.one_ne_zero presentation
  have minusOneZero : (-1 : K) = 0 := by
    calc
      (-1 : K) = root ^ 2 := rootSquare.symm
      _ = 0 := by rw [rootZero]; ring1
  calc
    (1 : K) = -(-1) := by ring1
    _ = 0 := by rw [minusOneZero]; ring1
end
end Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation

end

section
@[expose] public section
namespace Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation
variable {K : Type*} [ExplicitField K]
section
variable (presentation : Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation K)

/-- The complete displayed affine pair carrier. -/
def scalarPairs : List
  (Algebra.Quadratic.Pair
  K (1 : K)) :=
  presentation.carrier.flatMap fun first =>
    presentation.carrier.map fun second => ⟨first, second⟩
end
end Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation

end

section
@[expose] public section
namespace Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation
variable {K : Type*} [ExplicitField K]
section
variable (presentation : Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation K)

/-- The factorized hyperbola fiber `uv = value`. -/
def productFiber (value : K) : List
  (Algebra.Quadratic.Pair K (1 : K)) := by
  letI : DecidableEq K := presentation.eqDecidable
  exact presentation.scalarPairs.filter fun pair =>
    pair.re * pair.im = value
end
end Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation

end

section
@[expose] public section
namespace Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation
variable {K : Type*} [ExplicitField K]
section
variable (presentation : Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation K)

/-- Every displayed pair occurs in the explicit pair carrier. -/
theorem scalarPairs_complete (pair :
  Algebra.Quadratic.Pair K (1 : K)) :
    pair ∈ presentation.scalarPairs := by
  unfold scalarPairs
  apply Flatten.mem_flatMap.mpr
  refine ⟨pair.re, presentation.carrierComplete pair.re, ?_⟩
  exact Map.mem_map.mpr
    ⟨pair.im, presentation.carrierComplete pair.im, rfl⟩
end
end Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation

end

section
@[expose] public section
namespace Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation
variable {K : Type*} [ExplicitField K]
section
variable (presentation : Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation K)

/-- A product-fiber occurrence has the requested coordinate product.

The Boolean filter retains exactly those pairs satisfying the product equation.
The complete displayed pair carrier supplies the source occurrence in reverse. -/
theorem mem_productFiber_iff (value : K)
  (pair : Algebra.Quadratic.Pair K (1 : K)) :
    pair ∈ presentation.productFiber value ↔
      pair.re * pair.im = value := by
  letI : DecidableEq K := presentation.eqDecidable
  unfold productFiber
  constructor
  · intro member
    exact of_decide_eq_true (Filter.mem_filter.mp member).2
  · intro equation
    exact Filter.mem_filter.mpr ⟨presentation.scalarPairs_complete pair,
      decide_eq_true equation⟩
end
end Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation

end

section
@[expose] public section
namespace Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation
variable {K : Type*} [ExplicitField K]
section
variable (presentation : Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation K)

/-- A nonzero product fiber is parametrized by its nonzero first coordinate. -/
def nonzeroProductBijection (value : K)
  (valueNonzero : value ≠ 0) :
    Bijection.ListBijection (presentation.productFiber value)
      presentation.nonzeroScalars where
  forward := Algebra.Quadratic.Pair.re
  backward := fun first => ⟨first, value / first⟩
  forward_mem := by
    intro pair member
    apply (presentation.mem_nonzeroScalars_iff pair.re).2
    exact ⟨first_ne_zero_of_product_eq valueNonzero
      pair
      ((presentation.mem_productFiber_iff value pair).1 member),
      presentation.carrierComplete pair.re⟩
  backward_mem := by
    intro first member
    apply (presentation.mem_productFiber_iff value _).2
    have firstNonzero :=
      (presentation.mem_nonzeroScalars_iff first).1 member |>.1
    rw [ExplicitField.div_eq_mul_inv]
    calc
      first * (value * first⁻¹) =
          value * (first * first⁻¹) := by ring1
      _ = value := by
        rw [ExplicitField.mul_inv_cancel first firstNonzero, mul_one]
  backward_forward := by
    intro pair member
    have product := (presentation.mem_productFiber_iff value pair).1 member
    have firstNonzero :=
      first_ne_zero_of_product_eq valueNonzero pair
        product
    apply Algebra.Quadratic.Pair.ext
    · rfl
    · change value / pair.re = pair.im
      rw [ExplicitField.div_eq_mul_inv]
      calc
        value * pair.re⁻¹ =
            (pair.re * pair.im) * pair.re⁻¹ := by rw [product]
        _ = pair.im * (pair.re * pair.re⁻¹) := by ring1
        _ = pair.im := by
          rw [ExplicitField.mul_inv_cancel pair.re firstNonzero,
            mul_one]
  forward_backward := by
    intro _ _
    rfl
end
end Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation

end

section
@[expose] public section
namespace Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation
variable {K : Type*} [ExplicitField K]
section
variable (presentation : Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation K)

/-- Enumerating second coordinates over a duplicate-free first-coordinate list yields no duplicate pairs. -/
private theorem
  scalarPairs_nodup_flatMap
    (presentation : Presentation.FiniteOddFieldPresentation K) :
    ∀ {values : List K}, values.Nodup →
      (values.flatMap fun first =>
        presentation.carrier.map fun second =>
          (⟨first, second⟩ : Algebra.Quadratic.Pair K (1 : K))).Nodup
  | [], _ => List.Pairwise.nil
  | head :: tail, nodup => by
      rw [Flatten.flatMap_cons]
      apply Nodup.nodup_append
      · apply Data.List.Nodup.nodup_map_of_injective
        · intro left right equal
          exact congrArg Algebra.Quadratic.Pair.im equal
        · exact presentation.carrierNodup
      · exact scalarPairs_nodup_flatMap
          presentation
          (List.pairwise_cons.mp nodup).2
      · intro left leftMember right rightMember equal
        rcases Map.mem_map.mp leftMember with
          ⟨leftSecond, _, leftEqual⟩
        rcases Flatten.mem_flatMap.mp rightMember with
          ⟨rightFirst, rightFirstMember, rightSecondMember⟩
        rcases Map.mem_map.mp rightSecondMember with
          ⟨rightSecond, _, rightEqual⟩
        apply (List.pairwise_cons.mp nodup).1 rightFirst rightFirstMember
        calc
          head = left.re := congrArg Algebra.Quadratic.Pair.re leftEqual
          _ = right.re := congrArg Algebra.Quadratic.Pair.re equal
          _ = rightFirst :=
            (congrArg Algebra.Quadratic.Pair.re rightEqual).symm
end
end Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation

end

section
@[expose] public section
namespace Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation
variable {K : Type*} [ExplicitField K]
section
variable (presentation : Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation K)

/-- The complete pair carrier has no duplicates. -/
theorem scalarPairs_nodup :
  presentation.scalarPairs.Nodup := by
  unfold scalarPairs
  exact scalarPairs_nodup_flatMap presentation
    presentation.carrierNodup
end
end Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation

end

section
@[expose] public section
namespace Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation
variable {K : Type*} [ExplicitField K]
section
variable (presentation : Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation K)

/-- Filtering by a coordinate product yields a duplicate-free fiber. -/
theorem productFiber_nodup (value : K) :
    (presentation.productFiber value).Nodup := by
  letI : DecidableEq K := presentation.eqDecidable
  unfold productFiber
  exact Filter.pairwise_filter _ presentation.scalarPairs_nodup
end
end Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation

end

section
@[expose] public section
namespace Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation
variable {K : Type*} [ExplicitField K]
section
variable (presentation : Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation K)

/-- A nonzero product fiber has the same size as the nonzero scalar carrier. -/
theorem productFiber_length_of_ne_zero
  (value : K) (valueNonzero : value ≠ 0) :
    (presentation.productFiber value).length =
      presentation.nonzeroScalars.length := by
  exact ListBijection.length_eq
    (presentation.nonzeroProductBijection value valueNonzero)
    (presentation.productFiber_nodup value)
    presentation.nonzeroScalars_nodup
end
end Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation

end

section
@[expose] public section
namespace Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation
variable {K : Type*} [ExplicitField K]
section
variable (presentation : Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation K)

/-- One two-square affine quadric fiber. -/
def twoSquareFiber (value : K) : List
  (Algebra.Quadratic.Pair K (1 : K)) := by
  letI : DecidableEq K := presentation.eqDecidable
  exact presentation.scalarPairs.filter fun pair => pair.quadrance = value
end
end Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation

end

section
@[expose] public section
namespace Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation
variable {K : Type*} [ExplicitField K]
section
variable (presentation : Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation K)

/-- Executable cardinality of one two-square fiber. -/
def twoSquareCount (value : K) : Nat :=
  (presentation.twoSquareFiber value).length
end
end Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation

end

section
@[expose] public section
namespace Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation
variable {K : Type*} [ExplicitField K]
section
variable (presentation : Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation K)

/-- The ternary quadrance count expressed as the finite sum of its binary slices `r²+s² = value-t²`. -/
def ternaryQuadranceSlicedCount (value :
  K) : Nat :=
  (presentation.carrier.map fun t =>
    presentation.twoSquareCount (value - t ^ 2)).foldr Nat.add 0
end
end Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation

end

section
@[expose] public section
namespace Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation
variable {K : Type*} [ExplicitField K]
section
variable (presentation : Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation K)

/-- Partition a finite sum of two-square slice sizes by square roots of the requested value.

The zero residual has the supplied zero-fiber size, and every nonzero residual has the supplied common size. -/
private theorem ternarySlice_partition
    (presentation : Presentation.FiniteOddFieldPresentation K) (eqDecidable : DecidableEq K)
    (value : K) (zeroFiberSize nonzeroFiberSize : Nat)
    (zeroFiberCount : presentation.twoSquareCount 0 = zeroFiberSize)
    (nonzeroFiberCount : ∀ residual : K, residual ≠ 0 →
      presentation.twoSquareCount residual = nonzeroFiberSize) :
    ∀ values : List K,
      (values.map fun t =>
        presentation.twoSquareCount (value - t ^ 2)).foldr Nat.add 0 =
      (letI : DecidableEq K := eqDecidable
       (values.filter fun t => t ^ 2 = value).length * zeroFiberSize +
         (values.filter fun t => t ^ 2 ≠ value).length * nonzeroFiberSize)
  | [] => by
      change 0 = 0 * zeroFiberSize + 0 * nonzeroFiberSize
      rw [Nat.zero_mul, Nat.zero_mul, Nat.zero_add]
  | head :: tail => by
      letI : DecidableEq K := eqDecidable
      cases eqDecidable (head ^ 2) value with
      | isTrue equal =>
          have residualZero : value - head ^ 2 = 0 := by rw [equal]; ring1
          rw [List.map_cons, List.foldr_cons, residualZero, zeroFiberCount,
            Filter.filter_cons_of_pos
              (predicate := fun t : K => decide (t ^ 2 = value))
              (decide_eq_true equal),
            Filter.filter_cons_of_neg
              (predicate := fun t : K => decide (t ^ 2 ≠ value))
              (fun accepted => (of_decide_eq_true accepted) equal),
            List.length_cons,
            ternarySlice_partition presentation
              eqDecidable value
              zeroFiberSize nonzeroFiberSize zeroFiberCount nonzeroFiberCount tail,
            Nat.succ_mul]
          exact nat_add_swap_first_flat zeroFiberSize _
            _
      | isFalse different =>
          have residualNonzero : value - head ^ 2 ≠ 0 := by
            intro residualZero
            apply different
            calc
              head ^ 2 = value - (value - head ^ 2) := by ring1
              _ = value := by rw [residualZero]; ring1
          rw [List.map_cons, List.foldr_cons,
            nonzeroFiberCount (value - head ^ 2) residualNonzero,
            Filter.filter_cons_of_neg
              (predicate := fun t : K => decide (t ^ 2 = value))
              (fun accepted => different (of_decide_eq_true accepted)),
            Filter.filter_cons_of_pos
              (predicate := fun t : K => decide (t ^ 2 ≠ value))
              (decide_eq_true different),
            List.length_cons,
            ternarySlice_partition presentation
              eqDecidable value
              zeroFiberSize nonzeroFiberSize zeroFiberCount nonzeroFiberCount tail,
            Nat.succ_mul]
          exact nat_add_rotate_first nonzeroFiberSize _
            _
end
end Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation

end

section
@[expose] public section
namespace Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation

variable {K : Type*} [ExplicitField K]
section
variable (presentation : Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation K)

/-- The ternary slice count is the square-root count times the zero-fiber size plus the nonroot count times the common
nonzero-fiber size. -/
theorem
  ternaryQuadranceSlicedCount_eq_root_partition
    (value : K) (zeroFiberSize nonzeroFiberSize : Nat)
    (zeroFiberCount : presentation.twoSquareCount 0 = zeroFiberSize)
    (nonzeroFiberCount : ∀ residual : K, residual ≠ 0 →
      presentation.twoSquareCount residual = nonzeroFiberSize) :
    presentation.ternaryQuadranceSlicedCount value =
      presentation.squareRootCount value * zeroFiberSize +
        presentation.squareNonrootCount value * nonzeroFiberSize := by
  unfold ternaryQuadranceSlicedCount FiniteOddFieldPresentation.squareRootCount
    FiniteOddFieldPresentation.squareNonrootCount
    FiniteOddFieldPresentation.squareRootFiber FiniteOddFieldPresentation.squareNonrootFiber
  exact ternarySlice_partition presentation
    presentation.eqDecidable value
    zeroFiberSize nonzeroFiberSize zeroFiberCount nonzeroFiberCount
    presentation.carrier
end
end Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation

end

section
@[expose] public section
namespace Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation
variable {K : Type*} [ExplicitField K]
section
variable (presentation : Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation K)

/-- A two-square-fiber occurrence has the requested quadrance.

The Boolean filter retains exactly those pairs satisfying the quadrance
equation. The complete displayed pair carrier supplies each source occurrence. -/
theorem mem_twoSquareFiber_iff (value :
  K) (pair : Algebra.Quadratic.Pair K (1 : K)) :
    pair ∈ presentation.twoSquareFiber value ↔ pair.quadrance = value := by
  letI : DecidableEq K := presentation.eqDecidable
  unfold twoSquareFiber
  constructor
  · intro member
    exact of_decide_eq_true (Filter.mem_filter.mp member).2
  · intro equation
    exact Filter.mem_filter.mpr ⟨presentation.scalarPairs_complete pair,
      decide_eq_true equation⟩
end
end Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation

end

section
@[expose] public section
namespace Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation
variable {K : Type*} [ExplicitField K]
section
variable (presentation : Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation K)

/-- In the nonsplit case, the zero conic contains only the origin. -/
def nonsplitZeroFiberBijection
    (minusOneNoRoot : ∀ root : K, root ^ 2 ≠ -1) :
    Bijection.ListBijection (presentation.twoSquareFiber 0)
      [(⟨0, 0⟩ : Algebra.Quadratic.Pair K (1 : K))] where
  forward := fun pair => pair
  backward := fun pair => pair
  forward_mem := by
    intro pair member
    have pairZero :=
      Pair.Coordinates.eq_zero_of_quadrance_eq_zero_of_minus_one_nonsquare
        presentation.eqDecidable minusOneNoRoot pair
        ((presentation.mem_twoSquareFiber_iff 0 pair).1 member)
    rw [pairZero]
    exact List.mem_cons_self
  backward_mem := by
    intro pair member
    rcases Membership.mem_cons.mp member with pairZero | impossible
    · rw [pairZero]
      exact (presentation.mem_twoSquareFiber_iff 0 _).2 (by
        unfold Pair.quadrance
        ring1)
    · nomatch impossible
  backward_forward := by intro _ _; rfl
  forward_backward := by intro _ _; rfl
end
end Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation

end

section
@[expose] public section
namespace Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation
variable {K : Type*} [ExplicitField K]
section
variable (presentation : Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation K)

/-- Each two-square fiber has no duplicates. -/
theorem twoSquareFiber_nodup (value : K)
  :
    (presentation.twoSquareFiber value).Nodup := by
  letI : DecidableEq K := presentation.eqDecidable
  unfold twoSquareFiber
  exact Filter.pairwise_filter _ presentation.scalarPairs_nodup
end
end Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation

end

section
@[expose] public section
namespace Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation

variable {K : Type*} [ExplicitField K]
section
variable (presentation : Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation K)

/-- If minus one is nonsquare, the zero two-square fiber contains exactly one point. -/
theorem
  twoSquareCount_zero_of_minus_one_nonsquare
    (minusOneNoRoot : ∀ root : K, root ^ 2 ≠ -1) :
    presentation.twoSquareCount 0 = 1 := by
  unfold twoSquareCount
  exact ListBijection.length_eq
    (presentation.nonsplitZeroFiberBijection minusOneNoRoot)
    (presentation.twoSquareFiber_nodup 0)
    (Nodup.nodup_singleton (⟨0, 0⟩ : Quadratic.Pair K (1 : K)))
end
end Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation

end

section
@[expose] public section
namespace Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation
variable {K : Type*} [ExplicitField K]
section
variable (presentation : Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation K)

/-- When `-1` has the displayed square root `root`, split coordinates give a constructive bijection from the two-square
conic to the product hyperbola. -/
def twoSquareProductBijection (value
  root : K) (rootSquare : root ^ 2 = -1) :
    Bijection.ListBijection (presentation.twoSquareFiber value)
      (presentation.productFiber value) where
  forward := Pair.Coordinates.split root
  backward := Pair.Coordinates.unsplit root
  forward_mem := by
    intro pair member
    apply (presentation.mem_productFiber_iff value _).2
    rw [Pair.Coordinates.product_split root rootSquare pair]
    exact (presentation.mem_twoSquareFiber_iff value pair).1 member
  backward_mem := by
    intro pair member
    apply (presentation.mem_twoSquareFiber_iff value _).2
    have splitProduct := Pair.Coordinates.product_split root rootSquare
      (Pair.Coordinates.unsplit root pair)
    rw [Pair.Coordinates.split_unsplit root
      (root_ne_zero presentation rootSquare)
        presentation.twoNonzero pair]
      at splitProduct
    exact splitProduct.symm.trans
      ((presentation.mem_productFiber_iff value pair).1 member)
  backward_forward := by
    intro pair _
    exact Pair.Coordinates.unsplit_split root
      (root_ne_zero presentation rootSquare)
        presentation.twoNonzero pair
  forward_backward := by
    intro pair _
    exact Pair.Coordinates.split_unsplit root
      (root_ne_zero presentation rootSquare)
        presentation.twoNonzero pair
end
end Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation

end

section
@[expose] public section
namespace Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation
variable {K : Type*} [ExplicitField K]
section
variable (presentation : Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation K)

/-- A displayed square root of minus one identifies the two-square and product-fiber counts. -/
theorem
  twoSquareCount_eq_productFiber_length
  (value root : K)
    (rootSquare : root ^ 2 = -1) :
    presentation.twoSquareCount value =
      (presentation.productFiber value).length := by
  unfold twoSquareCount
  exact ListBijection.length_eq
    (presentation.twoSquareProductBijection value root rootSquare)
    (presentation.twoSquareFiber_nodup value)
    (presentation.productFiber_nodup value)
end
end Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation

end

section
@[expose] public section
namespace Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation

variable {K : Type*} [ExplicitField K]
section
variable (presentation : Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation K)

/-- If minus one is square, each nonzero two-square fiber has `q - 1` points. -/
theorem
  twoSquareCount_of_minus_one_square_of_ne_zero
    (value root : K) (rootSquare : root ^ 2 = -1)
    (valueNonzero : value ≠ 0) :
    presentation.twoSquareCount value =
      presentation.carrier.length - 1 := by
  rw [presentation.twoSquareCount_eq_productFiber_length value root rootSquare,
    presentation.productFiber_length_of_ne_zero value valueNonzero,
    presentation.nonzeroScalars_length]
end
end Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation

end

section
@[expose] public section
namespace Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation
variable {K : Type*} [ExplicitField K]
section
variable (presentation : Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation K)

/-- If `-1` is nonsquare, the rational circle parametrization plus its exceptional point is a complete constructive
enumeration of `x²+y²=1`. -/
def unitCircleParameterBijection
    (minusOneNoRoot : ∀ root : K, root ^ 2 ≠ -1) :
    Bijection.ListBijection (presentation.twoSquareFiber 1)
      presentation.circleParameters := by
  letI : DecidableEq K := presentation.eqDecidable
  exact
    { forward := fun pair =>
        if pair = Pair.Coordinates.circleInfinity then none
        else some (pair.im / (pair.re + 1))
      backward := fun parameter => match parameter with
        | some value => Pair.Coordinates.circleParameter value
        | none => Pair.Coordinates.circleInfinity
      forward_mem := by
        intro pair member
        if infinity : pair = Pair.Coordinates.circleInfinity then
          rw [if_pos infinity]
          unfold circleParameters
          exact Membership.mem_append.mpr (Or.inr List.mem_cons_self)
        else
          rw [if_neg infinity]
          unfold circleParameters
          apply Membership.mem_append.mpr
          left
          exact Map.mem_map.mpr
            ⟨pair.im / (pair.re + 1),
              presentation.carrierComplete _, rfl⟩
      backward_mem := by
        intro parameter _
        cases parameter with
        | none =>
            exact (presentation.mem_twoSquareFiber_iff 1 _).2
              Pair.Coordinates.circleInfinity_quadrance
        | some value =>
            exact (presentation.mem_twoSquareFiber_iff 1 _).2
              (Pair.Coordinates.quadrance_circleParameter minusOneNoRoot value)
      backward_forward := by
        intro pair member
        have quadranceOne :=
          (presentation.mem_twoSquareFiber_iff 1 pair).1 member
        if infinity : pair = Pair.Coordinates.circleInfinity then
          rw [if_pos infinity]
          exact infinity.symm
        else
          rw [if_neg infinity]
          exact Pair.Coordinates.circleParameter_complete
            presentation.eqDecidable minusOneNoRoot pair quadranceOne infinity
      forward_backward := by
        intro parameter _
        cases parameter with
        | none => rw [if_pos rfl]
        | some value =>
            rw [if_neg (Pair.Coordinates.circleParameter_ne_infinity
              presentation.twoNonzero minusOneNoRoot value)]
            rw [Pair.Coordinates.circleParameter_inverse presentation.twoNonzero
              minusOneNoRoot value] }
end
end Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation

end

section
@[expose] public section
namespace Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation

variable {K : Type*} [ExplicitField K]
section
variable (presentation : Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation K)

/-- If minus one is nonsquare, the unit two-square fiber has `q + 1` points. -/
theorem
  twoSquareCount_one_of_minus_one_nonsquare
    (minusOneNoRoot : ∀ root : K, root ^ 2 ≠ -1) :
    presentation.twoSquareCount 1 = presentation.carrier.length + 1 := by
  unfold twoSquareCount
  calc
    (presentation.twoSquareFiber 1).length =
        presentation.circleParameters.length :=
      ListBijection.length_eq
        (presentation.unitCircleParameterBijection minusOneNoRoot)
        (presentation.twoSquareFiber_nodup 1)
        presentation.circleParameters_nodup
    _ = presentation.carrier.length + 1 :=
      presentation.circleParameters_length
end
end Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation

end

section
@[expose] public section
namespace Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation
variable {K : Type*} [ExplicitField K]
section
variable (presentation : Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation K)

/-- Multiplication by a computed representation of a nonzero value transports the unit circle bijectively onto that
value's two-square fiber. -/
def unitCircleToNonzeroFiberBijection
  (value : K) (valueNonzero : value ≠ 0) :
    Bijection.ListBijection (presentation.twoSquareFiber 1)
      (presentation.twoSquareFiber value) where
  forward := Pair.multiply (presentation.representedPair value)
  backward := Pair.Coordinates.divideMul value (presentation.representedPair value)
  forward_mem := by
    intro pair member
    apply (presentation.mem_twoSquareFiber_iff value _).2
    rw [Pair.quadrance_mul, presentation.representedPair_quadrance,
      (presentation.mem_twoSquareFiber_iff 1 pair).1 member, mul_one]
  backward_mem := by
    intro pair member
    apply (presentation.mem_twoSquareFiber_iff 1 _).2
    exact Pair.Coordinates.quadrance_divideMul value valueNonzero
      (presentation.representedPair value) pair
      (presentation.representedPair_quadrance value)
      ((presentation.mem_twoSquareFiber_iff value pair).1 member)
  backward_forward := by
    intro pair _
    exact Pair.Coordinates.divideMul_mul value valueNonzero
      (presentation.representedPair value) pair
      (presentation.representedPair_quadrance value)
  forward_backward := by
    intro pair _
    exact Pair.Coordinates.mul_divideMul value valueNonzero
      (presentation.representedPair value) pair
      (presentation.representedPair_quadrance value)
end
end Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation

end

section
@[expose] public section
namespace Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation
variable {K : Type*} [ExplicitField K]
section
variable (presentation : Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation K)

/-- Every nonzero two-square fiber has the same count as the unit fiber. -/
theorem twoSquareCount_eq_one_of_ne_zero
  (value : K) (valueNonzero : value ≠ 0) :
    presentation.twoSquareCount value = presentation.twoSquareCount 1 := by
  unfold twoSquareCount
  exact (ListBijection.length_eq
    (presentation.unitCircleToNonzeroFiberBijection value valueNonzero)
    (presentation.twoSquareFiber_nodup 1)
    (presentation.twoSquareFiber_nodup value)).symm
end
end Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation

end

section
@[expose] public section
namespace Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation

variable {K : Type*} [ExplicitField K]
section
variable (presentation : Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation K)

/-- If minus one is nonsquare, each nonzero two-square fiber has `q + 1` points. -/
theorem
  twoSquareCount_of_minus_one_nonsquare_of_ne_zero
    (value : K) (valueNonzero : value ≠ 0)
    (minusOneNoRoot : ∀ root : K, root ^ 2 ≠ -1) :
    presentation.twoSquareCount value = presentation.carrier.length + 1 := by
  rw [presentation.twoSquareCount_eq_one_of_ne_zero value valueNonzero,
    presentation.twoSquareCount_one_of_minus_one_nonsquare minusOneNoRoot]
end
end Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation

end

section
@[expose] public section
namespace Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation

variable {K : Type*} [ExplicitField K]
section
variable (presentation : Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation K)

/-- A nonsquare value has `q² + q` ternary representations when minus one is nonsquare. -/
theorem
  ternaryQuadranceSlicedCount_of_nonsplit_nonsquare
    (value : K)
    (minusOneNoRoot : ∀ root : K, root ^ 2 ≠ -1)
    (valueNoRoot : ∀ root : K, root ^ 2 ≠ value) :
    presentation.ternaryQuadranceSlicedCount value =
      presentation.carrier.length * presentation.carrier.length +
        presentation.carrier.length := by
  have rootCount := presentation.squareRootCount_of_nonsquare value valueNoRoot
  have partition := presentation.squareRootCount_add_squareNonrootCount value
  rw [rootCount, Nat.zero_add] at partition
  have sliced := presentation.ternaryQuadranceSlicedCount_eq_root_partition
    value 1 (presentation.carrier.length + 1)
    (presentation.twoSquareCount_zero_of_minus_one_nonsquare minusOneNoRoot)
    (fun residual residualNonzero =>
      presentation.twoSquareCount_of_minus_one_nonsquare_of_ne_zero
        residual residualNonzero minusOneNoRoot)
  rw [rootCount, Nat.zero_mul, Nat.zero_add, partition] at sliced
  exact sliced.trans (by ring1)
end
end Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation

end

section
@[expose] public section
namespace Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation

variable {K : Type*} [ExplicitField K]
section
variable (presentation : Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation K)

/-- A nonzero square has `q² - q` ternary representations when minus one is nonsquare. -/
theorem
  ternaryQuadranceSlicedCount_of_nonsplit_square
    (value valueRoot : K) (valueNonzero : value ≠ 0)
    (minusOneNoRoot : ∀ root : K, root ^ 2 ≠ -1)
    (valueSquare : valueRoot ^ 2 = value) :
    presentation.ternaryQuadranceSlicedCount value =
      presentation.carrier.length * presentation.carrier.length -
        presentation.carrier.length := by
  have rootCount := presentation.squareRootCount_of_nonzero_square
    value valueRoot valueNonzero valueSquare
  have partition := presentation.squareRootCount_add_squareNonrootCount value
  rw [rootCount] at partition
  have sliced := presentation.ternaryQuadranceSlicedCount_eq_root_partition
    value 1 (presentation.carrier.length + 1)
    (presentation.twoSquareCount_zero_of_minus_one_nonsquare minusOneNoRoot)
    (fun residual residualNonzero =>
      presentation.twoSquareCount_of_minus_one_nonsquare_of_ne_zero
        residual residualNonzero minusOneNoRoot)
  rw [rootCount, Nat.mul_one] at sliced
  have added : presentation.ternaryQuadranceSlicedCount value +
      presentation.carrier.length =
        presentation.carrier.length * presentation.carrier.length := by
    rw [← partition] at sliced ⊢
    calc
      presentation.ternaryQuadranceSlicedCount value +
          (2 + presentation.squareNonrootCount value) =
        (2 + presentation.squareNonrootCount value *
          (2 + presentation.squareNonrootCount value + 1)) +
          (2 + presentation.squareNonrootCount value) :=
            congrArg (fun count => count +
              (2 + presentation.squareNonrootCount value)) sliced
      _ = (2 + presentation.squareNonrootCount value) *
          (2 + presentation.squareNonrootCount value) := by ring1
  exact nat_eq_sub_of_add_eq added
end
end Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation

end

section
@[expose] public section
namespace Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation
variable {K : Type*} [ExplicitField K]
section
variable (presentation : Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation K)

/-- The zero product fiber, with the origin included only on the vertical axis and the horizontal axis restricted to
nonzero first coordinates. -/
def zeroProductPoints : List
  (Algebra.Quadratic.Pair K (1 : K)) :=
  presentation.carrier.map (fun second => ⟨0, second⟩) ++
    presentation.nonzeroScalars.map (fun first => ⟨first, 0⟩)
end
end Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation

end

section
@[expose] public section
namespace Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation
variable {K : Type*} [ExplicitField K]
section
variable (presentation : Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation K)

/-- The disjoint two-axis display consists exactly of pairs with zero coordinate product. -/
theorem mem_zeroProductPoints_iff (pair
  : Algebra.Quadratic.Pair K (1 : K)) :
    pair ∈ presentation.zeroProductPoints ↔
      pair.re * pair.im = 0 := by
  constructor
  · intro member
    rcases Membership.mem_append.mp member with vertical | horizontal
    · rcases Map.mem_map.mp vertical with
        ⟨second, _, equal⟩
      rw [← equal]
      exact zero_mul second
    · rcases Map.mem_map.mp horizontal with
        ⟨first, _, equal⟩
      rw [← equal]
      exact mul_zero first
  · intro product
    cases presentation.eqDecidable pair.re 0 with
    | isTrue firstZero =>
        apply Membership.mem_append.mpr
        left
        apply Map.mem_map.mpr
        refine ⟨pair.im, presentation.carrierComplete pair.im, ?_⟩
        apply Algebra.Quadratic.Pair.ext
        · exact firstZero.symm
        · rfl
    | isFalse firstNonzero =>
        have secondZero : pair.im = 0 := by
          cases presentation.eqDecidable pair.im 0 with
          | isTrue equal => exact equal
          | isFalse secondNonzero =>
              exact False.elim
                (ExplicitField.mul_ne_zero firstNonzero secondNonzero product)
        apply Membership.mem_append.mpr
        right
        apply Map.mem_map.mpr
        refine ⟨pair.re,
          (presentation.mem_nonzeroScalars_iff pair.re).2
            ⟨firstNonzero, presentation.carrierComplete pair.re⟩, ?_⟩
        apply Algebra.Quadratic.Pair.ext
        · rfl
        · exact secondZero.symm
end
end Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation

end

section
@[expose] public section
namespace Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation
variable {K : Type*} [ExplicitField K]
section
variable (presentation : Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation K)

/-- The zero hyperbola fiber and its explicit two-axis display contain the same points. -/
def zeroProductBijection :
    Bijection.ListBijection (presentation.productFiber 0)
      presentation.zeroProductPoints where
  forward := fun pair => pair
  backward := fun pair => pair
  forward_mem := by
    intro pair member
    exact (presentation.mem_zeroProductPoints_iff pair).2
      ((presentation.mem_productFiber_iff 0 pair).1 member)
  backward_mem := by
    intro pair member
    exact (presentation.mem_productFiber_iff 0 pair).2
      ((presentation.mem_zeroProductPoints_iff pair).1 member)
  backward_forward := by intro _ _; rfl
  forward_backward := by intro _ _; rfl
end
end Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation

end

section
@[expose] public section
namespace Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation
variable {K : Type*} [ExplicitField K]
section
variable (presentation : Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation K)

/-- The disjoint two-axis display has `q + (q - 1)` entries. -/
theorem zeroProductPoints_length :
    presentation.zeroProductPoints.length =
      presentation.carrier.length + (presentation.carrier.length - 1) := by
  unfold zeroProductPoints
  rw [Append.length_append, Map.length_map, Map.length_map,
    presentation.nonzeroScalars_length]
end
end Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation

end

section
@[expose] public section
namespace Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation
variable {K : Type*} [ExplicitField K]
section
variable (presentation : Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation K)

/-- The disjoint two-axis display has no duplicates. -/
theorem zeroProductPoints_nodup :
  presentation.zeroProductPoints.Nodup := by
  unfold zeroProductPoints
  apply Nodup.nodup_append
  · apply Data.List.Nodup.nodup_map_of_injective
    · intro left right equal
      exact congrArg Algebra.Quadratic.Pair.im equal
    · exact presentation.carrierNodup
  · apply Data.List.Nodup.nodup_map_of_injective
    · intro left right equal
      exact congrArg Algebra.Quadratic.Pair.re equal
    · exact presentation.nonzeroScalars_nodup
  · intro left leftMember right rightMember equal
    rcases Map.mem_map.mp leftMember with
      ⟨leftSecond, _, leftEqual⟩
    rcases Map.mem_map.mp rightMember with
      ⟨rightFirst, rightFirstMember, rightEqual⟩
    have rightNonzero :=
      (presentation.mem_nonzeroScalars_iff rightFirst).1 rightFirstMember |>.1
    apply rightNonzero
    calc
      rightFirst = right.re := congrArg Algebra.Quadratic.Pair.re rightEqual
      _ = left.re := (congrArg Algebra.Quadratic.Pair.re equal).symm
      _ = 0 := (congrArg Algebra.Quadratic.Pair.re leftEqual).symm
end
end Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation

end

section
@[expose] public section
namespace Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation
variable {K : Type*} [ExplicitField K]
section
variable (presentation : Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation K)

/-- The zero product fiber has `q + (q - 1)` points. -/
theorem productFiber_zero_length :
    (presentation.productFiber 0).length =
      presentation.carrier.length + (presentation.carrier.length - 1) := by
  calc
    (presentation.productFiber 0).length =
        presentation.zeroProductPoints.length :=
      ListBijection.length_eq presentation.zeroProductBijection
        (presentation.productFiber_nodup 0)
        presentation.zeroProductPoints_nodup
    _ = presentation.carrier.length +
        (presentation.carrier.length - 1) :=
      presentation.zeroProductPoints_length
end
end Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation

end

section
@[expose] public section
namespace Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation

variable {K : Type*} [ExplicitField K]
section
variable (presentation : Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation K)

/-- If minus one is square, the zero two-square fiber has `q + (q - 1)` points. -/
theorem
  twoSquareCount_zero_of_minus_one_square
    (root : K) (rootSquare : root ^ 2 = -1) :
    presentation.twoSquareCount 0 =
      presentation.carrier.length + (presentation.carrier.length - 1) := by
  rw [presentation.twoSquareCount_eq_productFiber_length 0 root rootSquare,
    presentation.productFiber_zero_length]
end
end Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation

end

section
@[expose] public section
namespace Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation

variable {K : Type*} [ExplicitField K]
section
variable (presentation : Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation K)

/-- A nonsquare value has `q² - q` ternary representations when minus one is square. -/
theorem
  ternaryQuadranceSlicedCount_of_split_nonsquare
    (value minusOneRoot : K)
    (minusOneSquare : minusOneRoot ^ 2 = -1)
    (valueNoRoot : ∀ root : K, root ^ 2 ≠ value) :
    presentation.ternaryQuadranceSlicedCount value =
      presentation.carrier.length * presentation.carrier.length -
        presentation.carrier.length := by
  have rootCount := presentation.squareRootCount_of_nonsquare value valueNoRoot
  have partition := presentation.squareRootCount_add_squareNonrootCount value
  rw [rootCount, Nat.zero_add] at partition
  have sliced := presentation.ternaryQuadranceSlicedCount_eq_root_partition
    value
    (presentation.carrier.length + (presentation.carrier.length - 1))
    (presentation.carrier.length - 1)
    (presentation.twoSquareCount_zero_of_minus_one_square
      minusOneRoot minusOneSquare)
    (fun residual residualNonzero =>
      presentation.twoSquareCount_of_minus_one_square_of_ne_zero
        residual minusOneRoot minusOneSquare residualNonzero)
  rw [rootCount, Nat.zero_mul, Nat.zero_add, partition] at sliced
  have zeroPartition := presentation.squareRootCount_add_squareNonrootCount 0
  rw [presentation.squareRootCount_zero] at zeroPartition
  have predecessor := carrier_predecessor presentation
  have added : presentation.ternaryQuadranceSlicedCount value +
      presentation.carrier.length =
        presentation.carrier.length * presentation.carrier.length := by
    calc
      presentation.ternaryQuadranceSlicedCount value +
          presentation.carrier.length =
        presentation.carrier.length * (presentation.carrier.length - 1) +
          presentation.carrier.length := congrArg
            (fun count => count + presentation.carrier.length) sliced
      _ = presentation.carrier.length * presentation.carrier.length := by
        rw [predecessor, ← zeroPartition]
        ring1
  exact nat_eq_sub_of_add_eq added
end
end Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation

end

section
@[expose] public section
namespace Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation

variable {K : Type*} [ExplicitField K]
section
variable (presentation : Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation K)

/-- A nonzero square has `q² + q` ternary representations when minus one is square. -/
theorem
  ternaryQuadranceSlicedCount_of_split_square
    (value minusOneRoot valueRoot : K) (valueNonzero : value ≠ 0)
    (minusOneSquare : minusOneRoot ^ 2 = -1)
    (valueSquare : valueRoot ^ 2 = value) :
    presentation.ternaryQuadranceSlicedCount value =
      presentation.carrier.length * presentation.carrier.length +
        presentation.carrier.length := by
  have rootCount := presentation.squareRootCount_of_nonzero_square
    value valueRoot valueNonzero valueSquare
  have partition := presentation.squareRootCount_add_squareNonrootCount value
  rw [rootCount] at partition
  have partitionOne : 1 + (1 + presentation.squareNonrootCount value) =
      presentation.carrier.length := by
    calc
      1 + (1 + presentation.squareNonrootCount value) =
          2 + presentation.squareNonrootCount value := by ring1
      _ = presentation.carrier.length := partition
  have predecessor : presentation.carrier.length - 1 =
      1 + presentation.squareNonrootCount value := by
    calc
      presentation.carrier.length - 1 =
          (1 + (1 + presentation.squareNonrootCount value)) - 1 := by
        rw [partitionOne]
      _ = 1 + presentation.squareNonrootCount value := by
        rw [Subtraction.add_sub_cancel_left]
  have sliced := presentation.ternaryQuadranceSlicedCount_eq_root_partition
    value
    (presentation.carrier.length + (presentation.carrier.length - 1))
    (presentation.carrier.length - 1)
    (presentation.twoSquareCount_zero_of_minus_one_square
      minusOneRoot minusOneSquare)
    (fun residual residualNonzero =>
      presentation.twoSquareCount_of_minus_one_square_of_ne_zero
        residual minusOneRoot minusOneSquare residualNonzero)
  rw [rootCount, predecessor] at sliced
  rw [← partition] at sliced ⊢
  exact sliced.trans (by ring1)
end
end Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation

end

section
@[expose] public section
namespace Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation
variable {K : Type*} [ExplicitField K]
section
variable (presentation : Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation K)

/-- The ternary null cone has exactly `q²` affine points in every displayed odd finite field, independently of the
split/nonsplit binary regime. -/
theorem ternaryQuadranceSlicedCount_zero
  :
    presentation.ternaryQuadranceSlicedCount 0 =
      presentation.carrier.length * presentation.carrier.length := by
  have rootCount := presentation.squareRootCount_zero
  have partition := presentation.squareRootCount_add_squareNonrootCount 0
  rw [rootCount] at partition
  have predecessor : presentation.carrier.length - 1 =
      presentation.squareNonrootCount 0 := by
    calc
      presentation.carrier.length - 1 =
          (1 + presentation.squareNonrootCount 0) - 1 := by rw [partition]
      _ = presentation.squareNonrootCount 0 := by
        rw [Subtraction.add_sub_cancel_left]
  cases presentation.classifyMinusOne with
  | square root rootSquare =>
      have sliced := presentation.ternaryQuadranceSlicedCount_eq_root_partition
        0
        (presentation.carrier.length + (presentation.carrier.length - 1))
        (presentation.carrier.length - 1)
        (presentation.twoSquareCount_zero_of_minus_one_square root rootSquare)
        (fun residual residualNonzero =>
          presentation.twoSquareCount_of_minus_one_square_of_ne_zero
            residual root rootSquare residualNonzero)
      rw [rootCount, Nat.one_mul, predecessor] at sliced
      rw [← partition] at sliced ⊢
      exact sliced.trans (by ring1)
  | nonsquare minusOneNoRoot =>
      have sliced := presentation.ternaryQuadranceSlicedCount_eq_root_partition
        0 1 (presentation.carrier.length + 1)
        (presentation.twoSquareCount_zero_of_minus_one_nonsquare minusOneNoRoot)
        (fun residual residualNonzero =>
          presentation.twoSquareCount_of_minus_one_nonsquare_of_ne_zero
            residual residualNonzero minusOneNoRoot)
      rw [rootCount, Nat.one_mul] at sliced
      rw [← partition] at sliced ⊢
      exact sliced.trans (by ring1)
end
end Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation

end

section
@[expose] public section
namespace Purelib.Geometry.Quadratic.Finite.Fibers.FiniteOddFieldPresentation

variable {K : Type*} [ExplicitField K]
section
variable (presentation : Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation K)

set_option genInjectivity false in
/-- Exhaustive constructive classification of the ternary affine fibers. The four nonzero cases expose exactly which two
square classifications produce the `q²+q` or `q²-q` result. -/
inductive TernaryQuadranceCountClassification
  (value : K) where
  /-- The value is zero and the ternary fiber has `q²` points. -/ | zero (valueZero : value = 0)
      (count : presentation.ternaryQuadranceSlicedCount value =
        presentation.carrier.length * presentation.carrier.length)
  /-- Minus one and the nonzero value have displayed roots, giving `q² + q` ternary points. -/ | splitSquare
    (valueNonzero : value ≠ 0)
      (minusOneRoot valueRoot : K)
      (minusOneSquare : minusOneRoot ^ 2 = -1)
      (valueSquare : valueRoot ^ 2 = value)
      (count : presentation.ternaryQuadranceSlicedCount value =
        presentation.carrier.length * presentation.carrier.length +
          presentation.carrier.length)
  /-- Minus one has a displayed root but the nonzero value is nonsquare, giving `q² - q` ternary points. -/ |
    splitNonsquare (valueNonzero : value ≠ 0)
      (minusOneRoot : K) (minusOneSquare : minusOneRoot ^ 2 = -1)
      (valueNoRoot : ∀ root : K, root ^ 2 ≠ value)
      (count : presentation.ternaryQuadranceSlicedCount value =
        presentation.carrier.length * presentation.carrier.length -
          presentation.carrier.length)
  /-- Minus one is nonsquare and the nonzero value has a displayed root, giving `q² - q` ternary points. -/ |
    nonsplitSquare (valueNonzero : value ≠ 0)
      (minusOneNoRoot : ∀ root : K, root ^ 2 ≠ -1)
      (valueRoot : K) (valueSquare : valueRoot ^ 2 = value)
      (count : presentation.ternaryQuadranceSlicedCount value =
        presentation.carrier.length * presentation.carrier.length -
          presentation.carrier.length)
  /-- Minus one and the nonzero value are nonsquare, giving `q² + q` ternary points. -/ | nonsplitNonsquare
    (valueNonzero : value ≠ 0)
      (minusOneNoRoot : ∀ root : K, root ^ 2 ≠ -1)
      (valueNoRoot : ∀ root : K, root ^ 2 ≠ value)
      (count : presentation.ternaryQuadranceSlicedCount value =
        presentation.carrier.length * presentation.carrier.length +
          presentation.carrier.length)

constructive_injectivity TernaryQuadranceCountClassification

end
end Purelib.Geometry.Quadratic.Finite.Fibers.FiniteOddFieldPresentation

end

section
@[expose] public section

open Purelib.Geometry.Quadratic.Finite.Fibers.FiniteOddFieldPresentation
namespace Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation
variable {K : Type*} [ExplicitField K]
section
variable (presentation : Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation K)

/-- Compute the exact ternary-fiber regime from the displayed equality and square classifiers. -/
def classifyTernaryQuadranceCount (value
  : K) :
    (Geometry.Quadratic.Finite.Fibers.FiniteOddFieldPresentation.TernaryQuadranceCountClassification presentation) value
      := by
  cases presentation.eqDecidable value 0 with
  | isTrue valueZero =>
      exact Geometry.Quadratic.Finite.Fibers.FiniteOddFieldPresentation.TernaryQuadranceCountClassification.zero
        valueZero (by
        rw [valueZero]
        exact presentation.ternaryQuadranceSlicedCount_zero)
  | isFalse valueNonzero =>
      cases presentation.classifyMinusOne with
      | square minusOneRoot minusOneSquare =>
          cases presentation.classifySquare value with
          | square valueRoot valueSquare =>
              exact
                TernaryQuadranceCountClassification.splitSquare
                valueNonzero minusOneRoot valueRoot minusOneSquare valueSquare
                (presentation.ternaryQuadranceSlicedCount_of_split_square
                  value minusOneRoot valueRoot valueNonzero minusOneSquare
                  valueSquare)
          | nonsquare valueNoRoot =>
              exact
                TernaryQuadranceCountClassification.splitNonsquare
                valueNonzero minusOneRoot minusOneSquare valueNoRoot
                (presentation.ternaryQuadranceSlicedCount_of_split_nonsquare
                  value minusOneRoot minusOneSquare valueNoRoot)
      | nonsquare minusOneNoRoot =>
          cases presentation.classifySquare value with
          | square valueRoot valueSquare =>
              exact
                TernaryQuadranceCountClassification.nonsplitSquare
                valueNonzero minusOneNoRoot valueRoot valueSquare
                (presentation.ternaryQuadranceSlicedCount_of_nonsplit_square
                  value valueRoot valueNonzero minusOneNoRoot valueSquare)
          | nonsquare valueNoRoot =>
              exact
                TernaryQuadranceCountClassification.nonsplitNonsquare
                valueNonzero minusOneNoRoot valueNoRoot
                (presentation.ternaryQuadranceSlicedCount_of_nonsplit_nonsquare
                  value minusOneNoRoot valueNoRoot)

end
end Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation

end

section
@[expose] public section
namespace Purelib.Geometry.Quadratic.Finite.Fibers.FiniteOddFieldPresentation
variable {K : Type*} [ExplicitField K]
section
variable (presentation : Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation K)

set_option genInjectivity false in
/-- Constructive exhaustive classification of every binary affine quadric fiber. This is the square-status form of the
usual `q mod 4` dichotomy. -/
inductive TwoSquareCountClassification where
  /-- A displayed root of minus one certifies `2q - 1` points at zero and `q - 1` at every nonzero binary fiber. -/ |
    split (root : K) (rootSquare : root ^ 2 = -1)
      (zeroCount : presentation.twoSquareCount 0 =
        presentation.carrier.length + (presentation.carrier.length - 1))
      (nonzeroCount : ∀ value : K, value ≠ 0 →
        presentation.twoSquareCount value = presentation.carrier.length - 1)
  /-- Nonsquareness of minus one certifies one point at zero and `q + 1` at every nonzero binary fiber. -/ | nonsplit
    (minusOneNoRoot : ∀ root : K, root ^ 2 ≠ -1)
      (zeroCount : presentation.twoSquareCount 0 = 1)
      (nonzeroCount : ∀ value : K, value ≠ 0 →
        presentation.twoSquareCount value = presentation.carrier.length + 1)

constructive_injectivity
  TwoSquareCountClassification

end
end Purelib.Geometry.Quadratic.Finite.Fibers.FiniteOddFieldPresentation

end
section
@[expose] public section
namespace Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation
variable {K : Type*} [ExplicitField K]
section
variable (presentation : Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation K)

/-- Compute the binary-quadric count regime from the cached square table. -/
def classifyTwoSquareCounts :
    (Geometry.Quadratic.Finite.Fibers.FiniteOddFieldPresentation.TwoSquareCountClassification presentation) :=
  match presentation.classifyMinusOne with
  | SquareClassification.square root rootSquare =>
      Geometry.Quadratic.Finite.Fibers.FiniteOddFieldPresentation.TwoSquareCountClassification.split root rootSquare
        (presentation.twoSquareCount_zero_of_minus_one_square root rootSquare)
        (fun value valueNonzero =>
          presentation.twoSquareCount_of_minus_one_square_of_ne_zero
            value root rootSquare valueNonzero)
  | SquareClassification.nonsquare minusOneNoRoot =>
      Geometry.Quadratic.Finite.Fibers.FiniteOddFieldPresentation.TwoSquareCountClassification.nonsplit minusOneNoRoot
        (presentation.twoSquareCount_zero_of_minus_one_nonsquare minusOneNoRoot)
        (fun value valueNonzero =>
          presentation.twoSquareCount_of_minus_one_nonsquare_of_ne_zero
            value valueNonzero minusOneNoRoot)
end
end Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation

end
