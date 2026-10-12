module
public import Purelib.Algebra.Field.Finite.Odd.Presentation
import Purelib.Algebra.Quadratic.Pair.Coordinates
public import Purelib.Data.List.Bijection
import Purelib.Data.List.Nodup
import Purelib.Data.List.Filter
import Purelib.Data.List.Membership
import Purelib.Data.Nat.Subtraction
import Purelib.Tactic.Ring

open Purelib.Algebra.Field
open Purelib.Data.List
open Purelib.Data.Nat
open scoped Purelib.Data.Nat

open Purelib.Algebra.Group in
attribute [local instance high] Negation.subNegZeroMonoid

open Purelib.Data.List.Bijection

section
@[expose] public section
namespace Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation
variable {K : Type*} [ExplicitField K]
section FiniteOddFieldPresentation
variable (presentation : Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation K)

/-- Filtering a finite list for roots of a nonsquare returns the empty list.

The supplied decidable equality checks the square equation, and the no-root hypothesis rejects each candidate. -/
private theorem filter_squareRoot_eq_nil
  (eqDecidable : DecidableEq K)
    (value : K) (noRoot : ∀ root : K, root ^ 2 ≠ value) :
    ∀ values : List K,
      (letI : DecidableEq K := eqDecidable
       values.filter fun root => root ^ 2 = value) = []
  | [] => rfl
  | head :: tail => by
      letI : DecidableEq K := eqDecidable
      rw [List.filter_cons_of_neg
        (p := fun root : K => decide (root ^ 2 = value))
        (fun accepted => noRoot head (of_decide_eq_true accepted))]
      exact Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation.filter_squareRoot_eq_nil
        eqDecidable value noRoot tail
end FiniteOddFieldPresentation
end Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation

end

section
@[expose] public section
namespace Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation
variable {K : Type*} [ExplicitField K]
section FiniteOddFieldPresentation
variable (presentation : Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation K)

/-- A nonzero scalar in the presented odd field differs from its negative.

The presentation's nonzero-two certificate rules out equality of the two signs. -/
private theorem root_ne_neg_root
    (presentation : Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation K)
    (root : K) (rootNonzero : root ≠ 0) :
    root ≠ -root := by
  intro equal
  have twiceZero : (2 : K) * root = 0 := by
    calc
      (2 : K) * root = root + root := by ring1
      _ = -root + root := congrArg (fun value => value + root) equal
      _ = 0 := by ring1
  exact (ExplicitField.mul_ne_zero presentation.twoNonzero rootNonzero)
    twiceZero
end FiniteOddFieldPresentation
end Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation

end

section
@[expose] public section
namespace Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation
variable {K : Type*} [ExplicitField K]
section FiniteOddFieldPresentation
variable (presentation : Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation K)

/-- A displayed root of a nonzero square value is nonzero.

The retained root equation identifies the value with the square of the root.
A zero root would make that square zero, contradicting the supplied value bound. -/
private theorem
  root_ne_zero_of_square_ne_zero {value
  root : K}
    (valueNonzero : value ≠ 0) (rootSquare : root ^ 2 = value) : root ≠ 0 := by
  intro rootZero
  apply valueNonzero
  calc
    value = root ^ 2 := rootSquare.symm
    _ = 0 := by rw [rootZero, pow_two, MulZeroClass.mul_zero]
end FiniteOddFieldPresentation
end Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation

end

section
@[expose] public section
namespace Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation
variable {K : Type*} [ExplicitField K]
section FiniteOddFieldPresentation
variable (presentation : Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation K)

/-- Filter the complete carrier for scalars whose squares differ from the target.

The list preserves carrier order and uses the presentation's retained equality decision. -/
def squareNonrootFiber (value : K) :
  List K := by
  letI : DecidableEq K := presentation.eqDecidable
  exact presentation.carrier.filter fun root => root ^ 2 ≠ value
end FiniteOddFieldPresentation
end Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation

end

section
@[expose] public section
namespace Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation
variable {K : Type*} [ExplicitField K]
section FiniteOddFieldPresentation
variable (presentation : Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation K)

/-- Filter the complete carrier for square roots of the target.

The list preserves carrier order and uses the presentation's retained equality decision. -/
def squareRootFiber (value : K) : List K
  := by
  letI : DecidableEq K := presentation.eqDecidable
  exact presentation.carrier.filter fun root => root ^ 2 = value
end FiniteOddFieldPresentation
end Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation

end

section
@[expose] public section
namespace Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation
variable {K : Type*} [ExplicitField K]
section FiniteOddFieldPresentation
variable (presentation : Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation K)

/-- The root and nonroot filters partition the length of any finite scalar list.

The same target and supplied equality decision are used by the two complementary filters. -/
private theorem
  squareRoot_partition_length
  (eqDecidable : DecidableEq K)
    (value : K) : ∀ values : List K,
    (letI : DecidableEq K := eqDecidable
     (values.filter fun root => root ^ 2 = value).length +
       (values.filter fun root => root ^ 2 ≠ value).length) = values.length
  | [] => rfl
  | head :: tail => by
      letI : DecidableEq K := eqDecidable
      cases eqDecidable (head ^ 2) value with
      | isTrue equal =>
          rw [List.filter_cons_of_pos
              (p := fun root : K => decide (root ^ 2 = value))
              (decide_eq_true equal),
            List.filter_cons_of_neg
              (p := fun root : K => decide (root ^ 2 ≠ value))
              (fun accepted => (of_decide_eq_true accepted) equal)]
          simp only [List.length_cons]
          rw [Nat.succ_add]
          exact congrArg Nat.succ
            (Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation.squareRoot_partition_length
              eqDecidable value tail)
      | isFalse different =>
          rw [List.filter_cons_of_neg
              (p := fun root : K => decide (root ^ 2 = value))
              (fun accepted => different (of_decide_eq_true accepted)),
            List.filter_cons_of_pos
              (p := fun root : K => decide (root ^ 2 ≠ value))
              (decide_eq_true different)]
          simp only [List.length_cons]
          rw [Nat.add_succ]
          exact congrArg Nat.succ
            (Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation.squareRoot_partition_length
              eqDecidable value tail)
end FiniteOddFieldPresentation
end Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation

end

section
@[expose] public section
namespace Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation
variable {K : Type*} [ExplicitField K]
section FiniteOddFieldPresentation
variable (presentation : Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation K)

/-- Count the retained carrier entries that do not square to the target. -/
def squareNonrootCount (value : K) : Nat
  :=
  (presentation.squareNonrootFiber value).length
end FiniteOddFieldPresentation
end Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation

end

section
@[expose] public section
namespace Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation
variable {K : Type*} [ExplicitField K]
section FiniteOddFieldPresentation
variable (presentation : Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation K)

/-- Count the retained carrier entries that square to the target. -/
def squareRootCount (value : K) : Nat :=
  (presentation.squareRootFiber value).length
end FiniteOddFieldPresentation
end Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation

end

section
@[expose] public section
namespace Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation
variable {K : Type*} [ExplicitField K]
section FiniteOddFieldPresentation
variable (presentation : Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation K)

open Purelib.Algebra.Field.Finite.Odd.Presentation in
/-- Membership in the retained root fiber is exactly the target square equation.

Carrier completeness ensures every scalar satisfying the equation occurs in the filtered list. -/
theorem mem_squareRootFiber_iff (value
  root : K) :
    root ∈ presentation.squareRootFiber value ↔ root ^ 2 = value := by
  letI : DecidableEq K := presentation.eqDecidable
  unfold FiniteOddFieldPresentation.squareRootFiber
  constructor
  · intro member
    exact of_decide_eq_true (Filter.mem_filter.mp member).2
  · intro square
    exact Filter.mem_filter.mpr ⟨presentation.carrierComplete root, decide_eq_true square⟩
end FiniteOddFieldPresentation
end Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation

end

section
@[expose] public section
namespace Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation
variable {K : Type*} [ExplicitField K]
section FiniteOddFieldPresentation
variable (presentation : Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation K)

open Purelib.Algebra.Field.Finite.Odd.Presentation in
/-- The retained root fiber of a certified nonsquare is empty. -/
theorem
  squareRootFiber_eq_nil_of_nonsquare
  (value : K)
    (noRoot : ∀ root : K, root ^ 2 ≠ value) :
    presentation.squareRootFiber value = [] := open Purelib.Algebra.Field.Finite.Odd.Presentation in by
  unfold FiniteOddFieldPresentation.squareRootFiber
  exact FiniteOddFieldPresentation.filter_squareRoot_eq_nil presentation.eqDecidable value noRoot
    presentation.carrier
end FiniteOddFieldPresentation
end Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation

end

section
@[expose] public section
namespace Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation
variable {K : Type*} [ExplicitField K]
section FiniteOddFieldPresentation
variable (presentation : Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation K)

open Purelib.Algebra.Field.Finite.Odd.Presentation in
/-- The retained root fiber contains no repeated roots.

Filtering preserves the original carrier's distinctness certificate. -/
theorem squareRootFiber_nodup (value :
  K) :
    (presentation.squareRootFiber value).Nodup := by
  letI : DecidableEq K := presentation.eqDecidable
  unfold FiniteOddFieldPresentation.squareRootFiber
  exact Filter.pairwise_filter _ presentation.carrierNodup
end FiniteOddFieldPresentation
end Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation

end

section
@[expose] public section
namespace Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation
variable {K : Type*} [ExplicitField K]
section FiniteOddFieldPresentation
variable (presentation : Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation K)

/-- Identify the root fiber with the displayed root and its negative using identity maps.

A supplied square equation is sufficient for the membership correspondence; the two target entries are proved distinct
separately for nonzero values. -/
def nonzeroSquareRootBijection (value
  root : K) (rootSquare : root ^ 2 = value) :
    ListBijection (presentation.squareRootFiber value) [root, -root] where
  forward := fun candidate => candidate
  backward := fun candidate => candidate
  forward_mem := by
    intro candidate member
    have candidateSquare :=
      (presentation.mem_squareRootFiber_iff value candidate).1 member
    have equalSquares : candidate ^ 2 = root ^ 2 :=
      candidateSquare.trans rootSquare.symm
    cases presentation.eqDecidable candidate root with
    | isTrue equal => exact Membership.mem_cons.mpr (Or.inl equal)
    | isFalse notRoot =>
        have firstFactorNonzero : candidate - root ≠ 0 := by
          intro differenceZero
          apply notRoot
          calc
            candidate = (candidate - root) + root := by ring1
            _ = root := by rw [differenceZero, zero_add]
        have productZero : (candidate - root) * (candidate + root) = 0 := by
          calc
            (candidate - root) * (candidate + root) =
                candidate ^ 2 - root ^ 2 := by ring1
            _ = 0 := by rw [equalSquares]; ring1
        have secondFactorZero : candidate + root = 0 := by
          cases presentation.eqDecidable (candidate + root) 0 with
          | isTrue equal => exact equal
          | isFalse secondFactorNonzero =>
              exact False.elim
                ((ExplicitField.mul_ne_zero firstFactorNonzero
                  secondFactorNonzero) productZero)
        apply Membership.mem_cons.mpr
        right
        apply Membership.mem_cons.mpr
        left
        calc
          candidate = (candidate + root) - root := by ring1
          _ = -root := by rw [secondFactorZero]; ring1
  backward_mem := by
    intro candidate member
    rcases Membership.mem_cons.mp member with rootEqual | negativeMember
    · rw [rootEqual]
      exact (presentation.mem_squareRootFiber_iff value root).2 rootSquare
    · rcases Membership.mem_cons.mp negativeMember with negativeEqual | impossible
      · rw [negativeEqual]
        apply (presentation.mem_squareRootFiber_iff value (-root)).2
        calc
          (-root) ^ 2 = root ^ 2 := by rw [pow_two, pow_two]; ring1
          _ = value := rootSquare
      · nomatch impossible
  backward_forward := by intro _ _; rfl
  forward_backward := by intro _ _; rfl
end FiniteOddFieldPresentation
end Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation

end

section
@[expose] public section
namespace Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation
variable {K : Type*} [ExplicitField K]
section FiniteOddFieldPresentation
variable (presentation : Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation K)

open Purelib.Algebra.Field.Finite.Odd.Presentation in
/-- A certified nonsquare has zero retained square roots. -/
theorem squareRootCount_of_nonsquare
  (value : K)
    (noRoot : ∀ root : K, root ^ 2 ≠ value) :
    presentation.squareRootCount value = 0 := by
  unfold FiniteOddFieldPresentation.squareRootCount
  rw [presentation.squareRootFiber_eq_nil_of_nonsquare value noRoot]
  rfl
end FiniteOddFieldPresentation
end Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation

end

section
@[expose] public section
namespace Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation
variable {K : Type*} [ExplicitField K]
section FiniteOddFieldPresentation
variable (presentation : Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation K)

open Purelib.Algebra.Field.Finite.Odd.Presentation in
/-- The root and nonroot counts add to the full carrier length. -/
theorem
  squareRootCount_add_squareNonrootCount
  (value : K) :
    presentation.squareRootCount value +
      presentation.squareNonrootCount value = presentation.carrier.length := open
        Purelib.Algebra.Field.Finite.Odd.Presentation in by
  unfold FiniteOddFieldPresentation.squareRootCount FiniteOddFieldPresentation.squareNonrootCount
    FiniteOddFieldPresentation.squareRootFiber FiniteOddFieldPresentation.squareNonrootFiber
  exact FiniteOddFieldPresentation.squareRoot_partition_length presentation.eqDecidable value
    presentation.carrier
end FiniteOddFieldPresentation
end Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation

end

section
@[expose] public section
namespace Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation
variable {K : Type*} [ExplicitField K]
section FiniteOddFieldPresentation
variable (presentation : Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation K)

/-- Identify the zero-square fiber with the singleton zero using identity maps.

Every scalar with zero square is zero, and carrier completeness retains that unique root. -/
def zeroSquareRootBijection :
    ListBijection (presentation.squareRootFiber 0) [(0 : K)] where
  forward := fun root => root
  backward := fun root => root
  forward_mem := by
    intro root member
    have rootZero := Quadratic.Pair.Coordinates.eq_zero_of_square_eq_zero
      presentation.eqDecidable root
      ((presentation.mem_squareRootFiber_iff 0 root).1 member)
    rw [rootZero]
    exact List.mem_cons_self
  backward_mem := by
    intro root member
    rcases Membership.mem_cons.mp member with rootZero | impossible
    · rw [rootZero]
      exact (presentation.mem_squareRootFiber_iff 0 0).2 (by rw [pow_two, MulZeroClass.mul_zero])
    · nomatch impossible
  backward_forward := by intro _ _; rfl
  forward_backward := by intro _ _; rfl
end FiniteOddFieldPresentation
end Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation

end
section
@[expose] public section
namespace Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation
variable {K : Type*} [ExplicitField K]
section FiniteOddFieldPresentation
variable (presentation : Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation K)

/-- The nonroot count is the carrier length minus the root count.

The complementary filters partition every retained carrier occurrence. Natural
subtraction therefore recovers the nonroot count from the certified total. -/
theorem
  squareNonrootCount_eq_length_sub_squareRootCount
  (value : K) :
    presentation.squareNonrootCount value =
      presentation.carrier.length - presentation.squareRootCount value := by
  have partition := presentation.squareRootCount_add_squareNonrootCount value
  calc
    presentation.squareNonrootCount value =
        (presentation.squareRootCount value +
          presentation.squareNonrootCount value) -
            presentation.squareRootCount value := by
      exact (Subtraction.add_sub_cancel_left _ _).symm
    _ = presentation.carrier.length - presentation.squareRootCount value :=
      congrArg (fun count => count - presentation.squareRootCount value)
        partition
end FiniteOddFieldPresentation
end Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation

end

section
@[expose] public section
namespace Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation
variable {K : Type*} [ExplicitField K]
section FiniteOddFieldPresentation
variable (presentation : Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation K)

open Purelib.Algebra.Field.Finite.Odd.Presentation in
/-- A displayed nonzero square has exactly two roots in the retained carrier.

The supplied root and its negative exhaust the root fiber and are distinct because two is nonzero. -/
theorem
  squareRootCount_of_nonzero_square
  (value root : K)
    (valueNonzero : value ≠ 0) (rootSquare : root ^ 2 = value) :
    presentation.squareRootCount value = 2 := open Purelib.Algebra.Field.Finite.Odd.Presentation in open Purelib in by
  unfold FiniteOddFieldPresentation.squareRootCount
  exact ListBijection.length_eq
    (presentation.nonzeroSquareRootBijection value root rootSquare)
    (presentation.squareRootFiber_nodup value)
    (Data.List.Nodup.nodup_append
      (Data.List.Nodup.nodup_singleton root)
      (Data.List.Nodup.nodup_singleton (-root)) (by
        intro left leftMember right rightMember
        rcases Membership.mem_cons.mp leftMember with leftEqual | leftImpossible
        · rcases Membership.mem_cons.mp rightMember with
            rightEqual | rightImpossible
          · rw [leftEqual, rightEqual]
            exact FiniteOddFieldPresentation.root_ne_neg_root presentation root
              (FiniteOddFieldPresentation.root_ne_zero_of_square_ne_zero valueNonzero rootSquare)
          · nomatch rightImpossible
        · nomatch leftImpossible))
end FiniteOddFieldPresentation
end Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation

end

section
@[expose] public section
namespace Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation
variable {K : Type*} [ExplicitField K]
section FiniteOddFieldPresentation
variable (presentation : Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation K)

open Purelib.Algebra.Field.Finite.Odd.Presentation in
/-- Zero has exactly one square root in the retained carrier. -/
theorem squareRootCount_zero :
  presentation.squareRootCount 0 = 1 := open Purelib in by
  unfold FiniteOddFieldPresentation.squareRootCount
  exact ListBijection.length_eq presentation.zeroSquareRootBijection
    (presentation.squareRootFiber_nodup 0)
    (Data.List.Nodup.nodup_singleton (0 : K))
end FiniteOddFieldPresentation
end Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation

end
