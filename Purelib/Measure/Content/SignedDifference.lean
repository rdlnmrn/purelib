module
import Purelib.Data.Rat.Fraction.Field
import Purelib.Measure.Content.Basic
public import Purelib.Measure.Content.Histogram
import Purelib.Measure.Content.Integral
import Purelib.Measure.Content.Operations
import Purelib.Measure.SignedContent.Basic
public import Purelib.Measure.SignedContent.Hahn.Basic
import Purelib.Measure.Weighted.Basic
import Purelib.Measure.Weighted.Consolidation
import Purelib.Measure.Weighted.Integral
import Purelib.Tactic.Ring
import Purelib.Data.Rat.Fraction
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Order.Basic

section
public section

/-!
# Total variation distance between finite rational laws

The duplicate-free union of two displayed atom catalogues supports their
signed difference.  A decidable comparison of the two singleton masses gives
an executable Hahn event.  For probability distributions this event attains
the largest possible event-probability discrepancy, because the positive and
negative Jordan masses agree.

Thus total variation is an exact rational computation here.  The development
proves its sharp event bound, half-L1 formula, metric laws modulo evaluation
equivalence, contraction under pushforward, and the coupling inequality.
-/

namespace Purelib.Measure

namespace Content

/-- Build signed content on the shared consolidated keys using original left singleton mass minus original right
singleton mass.

The exact finite key list covers both original contents without repeated payloads, so cancellation occurs at singleton
masses before constructing the signed occurrence list. -/
@[expose] def signedDifference {α : Type} [DecidableEq α]
    (left right : Content α) : SignedContent α where
  atoms := (left.radonNikodymKeys right).map fun key =>
    { item := key.item
      weight := left.measure (atomEvent key.item) -
        right.measure (atomEvent key.item) }

/-- Signed content retains identical rows under either supplied equality procedure. -/
theorem signedDifference_eq_of_decidableEq {α : Type} (first second : DecidableEq α)
    (left right : Content α) :
    @signedDifference α first left right = @signedDifference α second left right := by
  have keys : @radonNikodymKeys α first left right =
      @radonNikodymKeys α second left right :=
    consolidateAtoms_eq_of_decidableEq first second (left.atoms ++ right.atoms)
  have rows : ∀ keys : List (Weighted α),
      keys.map (fun key => SignedWeighted.mk key.item
        (left.measure (@atomEvent α first key.item) - right.measure (@atomEvent α first key.item))) =
      keys.map (fun key => SignedWeighted.mk key.item
        (left.measure (@atomEvent α second key.item) - right.measure (@atomEvent α second key.item))) := by
    intro keys
    induction keys with
    | nil => rfl
    | cons key remaining ih =>
        have leftMass := left.measure_congr (@atomEvent α first key.item)
          (@atomEvent α second key.item) (atomEvent_eq_of_decidableEq first second key.item)
        have rightMass := right.measure_congr (@atomEvent α first key.item)
          (@atomEvent α second key.item) (atomEvent_eq_of_decidableEq first second key.item)
        exact congrArg₂ List.cons (congrArg (SignedWeighted.mk key.item)
          (congrArg₂ (fun a b => a - b) leftMass rightMass)) ih
  unfold signedDifference
  apply congrArg SignedContent.mk
  exact (congrArg (fun keys : List (Weighted α) => keys.map fun key =>
    SignedWeighted.mk key.item (left.measure (@atomEvent α first key.item) -
      right.measure (@atomEvent α first key.item))) keys).trans (rows _)

section
open Purelib.Data.Rat
/-- Signed event evaluation on mass-difference rows equals the difference of original key-indexed indicator mass sums.
-/
private theorem signedEventWeight_differenceKeys {α : Type}
    [DecidableEq α] (left right : Content α)
    (event : α → Bool) :
    ∀ keys : List (Weighted α),
      signedEventWeight
          (keys.map fun key =>
            { item := key.item
              weight := left.measure (atomEvent key.item) -
                right.measure (atomEvent key.item) : SignedWeighted α })
          event =
        left.atomMassSum keys (Distribution.indicator event) -
          right.atomMassSum keys (Distribution.indicator event)
  | [] => by
      change (0 : Fraction.Rational) = 0 - 0
      ring1
  | key :: remaining => by
      simp only [-eq_self, -iff_self, List.map_cons, signedEventWeight, atomMassSum]
      cases selected : event key.item
      · simp only [-eq_self, -iff_self, selected, if_neg (by decide : ¬ false = true),
          Distribution.indicator,
          signedEventWeight_differenceKeys left right event remaining]
        ring1
      · simp only [-eq_self, -iff_self, selected, if_pos rfl, Distribution.indicator, mul_one,
          signedEventWeight_differenceKeys left right event remaining]
        ring1

/-- Signed integration on mass-difference rows equals the difference of original key-indexed observable mass sums. -/
private theorem signedIntegralWeight_differenceKeys {α : Type}
    [DecidableEq α] (left right : Content α)
    (value : α → Fraction.Rational) :
    ∀ keys : List (Weighted α),
      signedIntegralWeight
          (keys.map fun key =>
            { item := key.item
              weight := left.measure (atomEvent key.item) -
                right.measure (atomEvent key.item) : SignedWeighted α })
          value =
        left.atomMassSum keys value - right.atomMassSum keys value
  | [] => by
      change (0 : Fraction.Rational) = 0 - 0
      ring1
  | key :: remaining => by
      simp only [-eq_self, -iff_self, List.map_cons, signedIntegralWeight, atomMassSum,
        signedIntegralWeight_differenceKeys left right value remaining]
      ring1

end

/-- The retained signed-difference content measures every event as original left mass minus original right mass. -/
theorem signedDifference_measure {α : Type} [DecidableEq α]
    (left right : Content α) (event : α → Bool) :
    (left.signedDifference right).measure event =
      left.measure event - right.measure event := by
  unfold signedDifference SignedContent.measure
  rw [signedEventWeight_differenceKeys]
  rw [left.atomMassSum_eq_integral (Distribution.indicator event)
      (left.radonNikodymKeys right)
      (left.radonNikodymKeys_noRepeated right)
      (left.payloadsCovered_radonNikodymKeys_left right),
    right.atomMassSum_eq_integral (Distribution.indicator event)
      (left.radonNikodymKeys right)
      (left.radonNikodymKeys_noRepeated right)
      (left.payloadsCovered_radonNikodymKeys_right right),
    left.integral_indicator, right.integral_indicator]

open Purelib.Data.Rat in
/-- The retained signed-difference content integrates every observable as original left integral minus original right
integral. -/
theorem signedDifference_integral {α : Type} [DecidableEq α]
    (left right : Content α) (value : α → Fraction.Rational) :
    (left.signedDifference right).integral value =
      left.integral value - right.integral value := by
  unfold signedDifference SignedContent.integral
  rw [signedIntegralWeight_differenceKeys]
  rw [left.atomMassSum_eq_integral value
      (left.radonNikodymKeys right)
      (left.radonNikodymKeys_noRepeated right)
      (left.payloadsCovered_radonNikodymKeys_left right),
    right.atomMassSum_eq_integral value
      (left.radonNikodymKeys right)
      (left.radonNikodymKeys_noRepeated right)
      (left.payloadsCovered_radonNikodymKeys_right right)]

/-- The retained signed-difference content has total equal to original left total minus original right total. -/
theorem signedDifference_total {α : Type} [DecidableEq α]
    (left right : Content α) :
    (left.signedDifference right).total = left.total - right.total := by
  calc
    (left.signedDifference right).total =
        (left.signedDifference right).measure (fun _ => true) :=
      ((left.signedDifference right).measure_univ).symm
    _ = left.measure (fun _ => true) - right.measure (fun _ => true) :=
      left.signedDifference_measure right (fun _ => true)
    _ = left.total - right.total := by
      rw [left.measure_univ, right.measure_univ]

open Purelib.Data.List in
open Purelib.Data.Rat in
/-- Certify the exact singleton-mass difference as nonnegative where right mass is at most left mass.

The retained decidable event compares the same original singleton readings used to construct every signed difference
row. -/
@[expose] def signedDifferenceHahnCertificate {α : Type} [DecidableEq α]
    (left right : Content α) :
    SignedContent.HahnCertificate (left.signedDifference right) where
  positiveEvent := fun item =>
    decide (right.measure (atomEvent item) ≤
      left.measure (atomEvent item))
  selected_nonnegative := by
    intro atom member selected
    unfold signedDifference at member
    rcases Map.mem_map.mp member with ⟨key, keyMember, equal⟩
    subst atom
    exact Fraction.Order.Arithmetic.sub_nonneg_direct (of_decide_eq_true selected)
  unselected_nonpositive := by
    intro atom member unselected
    unfold signedDifference at member
    rcases Map.mem_map.mp member with ⟨key, keyMember, equal⟩
    subst atom
    apply Fraction.Order.Boundary.sub_nonpositive_iff.mpr
    apply (Fraction.Order.Arithmetic.lt_of_not_ge_direct ?_).le
    intro order
    have selected : decide
        (right.measure (atomEvent key.item) ≤
          left.measure (atomEvent key.item)) = true :=
      decide_eq_true order
    rw [selected] at unselected
    exact Bool.noConfusion unselected

end Content

end Purelib.Measure

end
