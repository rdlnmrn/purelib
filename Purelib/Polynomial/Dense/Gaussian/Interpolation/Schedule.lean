module

public import Purelib.Polynomial.Dense.Gaussian.Interpolation
public import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Tactic.Ring

/-!
# Prepaid residual targets for original synthetic expansions

A backward finite schedule depends only on positive source-residual targets
and one positive squared node-separation floor. Each stored incoming payment
uses its same retained tail payment. The original synthetic expansion then
pays every target through its actual sequential quotients and remainders;
neither scheduling nor readback constructs another division or observation.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Interpolation

open Purelib.Data
open Purelib.Data.Rat
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Rat.Fraction (Rational)
open Rat.Fraction.Order

set_option genInjectivity false in
/-- Cached incoming sample tolerances at the original ordered target occurrences.

The empty schedule has the fixed positive terminal tolerance one. A nonempty
cell stores its actual incoming tolerance and the same already-prepared tail.
The original target list remains the index rather than a copied coefficient
or node owner.
-/
public inductive Schedule : List Rational → Type
  /-- No remaining target requires no further payment cell. -/
  | nil : Schedule []
  /-- Retain the current incoming tolerance and its original scheduled tail. -/
  | cons {target : Rational} {remaining : List Rational}
      (incoming : Rational) (tail : Schedule remaining) : Schedule (target :: remaining)

namespace Schedule

/-- Read the actual stored initial tolerance, or the fixed terminal tolerance for an empty schedule. -/
@[expose] public def initial {targets : List Rational} : Schedule targets → Rational
  | .nil => 1
  | .cons incoming _ => incoming

/-- Read the same stored schedule tail without computing another backward payment. -/
@[expose] public def next {target : Rational} {remaining : List Rational} :
    Schedule (target :: remaining) → Schedule remaining
  | .cons _ tail => tail

set_option genInjectivity false in
/-- Exact backward payment certificates for the same stored ordered schedule.

Each original target is positive. The current incoming tolerance is exactly
the smaller of that target and one quarter of the separation-scaled retained
tail tolerance. The certificate recursively refers to that same cached tail.
-/
public inductive Paid (separation : Rational) :
    {targets : List Rational} → Schedule targets → Prop
  /-- The fixed terminal tolerance certifies the empty target list. -/
  | nil : Paid separation .nil
  /-- Certify the same retained current tolerance and its exact original tail. -/
  | cons {target incoming : Rational} {remaining : List Rational} {tail : Schedule remaining}
      (targetPositive : 0 < target) (incomingPositive : 0 < incoming) (tailPaid : Paid separation tail)
      (incoming_eq : incoming = min target (tail.initial * separation / 4)) :
      Paid separation (.cons (target := target) incoming tail)

/-- A prepared schedule retains actual payment data with their exact backward certificate. -/
public abbrev Prepared (separation : Rational) (targets : List Rational) :=
  {schedule : Schedule targets // schedule.Paid separation}

namespace Paid

/-- Read the original current target's positive payment prerequisite. -/
public theorem target_positive {separation target : Rational} {remaining : List Rational}
    {schedule : Schedule (target :: remaining)} (paid : schedule.Paid separation) : 0 < target := by
  cases paid with
  | cons positive _ _ _ => exact positive

/-- The same stored schedule tail carries its original exact backward certificate. -/
public theorem next {separation target : Rational} {remaining : List Rational}
    {schedule : Schedule (target :: remaining)} (paid : schedule.Paid separation) :
    schedule.next.Paid separation := by
  cases paid with
  | cons _ _ tail _ => exact tail

/-- Every actual retained incoming tolerance carries its constructive positivity certificate. -/
public theorem positive {separation : Rational}
    {targets : List Rational} {schedule : Schedule targets} (paid : schedule.Paid separation) :
    0 < schedule.initial := by
  cases paid with
  | nil => decide
  | cons _ positive _ _ => exact positive

/-- Read the exact backward equation from the same cached current and tail tolerances. -/
public theorem initial_eq {separation target : Rational} {remaining : List Rational}
    {schedule : Schedule (target :: remaining)} (paid : schedule.Paid separation) :
    schedule.initial = min target (schedule.next.initial * separation / 4) := by
  cases paid with
  | cons _ _ _ equation => exact equation

/-- The current stored tolerance pays its corresponding original target. -/
public theorem head_le {separation target : Rational} {remaining : List Rational}
    {schedule : Schedule (target :: remaining)} (paid : schedule.Paid separation) :
    schedule.initial ≤ target := by
  cases paid with
  | cons _ _ _ equation =>
      rewrite [equation]
      exact Rat.Fraction.Order.Basic.min_le_left _ _

/-- The same current tolerance pays the original four-over-separation tail amplification. -/
public theorem next_le {separation target : Rational} {remaining : List Rational}
    {schedule : Schedule (target :: remaining)} (paid : schedule.Paid separation)
    (separationPositive : 0 < separation) :
    4 * schedule.initial / separation ≤ schedule.next.initial := by
  cases schedule with
  | cons incoming tail =>
      cases paid with
      | cons _ _ _ equation =>
          change 4 * incoming / separation ≤ tail.initial
          apply (Field.div_le_iff_pos separationPositive).mpr
          have payment : incoming * 4 ≤ tail.initial * separation :=
            (Field.le_div_iff_pos (by decide : (0 : Rational) < 4)).mp
              (equation ▸ Rat.Fraction.Order.Basic.min_le_right _ _)
          exact payment.trans_eq' (Rat.Fraction.Field.mul_comm _ _)

end Paid

/-- Prepare all positive residual targets before any source sample or synthetic division is observed.

Recursion stores the original tail first. Its retained initial tolerance pays
the current finite minimum, and both the incoming value and complete tail
are returned with the exact constructor certificate.
-/
@[expose] public def prepare (separation : Rational) (separationPositive : 0 < separation) :
    (targets : List Rational) → (∀ target ∈ targets, 0 < target) → Prepared separation targets
  | [], _ => ⟨.nil, .nil⟩
  | target :: remaining, positive =>
      let tail := prepare separation separationPositive remaining
        (fun next member => positive next (List.mem_cons_of_mem target member))
      let incoming := min target (tail.val.initial * separation / 4)
      have incomingPositive : 0 < incoming := Rat.Fraction.Order.Basic.lt_min
        (positive target List.mem_cons_self)
        (Field.div_pos_direct (Arithmetic.mul_pos_direct tail.property.positive separationPositive) (by decide))
      ⟨.cons incoming tail.val,
        .cons (positive target List.mem_cons_self) incomingPositive tail.property rfl⟩

end Schedule

namespace Expansion

set_option genInjectivity false in
/-- Each original retained synthetic head remainder pays its corresponding original ordered target.

The tail certificate concerns the same stored quotient expansion. This is a
certificate about the actual finite division chain, not a list of proposed
roots or a second set of independently evaluated quotient polynomials.
-/
public inductive Pays : {polynomial : CoefficientPolynomial} → {nodes : List Canonical} →
    Expansion polynomial nodes → List Rational → Prop
  /-- Empty original expansions pay the empty target list. -/
  | nil {polynomial : CoefficientPolynomial} : Pays (.nil : Expansion polynomial []) []
  /-- The actual retained head remainder and its same quotient tail pay their original targets. -/
  | cons {polynomial : CoefficientPolynomial} {node : Canonical} {remaining : List Canonical}
      {division : Division.Synthetic.Result polynomial node}
      {equation : division = Division.Synthetic.divide polynomial node}
      {tail : Expansion division.quotient remaining} {target : Rational} {targets : List Rational}
      (head : Norm.Basic.normSq division.remainder ≤ target) (next : Pays tail targets) :
      Pays (.cons division equation tail) (target :: targets)

namespace Pays

/-- Every paid target corresponds to exactly one original retained division occurrence. -/
public theorem length {polynomial : CoefficientPolynomial} {nodes : List Canonical}
    {expansion : Expansion polynomial nodes} {targets : List Rational} (paid : expansion.Pays targets) :
    targets.length = nodes.length := by
  induction paid with
  | nil => rfl
  | cons _ _ inductionHypothesis => exact congrArg Nat.succ inductionHypothesis

/-- Read the current actual stored remainder's original target payment. -/
public theorem head {polynomial : CoefficientPolynomial} {node : Canonical} {remaining : List Canonical}
    {expansion : Expansion polynomial (node :: remaining)} {target : Rational} {targets : List Rational}
    (paid : expansion.Pays (target :: targets)) :
    Norm.Basic.normSq expansion.first.remainder ≤ target := by
  cases paid with
  | cons head _ => exact head

/-- The same retained remainder payment bounds its original source polynomial's actual head-node value. -/
public theorem head_eval {polynomial : CoefficientPolynomial} {node : Canonical} {remaining : List Canonical}
    {expansion : Expansion polynomial (node :: remaining)} {target : Rational} {targets : List Rational}
    (paid : expansion.Pays (target :: targets)) :
    Norm.Basic.normSq (polynomial.eval node) ≤ target := by
  rewrite [← expansion.first.remainder_eval]
  exact paid.head

/-- Read the payment certificate for the same stored first quotient's expansion. -/
public theorem next {polynomial : CoefficientPolynomial} {node : Canonical} {remaining : List Canonical}
    {expansion : Expansion polynomial (node :: remaining)} {target : Rational} {targets : List Rational}
    (paid : expansion.Pays (target :: targets)) : expansion.next.Pays targets := by
  cases paid with
  | cons _ next => exact next

end Pays

/-- The pre-observation backward schedule pays every same retained sequential original head residual.

One original source sample bound at all original separated nodes suffices.
The original first quotient's tail sample theorem propagates that payment to
the same stored next expansion. No roots, division results or sufficient
search fuel are supplied by this schedule.
-/
public theorem pays {polynomial : CoefficientPolynomial} {nodes : List Canonical}
    (expansion : Expansion polynomial nodes) {separation : Rational}
    (separationPositive : 0 < separation) {targets : List Rational}
    (schedule : Schedule targets) (paid : schedule.Paid separation)
    (count : targets.length = nodes.length)
    (separated : nodes.Pairwise (fun left right =>
      separation ≤ Norm.Basic.normSq (left - right)))
    (samples : ∀ point ∈ nodes, Norm.Basic.normSq (polynomial.eval point) ≤ schedule.initial) :
    expansion.Pays targets := by
  induction expansion generalizing targets with
  | @nil polynomial =>
      cases targets with
      | nil => exact .nil
      | cons target remaining => exact (Nat.noConfusion count)
  | @cons polynomial node remaining division equation tail inductionHypothesis =>
      cases targets with
      | nil => exact (Nat.noConfusion count)
      | cons target targets =>
          cases schedule with
          | cons incoming rest =>
              apply Pays.cons
              · exact ((division.remainder_eval ▸ samples node List.mem_cons_self)).trans paid.head_le
              · apply inductionHypothesis rest paid.next (Nat.succ.inj count) (List.pairwise_cons.mp separated).2
                intro point member
                exact ((Expansion.cons division equation tail).next_samples_le separationPositive
                  separated samples point member).trans (paid.next_le separationPositive)

end Expansion
end Purelib.Polynomial.Dense.Gaussian.Interpolation
