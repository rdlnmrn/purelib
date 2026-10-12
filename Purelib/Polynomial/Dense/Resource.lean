module
import Purelib.Algebra.Group.Negation
import Purelib.Data.List.DropWhile.Basic
import Purelib.Data.List.Membership
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Algebra.Field.Resource.Magnitude
import Purelib.Data.List.Map
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Basic
public import Purelib.Polynomial.Dense.Division.Basic
import Purelib.Polynomial.Dense.Division.CancelLead
public import Purelib.Polynomial.Dense.Multiplication

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Polynomial.Dense.Evaluation
import Mathlib.Algebra.Ring.Defs
import Mathlib.Order.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.GroupWithZero.Nat

open Purelib.Algebra.Field

open Purelib

open Purelib.Polynomial

open Purelib.Algebra.Group in
attribute [local instance high] Negation.subNegZeroMonoid

section
@[expose] public section

/-!
# Resource envelopes for normalized dense-polynomial arithmetic

This module supplies a common finite accounting layer for dense polynomials
whose coefficients are canonical reduced rational or Gaussian-rational
records.  A single arithmetic operation advances a monotone component
envelope.  Iterating that envelope along the actual Horner and long-division
recursions gives source-only bounds for every coefficient record they carry.
-/

namespace Purelib.Polynomial.Dense.Resource

open Purelib.Algebra Purelib.Algebra.Field.Resource Purelib.Polynomial Purelib.Data
open Purelib.Polynomial.Dense.Basic
open _root_.Purelib.Polynomial.Dense.Basic renaming CoefficientPolynomial -> Dense

/-- The descending dense polynomial representation whose coefficient magnitudes are bounded. -/
abbrev DensePolynomial (K : Type*) :=
  Dense.Basic.DensePolynomial K
variable {K : Type*} [Field.ExplicitField K] [DecidableEq K]

/-- Every retained coefficient has magnitude at most the supplied natural bound.

The predicate uses the given field magnitude model on the original coefficient list, including any stored leading zeros.
-/
def PolynomialWithin (model : Magnitude.MagnitudeModel K)
    (polynomial : DensePolynomial K) (bound : Nat) : Prop :=
  Magnitude.ListWithin model polynomial.coeffs bound

/-- Enlarge a common magnitude bound for the retained polynomial coefficients. -/
theorem polynomialWithin_mono (model : Magnitude.MagnitudeModel K)
    {polynomial : DensePolynomial K} {left right : Nat}
    (bounded : PolynomialWithin model polynomial left)
    (order : left ≤ right) : PolynomialWithin model polynomial right :=
  Magnitude.listWithin_mono model bounded order

/-- Removing leading zeros preserves a common coefficient magnitude bound. -/
theorem normalize_within (model : Magnitude.MagnitudeModel K)
    {polynomial : DensePolynomial K} {bound : Nat}
    (bounded : PolynomialWithin model polynomial bound) :
    PolynomialWithin model polynomial.normalize bound :=
  Magnitude.listWithin_dropWhile model bounded _

/-- The empty dense zero display satisfies every coefficient magnitude bound. -/
theorem zero_within (model : Magnitude.MagnitudeModel K) (bound : Nat) :
    PolynomialWithin model (0 : DensePolynomial K) bound := by
  intro value member
  nomatch member

/-- A retained constant magnitude bounds its one-coefficient dense display. -/
theorem constant_within (model : Magnitude.MagnitudeModel K) {value : K} {bound
  : Nat}
    (bounded : model.magnitude value ≤ bound) :
    PolynomialWithin model (DensePolynomial.constant value) bound := by
  intro candidate member
  change candidate ∈ [value] at member
  cases member with
  | head => exact bounded
  | tail _ impossible => nomatch impossible

/-- Each retained Horner coefficient requires at most two magnitude-envelope updates.

The original accumulator and point bounds certify the multiplication and
addition at each fold step, while the tail keeps its original coefficient bounds. -/
private theorem evalFold_within (model : Magnitude.MagnitudeModel K) {point :
  K}
    (pointWithin : model.magnitude point ≤ bound) :
    ∀ (coefficients : List K) (accumulator : K),
      Magnitude.ListWithin model coefficients bound →
      model.magnitude accumulator ≤ bound →
      model.magnitude
          (coefficients.foldl (fun current coefficient =>
            current * point + coefficient) accumulator) ≤
        Magnitude.grow model bound (2 * coefficients.length)
  | [], _, _, accumulatorWithin => by
      exact accumulatorWithin
  | coefficient :: remaining, accumulator, coefficientsWithin,
      accumulatorWithin => by
      simp only [List.foldl_cons, List.length_cons]
      have productWithin := model.mul_le accumulatorWithin pointWithin
      have coefficientWithin :=
        (coefficientsWithin coefficient List.mem_cons_self).trans
          (model.expansive bound)
      have nextWithin := model.add_le productWithin
        coefficientWithin
      have remainingWithin : Magnitude.ListWithin model remaining bound :=
        fun value member => coefficientsWithin value
          (List.mem_cons_of_mem coefficient member)
      have recursive := evalFold_within model
        (pointWithin := pointWithin.trans
          (Magnitude.bound_le_grow model bound 2))
        remaining (accumulator * point + coefficient)
        (Magnitude.listWithin_mono model remainingWithin
          (Magnitude.bound_le_grow model bound 2)) nextWithin
      rw [Magnitude.grow_add] at recursive
      apply recursive.trans
      apply Magnitude.grow_mono_steps model bound
      have stepsEqual :
          2 + 2 * remaining.length = 2 * (remaining.length + 1) := by
        rw [Nat.mul_add, Nat.mul_one, Nat.add_comm]
      exact Nat.le_of_eq stepsEqual

/-- Every normalized Horner accumulator, and in particular its result, fits
the twice-per-coefficient operation envelope. -/
theorem eval_within (model : Magnitude.MagnitudeModel K)
    {polynomial : DensePolynomial K} {point : K} {bound : Nat}
    (zeroWithin : model.magnitude 0 ≤ bound)
    (pointWithin : model.magnitude point ≤ bound)
    (polynomialWithin : PolynomialWithin model polynomial bound) :
    model.magnitude (polynomial.eval point) ≤
      Magnitude.grow model bound (2 * polynomial.coeffs.length) := by
  exact evalFold_within model pointWithin polynomial.coeffs 0
    polynomialWithin zeroWithin

/-- Left zero padding preserves the original coefficient magnitude bound.

Each padded occurrence is either the retained zero scalar or an occurrence
from the original list, with its corresponding supplied magnitude certificate. -/
theorem padLeft_within (model : Magnitude.MagnitudeModel K) {values : List K}
    {bound : Nat} (zeroBound : model.magnitude 0 ≤ bound)
    (bounded : Magnitude.ListWithin model values bound) (padding : Nat) :
    Magnitude.ListWithin model (DensePolynomial.padLeft padding values) bound := by
  intro value member
  change value ∈ List.replicate padding 0 ++ values at member
  rcases List.Membership.mem_append.mp member with paddingMember | valueMember
  · rw [List.Membership.eq_of_mem_replicate paddingMember]
    exact zeroBound
  · exact bounded value valueMember

/-- Pairwise coefficient addition fits one update of the original magnitude envelope.

Each output occurrence retains the matching source occurrences. The original
addition certificate bounds their sum before structural recursion on the tails. -/
private theorem zipWith_add_within (model : Magnitude.MagnitudeModel K) :
    ∀ {left right : List K} {bound : Nat},
      Magnitude.ListWithin model left bound → Magnitude.ListWithin model right bound →
      Magnitude.ListWithin model (List.zipWith (· + ·) left right)
        (model.operationEnvelope bound)
  | [], _, _, _, _ => by
      intro value member
      nomatch member
  | _ :: _, [], _, _, _ => by
      intro value member
      nomatch member
  | left :: leftTail, right :: rightTail, bound, leftWithin, rightWithin => by
      intro value member
      change value ∈ (left + right) :: List.zipWith (· + ·) leftTail rightTail at member
      cases member with
      | head =>
          exact model.add_le
            (leftWithin left (List.Mem.head _))
            (rightWithin right (List.Mem.head _))
      | tail _ tail =>
          exact zipWith_add_within model
            (fun candidate candidateMember => leftWithin candidate
              (List.Mem.tail left candidateMember))
            (fun candidate candidateMember => rightWithin candidate
              (List.Mem.tail right candidateMember)) value tail

/-- Dense polynomial addition advances the shared coefficient magnitude envelope once, with zero bounded for padding.

The input polynomials share a coefficient magnitude bound, including the zero used
for padding. Every coefficient of their sum fits one application of the retained
operation envelope. -/
theorem add_within (model : Magnitude.MagnitudeModel K)
    {left right : DensePolynomial K} {bound : Nat}
    (zeroBound : model.magnitude 0 ≤ bound)
    (leftWithin : PolynomialWithin model left bound)
    (rightWithin : PolynomialWithin model right bound) :
    PolynomialWithin model (left + right) (Magnitude.grow model bound 1) := by
  unfold PolynomialWithin
  change Magnitude.ListWithin model (DensePolynomial.add left right).coeffs _
  unfold DensePolynomial.add
  apply Magnitude.listWithin_dropWhile
  apply zipWith_add_within model
  · exact padLeft_within model zeroBound leftWithin _
  · exact padLeft_within model zeroBound rightWithin _

/-- Coefficient negation fits one update of the retained magnitude envelope.

Each surviving mapped occurrence has an original coefficient witness. The
model's negation certificate bounds it before leading-zero normalization. -/
theorem neg_within (model : Magnitude.MagnitudeModel K)
    {polynomial : DensePolynomial K} {bound : Nat}
    (bounded : PolynomialWithin model polynomial bound) :
    PolynomialWithin model (-polynomial) (Magnitude.grow model bound 1) := by
  intro value member
  change value ∈ (polynomial.coeffs.map (fun scalar : K => -scalar)).dropWhile
    (fun scalar : K => decide (scalar = 0)) at member
  have rawMember := List.DropWhile.mem_of_mem (fun scalar : K => decide (scalar = 0)) member
  rcases List.Map.mem_map.mp rawMember with ⟨source, sourceMember, rfl⟩
  exact model.neg_le (bounded source sourceMember)

/-- Dense subtraction fits two advances of the shared coefficient magnitude envelope.

Both input coefficient lists share the supplied magnitude bound. Negation and
padded addition place every difference coefficient within two applications of the
retained operation envelope. -/
theorem sub_within (model : Magnitude.MagnitudeModel K)
    {left right : DensePolynomial K} {bound : Nat}
    (zeroBound : model.magnitude 0 ≤ bound)
    (leftWithin : PolynomialWithin model left bound)
    (rightWithin : PolynomialWithin model right bound) :
    PolynomialWithin model (left - right) (Magnitude.grow model bound 2) := by
  change PolynomialWithin model (left + -right) _
  have negated := neg_within model rightWithin
  have leftOne := polynomialWithin_mono model leftWithin
    (Magnitude.bound_le_grow model bound 1)
  have added := add_within model
    (zeroBound.trans (Magnitude.bound_le_grow model bound 1)) leftOne negated
  rw [Magnitude.grow_add] at added
  simpa using added

/-- A finite dense shift preserves the original coefficient magnitude bound.

The shift retains normalized source coefficients and appends the displayed
number of zeros. The supplied zero bound certifies each padding occurrence. -/
theorem shift_within (model : Magnitude.MagnitudeModel K)
    {polynomial : DensePolynomial K} {bound : Nat}
    (zeroBound : model.magnitude 0 ≤ bound)
    (bounded : PolynomialWithin model polynomial bound) (amount : Nat) :
    PolynomialWithin model (DensePolynomial.shift amount polynomial) bound := by
  rw [DensePolynomial.shift]
  split
  · exact zero_within model bound
  · intro value member
    rcases List.Membership.mem_append.mp member with source | padding
    · exact normalize_within model bounded value source
    · rw [List.Membership.eq_of_mem_replicate padding]
      exact zeroBound

/-- Dense coefficient scaling fits one update of the retained magnitude envelope.

Each surviving product has its original coefficient occurrence. The supplied
scalar bound and that coefficient bound certify the actual multiplication. -/
theorem scale_within (model : Magnitude.MagnitudeModel K)
    {scalar : K} {polynomial : DensePolynomial K} {bound : Nat}
    (scalarWithin : model.magnitude scalar ≤ bound)
    (bounded : PolynomialWithin model polynomial bound) :
    PolynomialWithin model (DensePolynomial.scale scalar polynomial) (Magnitude.grow model bound 1) := by
  intro value member
  unfold DensePolynomial.scale at member
  have rawMember := List.DropWhile.mem_of_mem (fun scalar : K => decide (scalar = 0)) member
  change value ∈ polynomial.coeffs.map (scalar * ·) at rawMember
  rcases List.Map.mem_map.mp rawMember with ⟨source, sourceMember, rfl⟩
  exact model.mul_le scalarWithin (bounded source sourceMember)

/-- Each multiplication-fold coefficient fits two retained magnitude-envelope updates.

The original right factor and accumulator bounds certify the retained shift,
scaling and addition operations. Recursive tails reuse those actual bounds. -/
private theorem mulFold_within (model : Magnitude.MagnitudeModel K)
    {right : DensePolynomial K} {source : List K}
    {accumulator : DensePolynomial K} {bound : Nat}
    (zeroBound : model.magnitude 0 ≤ bound)
    (sourceWithin : Magnitude.ListWithin model source bound)
    (rightWithin : PolynomialWithin model right bound)
    (accumulatorWithin : PolynomialWithin model accumulator bound) :
    PolynomialWithin model
      (source.foldl (fun value coefficient =>
        DensePolynomial.shift 1 value + DensePolynomial.scale coefficient right) accumulator)
      (Magnitude.grow model bound (2 * source.length)) := by
  induction source generalizing accumulator bound with
  | nil => exact accumulatorWithin
  | cons coefficient remaining inductionHypothesis =>
      simp only [List.foldl_cons, List.length_cons]
      have sourceHead := sourceWithin coefficient (List.mem_cons_self)
      have sourceTail : Magnitude.ListWithin model remaining bound := by
        intro value member
        exact sourceWithin value (List.mem_cons_of_mem coefficient member)
      let nextBound := Magnitude.grow model bound 2
      have boundLe : bound ≤ nextBound := Magnitude.bound_le_grow model bound 2
      have nextWithin : PolynomialWithin model
          (DensePolynomial.shift 1 accumulator + DensePolynomial.scale coefficient right) nextBound := by
        have shifted := shift_within model zeroBound accumulatorWithin 1
        have scaled := scale_within model sourceHead rightWithin
        have zeroNext : model.magnitude 0 ≤ Magnitude.grow model bound 1 :=
          zeroBound.trans (Magnitude.bound_le_grow model bound 1)
        exact add_within model zeroNext
          (polynomialWithin_mono model shifted (Magnitude.bound_le_grow model bound 1))
          scaled
      have recursive := inductionHypothesis
        (bound := nextBound)
        (zeroBound.trans boundLe)
        (Magnitude.listWithin_mono model sourceTail boundLe)
        (polynomialWithin_mono model rightWithin boundLe)
        nextWithin
      rw [Magnitude.grow_add] at recursive
      simpa only [List.length_cons, Nat.mul_add, Nat.mul_one,
        show 2 * (remaining.length + 1) = 2 + 2 * remaining.length by
          rw [Nat.mul_add, Nat.mul_one, Nat.add_comm],
        Nat.add_comm 2 (2 * remaining.length)] using recursive

/-- Dense multiplication fits two envelope advances per retained left coefficient.

The original left coefficient list determines the number of recursive products and
additions. The shared input magnitude bound is advanced twice for each retained
left entry. -/
theorem mul_within (model : Magnitude.MagnitudeModel K)
    {left right : DensePolynomial K} {bound : Nat}
    (zeroBound : model.magnitude 0 ≤ bound)
    (leftWithin : PolynomialWithin model left bound)
    (rightWithin : PolynomialWithin model right bound) :
    PolynomialWithin model (left * right)
      (Magnitude.grow model bound (2 * left.coeffs.length)) := by
  change PolynomialWithin model (DensePolynomial.mulPolynomial left right) _
  unfold DensePolynomial.mulPolynomial
  exact mulFold_within model zeroBound leftWithin rightWithin
    (zero_within model bound)

/-- A coefficient magnitude bound also bounds the leading coefficient when it bounds the zero default. -/
theorem leadingCoeff_le (model : Magnitude.MagnitudeModel K)
    {polynomial : DensePolynomial K} {bound : Nat}
    (zeroBound : model.magnitude 0 ≤ bound)
    (bounded : PolynomialWithin model polynomial bound) :
    model.magnitude polynomial.leadingCoeff ≤ bound := by
  unfold DensePolynomial.leadingCoeff
  cases coefficients : polynomial.normalize.coeffs with
  | nil => simpa only [coefficients, List.headD_nil] using zeroBound
  | cons head tail =>
      apply normalize_within model bounded head
      rw [coefficients]
      exact List.mem_cons_self

/-- The one-term division quotient fits one envelope advance of the shared input coefficient bound.

The original leading coefficients share the supplied magnitude bound. Their total
quotient and its zero padding fit one further operation envelope. -/
theorem leadQuotient_within (model : Magnitude.MagnitudeModel K)
    {left right : DensePolynomial K} {bound : Nat}
    (zeroBound : model.magnitude 0 ≤ bound)
    (leftWithin : PolynomialWithin model left bound)
    (rightWithin : PolynomialWithin model right bound) :
    PolynomialWithin model (DensePolynomial.leadQuotient left right) (Magnitude.grow model bound 1) := by
  unfold DensePolynomial.leadQuotient
  apply shift_within model
  · exact zeroBound.trans (Magnitude.bound_le_grow model bound 1)
  · apply constant_within
    exact model.div_le
      (leadingCoeff_le model zeroBound leftWithin)
      (leadingCoeff_le model zeroBound rightWithin)

/-- One leading cancellation fits four envelope advances of the shared input coefficient bound.

The bound accounts for the coefficient division, scalar multiplication and subtraction; shifting only pads with bounded
zeros. -/
theorem cancelLead_within (model : Magnitude.MagnitudeModel K)
    {left right : DensePolynomial K} {bound : Nat}
    (zeroBound : model.magnitude 0 ≤ bound)
    (leftWithin : PolynomialWithin model left bound)
    (rightWithin : PolynomialWithin model right bound) :
    PolynomialWithin model (DensePolynomial.cancelLead left right) (Magnitude.grow model bound 4) := by
  unfold DensePolynomial.cancelLead
  have quotient : model.magnitude (left.leadingCoeff / right.leadingCoeff) ≤
      Magnitude.grow model bound 1 :=
    model.div_le (leadingCoeff_le model zeroBound leftWithin)
      (leadingCoeff_le model zeroBound rightWithin)
  have rightOne := polynomialWithin_mono model rightWithin
    (Magnitude.bound_le_grow model bound 1)
  have scaled := scale_within model quotient rightOne
  rw [Magnitude.grow_add] at scaled
  have shifted := shift_within model
    (zeroBound.trans (Magnitude.bound_le_grow model bound 2)) scaled
    (left.natDegree - right.natDegree)
  have leftTwo := polynomialWithin_mono model leftWithin
    (Magnitude.bound_le_grow model bound 2)
  have difference := sub_within model
    (zeroBound.trans (Magnitude.bound_le_grow model bound 2)) leftTwo shifted
  rw [Magnitude.grow_add] at difference
  simpa using difference

/-- Both polynomials returned by a fuel-bounded normalized long division fit
the same source-only envelope.

The original divisor, current dividend and accumulated quotient share the input
bound. Every retained fuel step advances the operation envelope and bounds both
returned coefficient lists. -/
theorem divLoop_within (model : Magnitude.MagnitudeModel K)
    (fuel : Nat) {left right quotient : DensePolynomial K} {bound : Nat}
    (zeroBound : model.magnitude 0 ≤ bound)
    (leftWithin : PolynomialWithin model left bound)
    (rightWithin : PolynomialWithin model right bound)
    (quotientWithin : PolynomialWithin model quotient bound) :
    PolynomialWithin model (DensePolynomial.divLoop fuel left right quotient).quotient
        (Magnitude.grow model bound (4 * fuel)) ∧
      PolynomialWithin model (DensePolynomial.divLoop fuel left right quotient).remainder
        (Magnitude.grow model bound (4 * fuel)) := by
  induction fuel generalizing left quotient bound with
  | zero => exact ⟨quotientWithin, leftWithin⟩
  | succ fuel inductionHypothesis =>
      rw [DensePolynomial.divLoop_succ]
      split
      · exact ⟨polynomialWithin_mono model quotientWithin
            (Magnitude.bound_le_grow model bound (4 * (fuel + 1))),
          polynomialWithin_mono model leftWithin
            (Magnitude.bound_le_grow model bound (4 * (fuel + 1)))⟩
      · dsimp only
        let nextBound := Magnitude.grow model bound 4
        have boundLe : bound ≤ nextBound := Magnitude.bound_le_grow model bound 4
        have nextLeft := cancelLead_within model zeroBound leftWithin rightWithin
        have term := leadQuotient_within model zeroBound leftWithin rightWithin
        have nextQuotient : PolynomialWithin model
            (quotient + DensePolynomial.leadQuotient left right) nextBound := by
          have quotientTwo := polynomialWithin_mono model quotientWithin
            (Magnitude.bound_le_grow model bound 2)
          have termTwo := polynomialWithin_mono model term
            (Magnitude.grow_mono_steps model bound (by decide : 1 ≤ 2))
          have added := add_within model
            (zeroBound.trans (Magnitude.bound_le_grow model bound 2))
            quotientTwo termTwo
          rw [Magnitude.grow_add] at added
          exact polynomialWithin_mono model added
            (Magnitude.grow_mono_steps model bound (by decide : 3 ≤ 4))
        have recursive := inductionHypothesis
          (bound := nextBound)
          (zeroBound.trans boundLe) nextLeft
          (polynomialWithin_mono model rightWithin boundLe) nextQuotient
        rw [Magnitude.grow_add] at recursive
        simpa only [Nat.mul_add, Nat.mul_one,
          show 4 * (fuel + 1) = 4 + 4 * fuel by
            rw [Nat.mul_add, Nat.mul_one, Nat.add_comm],
          Nat.add_comm 4 (4 * fuel)] using recursive

/-- Bound every returned long-division coefficient by the finite cancellation envelope.

The original dividend degree count supplies the finite fuel. Four operation-
envelope advances per cancellation round bound every coefficient of both returned
polynomials. -/
theorem divMod_within (model : Magnitude.MagnitudeModel K)
    {left right : DensePolynomial K} {bound : Nat}
    (zeroBound : model.magnitude 0 ≤ bound)
    (leftWithin : PolynomialWithin model left bound)
    (rightWithin : PolynomialWithin model right bound) :
    PolynomialWithin model (DensePolynomial.divMod left right).quotient
        (Magnitude.grow model bound (4 * (left.degreeCount + 1))) ∧
      PolynomialWithin model (DensePolynomial.divMod left right).remainder
        (Magnitude.grow model bound (4 * (left.degreeCount + 1))) := by
  unfold DensePolynomial.divMod
  exact divLoop_within model _ zeroBound
    (normalize_within model leftWithin)
    (normalize_within model rightWithin) (zero_within model bound)
end Purelib.Polynomial.Dense.Resource

end
