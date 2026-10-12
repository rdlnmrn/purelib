module

import Purelib.Data.List.DropWhile.Basic
public import Purelib.Algebra.Field.ExplicitField
-- Public field certificates retain the direct negation parent.
public import Purelib.Algebra.Group.Negation

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Order.Basic
public import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Order.RelClasses
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Algebra.Field

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

namespace Purelib.Algebra.Field.Resource.Magnitude

set_option genInjectivity false in
/-- The finite facts needed to account for one normalized field operation.

The retained magnitude and one-operation envelope bound every actual field
operation on the original inputs. Their scalar operations use the retained
field parent, including its original subtraction and negation. -/
structure MagnitudeModel (K : Type*) [ExplicitField K] [DecidableEq K]
  where
  /-- Assign a natural magnitude to each scalar. -/ magnitude : K → Nat
  /-- Enlarge a common input bound to an operation-result bound. -/ operationEnvelope : Nat → Nat
  /-- Each envelope value is at least its input bound. -/ expansive : ∀ bound, bound ≤ operationEnvelope bound
  /-- The envelope preserves inequalities between bounds. -/ monotone : ∀ {left right}, left ≤ right →
    operationEnvelope left ≤ operationEnvelope right
  /-- Addition of two bounded inputs fits within the operation envelope. -/ add_le : ∀ {left right bound}, magnitude
    left ≤ bound →
    magnitude right ≤ bound → magnitude (left + right) ≤ operationEnvelope bound
  /-- Negation of a bounded input fits within the operation envelope. -/ neg_le : ∀ {source bound}, magnitude source ≤
    bound →
    magnitude (-source) ≤ operationEnvelope bound
  /-- Subtraction of two bounded inputs fits within the operation envelope. -/ sub_le : ∀ {left right bound}, magnitude
    left ≤ bound →
    magnitude right ≤ bound → magnitude (left - right) ≤ operationEnvelope bound
  /-- Multiplication of two bounded inputs fits within the operation envelope. -/ mul_le : ∀ {left right bound},
    magnitude left ≤ bound →
    magnitude right ≤ bound → magnitude (left * right) ≤ operationEnvelope bound
  /-- Total inversion of a bounded input fits within the operation envelope. -/ inv_le : ∀ {source bound}, magnitude
    source ≤ bound →
    magnitude source⁻¹ ≤ operationEnvelope bound
  /-- Division of two bounded inputs fits within the operation envelope. -/ div_le : ∀ {left right bound}, magnitude
    left ≤ bound →
    magnitude right ≤ bound → magnitude (left / right) ≤ operationEnvelope bound

constructive_injectivity MagnitudeModel

variable {K : Type*} [ExplicitField K] [DecidableEq K]

open Purelib.Algebra.Field.Resource.Magnitude
open Purelib.Algebra.Field.Resource
open Purelib.Data.List

/-- Iterate the retained operation envelope for the requested number of steps.

Zero steps preserve the supplied starting bound; each successor applies one further envelope. -/
def grow (model : MagnitudeModel K) : Nat → Nat → Nat
  | bound, 0 => bound
  | bound, steps + 1 => model.operationEnvelope (grow model bound steps)

section
open Purelib.Algebra.Field.Resource.Magnitude
open Purelib.Algebra.Field.Resource
/-- Zero growth steps leave the initial magnitude bound unchanged. -/
@[simp] theorem grow_zero (model : MagnitudeModel K) (bound : Nat) :
    grow model bound 0 = bound := rfl

/-- A successor growth step applies the envelope to the previous bound. -/
@[simp] theorem grow_succ (model : MagnitudeModel K) (bound steps : Nat)
  :
    grow model bound (steps + 1) =
      model.operationEnvelope (grow model bound steps) := rfl

/-- Iterating the expansive envelope never decreases the starting bound. -/
theorem bound_le_grow (model : MagnitudeModel K) (bound steps : Nat) :
    bound ≤ grow model bound steps := by
  induction steps with
  | zero => exact le_refl _
  | succ steps inductionHypothesis =>
      exact inductionHypothesis.trans (model.expansive _)

/-- Envelope iteration preserves an inequality between starting bounds.

The two iterations use the same model and number of steps. -/
theorem grow_mono_bound (model : MagnitudeModel K) {left right : Nat}
    (order : left ≤ right) (steps : Nat) :
    grow model left steps ≤ grow model right steps := by
  induction steps with
  | zero => exact order
  | succ steps inductionHypothesis =>
      exact model.monotone inductionHypothesis

end

/-- Increasing the operation count cannot decrease the iterated envelope.

The retained model's expansive certificate bounds every additional update
starting from the same original magnitude. -/
theorem grow_mono_steps (model : MagnitudeModel K) (bound : Nat)
    {first second : Nat} (order : first ≤ second) :
    grow model bound first ≤ grow model bound second := by
  obtain ⟨extra, equation⟩ := Nat.le.dest order
  subst second
  clear order
  induction extra with
  | zero =>
      rw [Nat.add_zero]
  | succ extra inductionHypothesis =>
      exact inductionHypothesis.trans (model.expansive _)

/-- Iterating two operation counts in succession equals iterating their sum.

Both iterations use the same retained model and initial bound. The second
iteration begins at the first iteration's actual envelope reading. -/
theorem grow_add (model : MagnitudeModel K) (bound first second : Nat) :
    grow model (grow model bound first) second =
      grow model bound (first + second) := by
  induction second with
  | zero =>
      rw [Nat.add_zero]
      rfl
  | succ second inductionHypothesis =>
      rw [grow_succ, inductionHypothesis, Nat.add_succ, grow_succ]

open Purelib.Algebra.Field.Resource.Magnitude in
/-- Every scalar occurring in a finite list satisfies the supplied magnitude bound. -/
def ListWithin (model : MagnitudeModel K) (values : List K)
    (bound : Nat) : Prop :=
  ∀ value ∈ values, model.magnitude value ≤ bound

open Purelib.Algebra.Field.Resource in
open Purelib.Algebra.Field.Resource.Magnitude in
/-- Increasing a magnitude bound preserves boundedness of every list entry. -/
theorem listWithin_mono (model : MagnitudeModel K) {values : List K}
    {left right : Nat} (bounded : ListWithin model values left)
    (order : left ≤ right) : ListWithin model values right := by
  intro value member
  exact (bounded value member).trans order

/-- Dropping a finite leading prefix preserves a list's magnitude bound.

Each retained member belonged to the original coefficient list, so its actual
model magnitude retains the original common bound. -/
theorem listWithin_dropWhile (model : MagnitudeModel K) {values : List
  K}
    {bound : Nat} (bounded : ListWithin model values bound)
    (predicate : K → Bool) :
    ListWithin model (values.dropWhile predicate) bound := by
  intro value member
  exact bounded value (DropWhile.mem_of_mem predicate member)
end Purelib.Algebra.Field.Resource.Magnitude

end
