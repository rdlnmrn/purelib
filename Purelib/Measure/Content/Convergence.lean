module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Measure.Content.Lp.L1
import Purelib.Measure.Content.Operations
import Purelib.Measure.Weighted.Basic
import Purelib.Data.Rat.Fraction

public import Purelib.Data.List.Rat.Order
import Purelib.Data.Rat.Distance.Basic
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order
public import Purelib.Data.Rat.PointwiseMinimum
import Purelib.Measure.Content.Basic
import Purelib.Measure.Content.Integral
import Purelib.Measure.Content.Stability
public import Purelib.Measure.Weighted.Order
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Order.Basic

section
@[expose] public section

/-!
# Finite convergence certificates

The usual monotone, Fatou, and dominated convergence theorems concern
completed limits.  This module retains their executable finite content:
displayed monotone chains have monotone rational integrals, displayed lower
envelopes satisfy the finite Fatou inequality, and an integrable rational
error envelope gives an explicit accuracy certificate.

No sequence, limit, supremum, extended value, or completed function space is
formed.
-/

namespace Purelib.Measure
namespace Content

open Purelib in
open Purelib.Data.Rat in
/-- Integrating a finite pointwise monotone observable chain gives a monotone rational coordinate chain. -/
theorem integral_monotoneChain {α : Type} (content : Content α) :
    ∀ observables : List (α → Fraction.Rational),
      PointwiseMonotoneChainOn content.atoms observables →
        Data.Rat.MonotoneCoordinateChain (observables.map content.integral)
  | [], monotone => monotone
  | [_], monotone => monotone
  | first :: second :: remaining, monotone => by
      exact ⟨content.integral_mono first second monotone.1,
        content.integral_monotoneChain (second :: remaining) monotone.2⟩

end Content
namespace Content

open Purelib in
open Purelib.Data.Rat in
/-- The integral of the finite pointwise minimum is bounded by the integral of each observable in the original nonempty
list. -/
theorem integral_pointwiseMinimum_le_of_mem {α : Type}
    (content : Content α) (first : α → Fraction.Rational)
    (remaining : List (α → Fraction.Rational)) {candidate : α → Fraction.Rational}
    (member : candidate ∈ first :: remaining) :
    content.integral (Data.Rat.pointwiseMinimum first remaining) ≤
      content.integral candidate := by
  apply content.integral_mono
  intro atom atomMember
  exact Data.Rat.pointwiseMinimum_le_of_mem first remaining member atom.item

end Content

open Purelib.Data.Rat in
/-- Require an envelope to bound the rational separation of two observables at every retained atom payload. -/
def DominatesErrorOn {α : Type} (atoms : List (Weighted α))
    (envelope left right : α → Fraction.Rational) : Prop :=
  ∀ atom, atom ∈ atoms →
    Distance.rationalSeparation (left atom.item) (right atom.item) ≤
      envelope atom.item

namespace Content

section
open Purelib.Data.Rat
/-- A pointwise error envelope bounds integrated separation by its integral over the same content. -/
theorem l1Distance_le_integral_of_dominator {α : Type}
    (content : Content α) (envelope left right : α → Fraction.Rational)
    (dominates : DominatesErrorOn content.atoms envelope left right) :
    content.l1Distance left right ≤ content.integral envelope := by
  apply content.integral_mono
  intro atom member
  exact dominates atom member

/-- The integral of a pointwise error envelope bounds the separation of the two observable integrals. -/
theorem integral_separation_le_of_dominator {α : Type}
    (content : Content α) (envelope left right : α → Fraction.Rational)
    (dominates : DominatesErrorOn content.atoms envelope left right) :
    Distance.rationalSeparation (content.integral left) (content.integral right) ≤
      content.integral envelope := by
  have l1Bound := content.l1Distance_le_integral_of_dominator
    envelope left right dominates
  have integralBound := content.integral_close_l1 left right
  unfold Distance.rationalSeparation
  apply Fraction.Order.Basic.max_le
  · exact integralBound.2.trans l1Bound
  · exact integralBound.1.trans l1Bound

/-- An envelope integral below a tolerance makes the two observable integrals strictly that close. -/
theorem integral_separation_lt_of_dominator {α : Type}
    (content : Content α) (envelope left right : α → Fraction.Rational)
    (dominates : DominatesErrorOn content.atoms envelope left right)
    (epsilon : Fraction.Rational)
    (small : content.integral envelope < epsilon) :
    Distance.rationalSeparation (content.integral left) (content.integral right) <
      epsilon :=
  (content.integral_separation_le_of_dominator
    envelope left right dominates).trans_lt small

end

set_option genInjectivity false in
open Purelib.Data.Rat in
/-- Retain a nonnegative pointwise error envelope for the exact candidate and target observables over their original
content.

The domination proof is tied to the same retained atom list and envelope whose integral determines the numerical error
budget. -/
structure IntegralErrorBudget {α : Type} (content : Content α)
    (candidate target : α → Fraction.Rational) where
  /-- The exact retained pointwise envelope for candidate-target separation. -/ envelope : α → Fraction.Rational
  /-- The retained envelope is nonnegative at every original content occurrence. -/ envelope_nonnegative : ∀ atom, atom
    ∈ content.atoms →
    0 ≤ envelope atom.item
  /-- The retained envelope bounds separation of the exact candidate and target on all original occurrences. -/
    dominates : DominatesErrorOn content.atoms envelope candidate target

constructive_injectivity IntegralErrorBudget

namespace IntegralErrorBudget

open Purelib.Data.Rat
/-- Integrate the exact retained error envelope over its original content. -/
def error {α : Type} {content : Content α}
    {candidate target : α → Fraction.Rational}
    (budget : IntegralErrorBudget content candidate target) : Fraction.Rational :=
  content.integral budget.envelope

/-- The retained envelope's integrated error budget is nonnegative. -/
theorem error_nonnegative {α : Type} {content : Content α}
    {candidate target : α → Fraction.Rational}
    (budget : IntegralErrorBudget content candidate target) :
    0 ≤ budget.error :=
  content.integral_nonneg budget.envelope budget.envelope_nonnegative

/-- The retained budget bounds the separation of its exact candidate and target integrals. -/
theorem integral_separation_le {α : Type} {content : Content α}
    {candidate target : α → Fraction.Rational}
    (budget : IntegralErrorBudget content candidate target) :
    Distance.rationalSeparation (content.integral candidate)
        (content.integral target) ≤ budget.error :=
  content.integral_separation_le_of_dominator
    budget.envelope candidate target budget.dominates

/-- A retained integrated budget below the requested tolerance gives that strict accuracy for the original observable
integrals. -/
theorem accurate {α : Type} {content : Content α}
    {candidate target : α → Fraction.Rational}
    (budget : IntegralErrorBudget content candidate target)
    (epsilon : Fraction.Rational) (small : budget.error < epsilon) :
    Distance.rationalSeparation (content.integral candidate)
        (content.integral target) < epsilon :=
  budget.integral_separation_le.trans_lt small

end IntegralErrorBudget

set_option genInjectivity false in
open Purelib.Data.Rat in
/-- Retain an approximation below its target with a nonnegative pointwise remainder bounding their exact gap.

All comparisons use the same original content occurrences. Integrating the retained remainder certifies the one-sided
gap and rational separation. -/
structure MonotoneIntegralBudget {α : Type} (content : Content α)
    (approximation target : α → Fraction.Rational) where
  /-- The exact retained pointwise bound for the target-minus-approximation gap. -/ remainder : α → Fraction.Rational
  /-- The retained remainder is nonnegative at each original content occurrence. -/ remainder_nonnegative : ∀ atom, atom
    ∈ content.atoms →
    0 ≤ remainder atom.item
  /-- The retained approximation lies below its target on every original content occurrence. -/ approximation_le :
    PointwiseLeOn content.atoms approximation target
  /-- The exact target-minus-approximation gap is bounded by the same retained remainder. -/ gap_le_remainder : ∀ atom,
    atom ∈ content.atoms →
    target atom.item - approximation atom.item ≤ remainder atom.item

constructive_injectivity MonotoneIntegralBudget

namespace MonotoneIntegralBudget

open Purelib.Data.Rat
/-- The retained pointwise lower approximation integrates below its exact target. -/
theorem integral_mono {α : Type} {content : Content α}
    {approximation target : α → Fraction.Rational}
    (budget : MonotoneIntegralBudget content approximation target) :
    content.integral approximation ≤ content.integral target :=
  content.integral_mono approximation target budget.approximation_le

/-- The integral of the retained nonnegative remainder is nonnegative. -/
theorem remainderIntegral_nonnegative {α : Type}
    {content : Content α} {approximation target : α → Fraction.Rational}
    (budget : MonotoneIntegralBudget content approximation target) :
    0 ≤ content.integral budget.remainder :=
  content.integral_nonneg budget.remainder budget.remainder_nonnegative

/-- The exact target integral minus its lower approximation is bounded by the integral of the retained remainder. -/
theorem integral_gap_le {α : Type} {content : Content α}
    {approximation target : α → Fraction.Rational}
    (budget : MonotoneIntegralBudget content approximation target) :
    content.integral target - content.integral approximation ≤
      content.integral budget.remainder := by
  have averaged := content.integral_mono
    (fun item => target item - approximation item) budget.remainder
    budget.gap_le_remainder
  rw [content.integral_sub] at averaged
  exact averaged

/-- The integral of the retained remainder bounds the separation of the exact lower-approximation and target integrals.
-/
theorem integral_separation_le {α : Type} {content : Content α}
    {approximation target : α → Fraction.Rational}
    (budget : MonotoneIntegralBudget content approximation target) :
    Distance.rationalSeparation (content.integral approximation)
        (content.integral target) ≤ content.integral budget.remainder := by
  unfold Distance.rationalSeparation
  apply Fraction.Order.Basic.max_le
  · exact (Fraction.Order.Boundary.sub_nonpositive_iff.mpr budget.integral_mono).trans
      budget.remainderIntegral_nonnegative
  · exact budget.integral_gap_le

/-- A retained integrated budget below the requested tolerance gives that strict accuracy for the original observable
integrals. -/
theorem accurate {α : Type} {content : Content α}
    {approximation target : α → Fraction.Rational}
    (budget : MonotoneIntegralBudget content approximation target)
    (epsilon : Fraction.Rational)
    (small : content.integral budget.remainder < epsilon) :
    Distance.rationalSeparation (content.integral approximation)
        (content.integral target) < epsilon :=
  budget.integral_separation_le.trans_lt small

end MonotoneIntegralBudget

end Content

end Purelib.Measure

end
