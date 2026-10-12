module

public import Purelib.Data.Nat.BitWidth
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Basic
public import Purelib.Data.Rat.Fraction.Resource.Components

import Purelib.Tactic.Ring

section
@[expose] public section

/-!
# Explicit arithmetic envelopes for RFAP-II

This module bounds the finite post-processing performed in the second RFAP
paper.  It covers the square-threshold request, displayed grid record,
homogeneous Gaussian-integer evaluation, and finite Hurwitz recursion.  The
eliminant, Sturm, and repeated-subdivision costs used to produce the imported
RFAP-I Newton state are deliberately outside this module.
-/

namespace Purelib.Data.Rat.Fraction.Resource.Width

open Purelib.Data.Nat in
open Purelib.Data.Rat in
/-- Compute the natural bit width of the coordinate addition envelope for two canonical rational representatives.

Read the two exact reduced representatives and form their cross-numerator and denominator-product envelope. The natural
width of that envelope bounds the normalized result without recomputing its arithmetic result. -/
def normalizedAddBitBudget (left right : Fraction.Rational) : Nat :=
  BitWidth.natWidth (Fraction.Resource.Components.NormalizedFraction.addComponentEnvelope
    (Fraction.Basic.ofRational left)
    (Fraction.Basic.ofRational right))
end Purelib.Data.Rat.Fraction.Resource.Width

end

section
@[expose] public section

/-!
# Explicit arithmetic envelopes for RFAP-II

This module bounds the finite post-processing performed in the second RFAP
paper.  It covers the square-threshold request, displayed grid record,
homogeneous Gaussian-integer evaluation, and finite Hurwitz recursion.  The
eliminant, Sturm, and repeated-subdivision costs used to produce the imported
RFAP-I Newton state are deliberately outside this module.
-/

namespace Purelib.Data.Rat.Fraction.Resource.Width

open Purelib.Data.Nat in
open Purelib.Data.Rat in
/-- Compute the bit width of the multiplicative magnitude envelope for the two rational representatives.

The total reciprocal does not increase component magnitude, including at zero. Therefore the multiplicative magnitude
envelope bounds the normalized quotient with no nonzero-denominator precondition. -/
def normalizedDivBitBudget (left right : Fraction.Rational) : Nat :=
  BitWidth.natWidth (Fraction.Resource.Components.multiplicativeMagnitudeEnvelope
    (Fraction.Resource.Components.NormalizedFraction.componentMagnitude
      (Fraction.Basic.ofRational left))
    (Fraction.Resource.Components.NormalizedFraction.componentMagnitude
      (Fraction.Basic.ofRational right)))
end Purelib.Data.Rat.Fraction.Resource.Width

end

section
@[expose] public section

/-!
# Explicit arithmetic envelopes for RFAP-II

This module bounds the finite post-processing performed in the second RFAP
paper.  It covers the square-threshold request, displayed grid record,
homogeneous Gaussian-integer evaluation, and finite Hurwitz recursion.  The
eliminant, Sturm, and repeated-subdivision costs used to produce the imported
RFAP-I Newton state are deliberately outside this module.
-/

namespace Purelib.Data.Rat.Fraction.Resource.Width

open Purelib.Data.Nat in
open Purelib.Data.Rat in
/-- Compute the natural bit width of the coordinate multiplication envelope for two canonical rational representatives.

Read the two exact reduced representatives and form their numerator-product and denominator-product envelope. Its
natural width bounds the normalized product even when cross-cancellation reduces the components further. -/
def normalizedMulBitBudget (left right : Fraction.Rational) : Nat :=
  BitWidth.natWidth (Fraction.Resource.Components.NormalizedFraction.mulComponentEnvelope
    (Fraction.Basic.ofRational left)
    (Fraction.Basic.ofRational right))
end Purelib.Data.Rat.Fraction.Resource.Width

end

section
@[expose] public section

/-!
# Explicit arithmetic envelopes for RFAP-II

This module bounds the finite post-processing performed in the second RFAP
paper.  It covers the square-threshold request, displayed grid record,
homogeneous Gaussian-integer evaluation, and finite Hurwitz recursion.  The
eliminant, Sturm, and repeated-subdivision costs used to produce the imported
RFAP-I Newton state are deliberately outside this module.
-/

namespace Purelib.Data.Rat.Fraction.Resource.Width

open Purelib.Data.Nat in
open Purelib.Data.Rat in
/-- Compute the bit width of the additive magnitude envelope for the two rational representatives.

The magnitude envelope uses twice the product of the input component magnitudes. Canonical negation preserves magnitude,
so the same bound used for addition controls subtraction. -/
def normalizedSubBitBudget (left right : Fraction.Rational) : Nat :=
  BitWidth.natWidth (Fraction.Resource.Components.additiveMagnitudeEnvelope
    (Fraction.Resource.Components.NormalizedFraction.componentMagnitude
      (Fraction.Basic.ofRational left))
    (Fraction.Resource.Components.NormalizedFraction.componentMagnitude
      (Fraction.Basic.ofRational right)))
end Purelib.Data.Rat.Fraction.Resource.Width

end

section
@[expose] public section

/-!
# Explicit arithmetic envelopes for RFAP-II

This module bounds the finite post-processing performed in the second RFAP
paper.  It covers the square-threshold request, displayed grid record,
homogeneous Gaussian-integer evaluation, and finite Hurwitz recursion.  The
eliminant, Sturm, and repeated-subdivision costs used to produce the imported
RFAP-I Newton state are deliberately outside this module.
-/

namespace Purelib.Data.Rat.Fraction.Resource.Width

/-! ## Normalized rational work records -/

open Purelib.Data.Nat in
open Purelib.Data.Rat in
/-- Measure a reduced fraction by the natural bit width of its component magnitude. -/
def reducedFractionWidth (value : Fraction.Basic.ReducedFraction) : Nat
  :=
  BitWidth.natWidth (Fraction.Resource.Components.NormalizedFraction.componentMagnitude value)
end Purelib.Data.Rat.Fraction.Resource.Width

end

section
@[expose] public section

/-!
# Explicit arithmetic envelopes for RFAP-II

This module bounds the finite post-processing performed in the second RFAP
paper.  It covers the square-threshold request, displayed grid record,
homogeneous Gaussian-integer evaluation, and finite Hurwitz recursion.  The
eliminant, Sturm, and repeated-subdivision costs used to produce the imported
RFAP-I Newton state are deliberately outside this module.
-/

namespace Purelib.Data.Rat.Fraction.Resource.Width

open Purelib.Data.Rat in
/-- Measure a canonical rational by the width of its retained reduced representative. -/
def rationalRecordWidth (value : Fraction.Rational) : Nat :=
  reducedFractionWidth (Fraction.Basic.ofRational value)
end Purelib.Data.Rat.Fraction.Resource.Width

end

section
@[expose] public section

/-!
# Explicit arithmetic envelopes for RFAP-II

This module bounds the finite post-processing performed in the second RFAP
paper.  It covers the square-threshold request, displayed grid record,
homogeneous Gaussian-integer evaluation, and finite Hurwitz recursion.  The
eliminant, Sturm, and repeated-subdivision costs used to produce the imported
RFAP-I Newton state are deliberately outside this module.
-/

namespace Purelib.Data.Rat.Fraction.Resource.Width

open Purelib.Data.Nat in
open Purelib.Data.Rat in
/-- The width of the normalized sum is bounded by its computed bit budget. -/
theorem normalizedAdd_width_le_budget (left right : Fraction.Rational) :
    rationalRecordWidth
        (Fraction.Arithmetic.normalizedAdd left right) ≤
      normalizedAddBitBudget left right := by
  unfold rationalRecordWidth reducedFractionWidth
    normalizedAddBitBudget
  rw [Fraction.Arithmetic.ofRational_normalizedAdd]
  exact BitWidth.natWidth_mono
    (Fraction.Resource.Components.add_componentMagnitude_le _ _)
end Purelib.Data.Rat.Fraction.Resource.Width

end

section
@[expose] public section

/-!
# Explicit arithmetic envelopes for RFAP-II

This module bounds the finite post-processing performed in the second RFAP
paper.  It covers the square-threshold request, displayed grid record,
homogeneous Gaussian-integer evaluation, and finite Hurwitz recursion.  The
eliminant, Sturm, and repeated-subdivision costs used to produce the imported
RFAP-I Newton state are deliberately outside this module.
-/

namespace Purelib.Data.Rat.Fraction.Resource.Width

open Purelib.Data.Nat in
open Purelib.Data.Rat in
/-- The width of the normalized quotient is bounded by its computed bit budget. -/
theorem normalizedDiv_width_le_budget (left right : Fraction.Rational) :
    rationalRecordWidth
        (Fraction.Arithmetic.normalizedDiv left right) ≤
      normalizedDivBitBudget left right := by
  unfold rationalRecordWidth reducedFractionWidth
    normalizedDivBitBudget
  rw [Fraction.Arithmetic.ofRational_normalizedDiv]
  exact BitWidth.natWidth_mono
    (Fraction.Resource.Components.componentMagnitude_div_le _ _)
end Purelib.Data.Rat.Fraction.Resource.Width

end

section
@[expose] public section

/-!
# Explicit arithmetic envelopes for RFAP-II

This module bounds the finite post-processing performed in the second RFAP
paper.  It covers the square-threshold request, displayed grid record,
homogeneous Gaussian-integer evaluation, and finite Hurwitz recursion.  The
eliminant, Sturm, and repeated-subdivision costs used to produce the imported
RFAP-I Newton state are deliberately outside this module.
-/

namespace Purelib.Data.Rat.Fraction.Resource.Width

open Purelib.Data.Rat in
/-- Use the original rational record width as the budget for its total reciprocal. -/
def normalizedInvBitBudget (source : Fraction.Rational) : Nat :=
  rationalRecordWidth source
end Purelib.Data.Rat.Fraction.Resource.Width

end

section
@[expose] public section

/-!
# Explicit arithmetic envelopes for RFAP-II

This module bounds the finite post-processing performed in the second RFAP
paper.  It covers the square-threshold request, displayed grid record,
homogeneous Gaussian-integer evaluation, and finite Hurwitz recursion.  The
eliminant, Sturm, and repeated-subdivision costs used to produce the imported
RFAP-I Newton state are deliberately outside this module.
-/

namespace Purelib.Data.Rat.Fraction.Resource.Width

open Purelib.Data.Nat in
open Purelib.Data.Rat in
/-- The width of the normalized reciprocal is bounded by its computed bit budget. -/
theorem normalizedInv_width_le_budget (source : Fraction.Rational) :
    rationalRecordWidth
        (Fraction.Arithmetic.normalizedInv source) ≤
      normalizedInvBitBudget source := by
  unfold rationalRecordWidth reducedFractionWidth
    normalizedInvBitBudget
  rw [Fraction.Arithmetic.ofRational_normalizedInv]
  exact BitWidth.natWidth_mono
    (Fraction.Resource.Components.NormalizedFraction.componentMagnitude_inv_le _)
end Purelib.Data.Rat.Fraction.Resource.Width

end

section
@[expose] public section

/-!
# Explicit arithmetic envelopes for RFAP-II

This module bounds the finite post-processing performed in the second RFAP
paper.  It covers the square-threshold request, displayed grid record,
homogeneous Gaussian-integer evaluation, and finite Hurwitz recursion.  The
eliminant, Sturm, and repeated-subdivision costs used to produce the imported
RFAP-I Newton state are deliberately outside this module.
-/

namespace Purelib.Data.Rat.Fraction.Resource.Width

open Purelib.Data.Nat in
open Purelib.Data.Rat in
/-- The width of the normalized product is bounded by its computed bit budget. -/
theorem normalizedMul_width_le_budget (left right : Fraction.Rational) :
    rationalRecordWidth
        (Fraction.Arithmetic.normalizedMul left right) ≤
      normalizedMulBitBudget left right := by
  unfold rationalRecordWidth reducedFractionWidth
    normalizedMulBitBudget
  rw [Fraction.Arithmetic.ofRational_normalizedMul]
  exact BitWidth.natWidth_mono
    (Fraction.Resource.Components.mul_componentMagnitude_le _ _)
end Purelib.Data.Rat.Fraction.Resource.Width

end

section
@[expose] public section

/-!
# Explicit arithmetic envelopes for RFAP-II

This module bounds the finite post-processing performed in the second RFAP
paper.  It covers the square-threshold request, displayed grid record,
homogeneous Gaussian-integer evaluation, and finite Hurwitz recursion.  The
eliminant, Sturm, and repeated-subdivision costs used to produce the imported
RFAP-I Newton state are deliberately outside this module.
-/

namespace Purelib.Data.Rat.Fraction.Resource.Width

open Purelib.Data.Rat in
/-- Use the original rational record width as the budget for its negation. -/
def normalizedNegBitBudget (source : Fraction.Rational) : Nat :=
  rationalRecordWidth source
end Purelib.Data.Rat.Fraction.Resource.Width

end

section
@[expose] public section

/-!
# Explicit arithmetic envelopes for RFAP-II

This module bounds the finite post-processing performed in the second RFAP
paper.  It covers the square-threshold request, displayed grid record,
homogeneous Gaussian-integer evaluation, and finite Hurwitz recursion.  The
eliminant, Sturm, and repeated-subdivision costs used to produce the imported
RFAP-I Newton state are deliberately outside this module.
-/

namespace Purelib.Data.Rat.Fraction.Resource.Width

open Purelib.Data.Nat in
open Purelib.Data.Rat in
/-- The width of the normalized negation is bounded by its computed bit budget. -/
theorem normalizedNeg_width_le_budget (source : Fraction.Rational) :
    rationalRecordWidth
        (Fraction.Arithmetic.normalizedNeg source) ≤
      normalizedNegBitBudget source := by
  unfold rationalRecordWidth reducedFractionWidth
    normalizedNegBitBudget
  rw [Fraction.Arithmetic.ofRational_normalizedNeg]
  exact BitWidth.natWidth_mono
    (Fraction.Resource.Components.componentMagnitude_neg_le _)
end Purelib.Data.Rat.Fraction.Resource.Width

end

section
@[expose] public section

/-!
# Explicit arithmetic envelopes for RFAP-II

This module bounds the finite post-processing performed in the second RFAP
paper.  It covers the square-threshold request, displayed grid record,
homogeneous Gaussian-integer evaluation, and finite Hurwitz recursion.  The
eliminant, Sturm, and repeated-subdivision costs used to produce the imported
RFAP-I Newton state are deliberately outside this module.
-/

namespace Purelib.Data.Rat.Fraction.Resource.Width

open Purelib.Data.Nat in
open Purelib.Data.Rat in
/-- The width of the normalized difference is bounded by its computed bit budget. -/
theorem normalizedSub_width_le_budget (left right : Fraction.Rational) :
    rationalRecordWidth
        (Fraction.Arithmetic.normalizedSub left right) ≤
      normalizedSubBitBudget left right := by
  unfold rationalRecordWidth reducedFractionWidth
    normalizedSubBitBudget
  rw [Fraction.Arithmetic.ofRational_normalizedSub]
  exact BitWidth.natWidth_mono
    (Fraction.Resource.Components.componentMagnitude_sub_le _ _)
end Purelib.Data.Rat.Fraction.Resource.Width

end
