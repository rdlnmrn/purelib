module
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Algebra.Field.Resource.Magnitude
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Basic
public import Purelib.Data.Rat.Fraction.Resource.Components
import Purelib.Data.Nat.Order
import Purelib.Algebra.Group.Negation

import Mathlib.Data.Nat.Basic

open Purelib.Algebra

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

namespace Purelib.Data.Rat.Fraction.Resource.Model

open Purelib.Data.Rat

open Purelib.Data
open Purelib.Data.Rat.Fraction.Resource

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K] [DecidableEq K]

/-! ## Concrete normalized coefficient models -/

open Purelib.Data.Rat in
/-- Combine the input bound and both binary arithmetic envelopes into one natural resource bound.

Take the maximum of the input magnitude bound, twice its square and its square. Retaining the input term makes the
envelope expansive even at small bounds. -/
def rationalOperationEnvelope (bound : Nat) : Nat :=
  max bound (max
    (Components.additiveMagnitudeEnvelope bound bound)
    (Components.multiplicativeMagnitudeEnvelope bound bound))

/-- Increasing the input magnitude cannot decrease its arithmetic envelope.

The envelope retains the input and the original addition and multiplication
envelopes, each monotone in both retained input bounds. -/
theorem rationalOperationEnvelope_mono {left right : Nat}
    (order : left ≤ right) :
    rationalOperationEnvelope left ≤ rationalOperationEnvelope right := by
  unfold rationalOperationEnvelope
  exact Nat.Order.max_le_max order (Nat.Order.max_le_max
    (Components.additiveMagnitudeEnvelope_mono order order)
    (Components.multiplicativeMagnitudeEnvelope_mono order order))

/-- Component magnitudes bound the operations on reduced rational displays.

The model retains the original component maximum and operation envelope.
Its certificates bound the actual reduction-aware arithmetic operations. -/
def rationalModel : Field.Resource.Magnitude.MagnitudeModel
  Fraction.Basic.ReducedFraction where
  magnitude := Components.NormalizedFraction.componentMagnitude
  operationEnvelope := rationalOperationEnvelope
  expansive := fun bound => Nat.Order.le_max_left _ _
  monotone := rationalOperationEnvelope_mono
  add_le := by
    intro left right bound leftLe rightLe
    exact (Components.componentMagnitude_add_le_magnitudeEnvelope left right).trans
      ((Components.additiveMagnitudeEnvelope_mono leftLe rightLe).trans
        ((Nat.Order.le_max_left _ _).trans (Nat.Order.le_max_right _ _)))
  neg_le := by
    intro source bound sourceLe
    exact (Components.componentMagnitude_neg_le source).trans
      (sourceLe.trans (Nat.Order.le_max_left _ _))
  sub_le := by
    intro left right bound leftLe rightLe
    exact (Components.componentMagnitude_sub_le left right).trans
      ((Components.additiveMagnitudeEnvelope_mono leftLe rightLe).trans
        ((Nat.Order.le_max_left _ _).trans (Nat.Order.le_max_right _ _)))
  mul_le := by
    intro left right bound leftLe rightLe
    exact (Components.componentMagnitude_mul_le_magnitudeEnvelope left right).trans
      ((Components.multiplicativeMagnitudeEnvelope_mono leftLe rightLe).trans
        ((Nat.Order.le_max_right _ _).trans (Nat.Order.le_max_right _ _)))
  inv_le := by
    intro source bound sourceLe
    exact (Components.NormalizedFraction.componentMagnitude_inv_le source).trans
      (sourceLe.trans (Nat.Order.le_max_left _ _))
  div_le := by
    intro left right bound leftLe rightLe
    exact (Components.componentMagnitude_div_le left right).trans
      ((Components.multiplicativeMagnitudeEnvelope_mono leftLe rightLe).trans
        ((Nat.Order.le_max_right _ _).trans (Nat.Order.le_max_right _ _)))
end Purelib.Data.Rat.Fraction.Resource.Model

end

section
/-!
# Resource bounds for safe cuts, winding, and subdivision

The bounds in this file are computed from displayed endpoint records, the
displayed elimination degree, and the requested finite depth.  Safe-cut
coordinates are produced through the normalized rational layer.  The
recurrence therefore bounds the canonical numerator and denominator retained
at every subdivision round, rather than merely the quotient value.
-/

@[expose] public section

namespace Purelib.Data.Rat.Fraction.Resource.Model

open Purelib.Data.Rat in
/-- Read a canonical rational's component magnitude through its exact reduced representative. -/
def coordinateMagnitude (source : Fraction.Rational) : Nat :=
  Fraction.Resource.Model.rationalModel.magnitude (Fraction.Basic.ofRational source)

end Purelib.Data.Rat.Fraction.Resource.Model

end

namespace Purelib.Data.Rat.Fraction.Resource.Model

open Purelib.Data.Rat

/-- One resource-envelope step bounds normalized addition of coordinates whose magnitudes satisfy the common input
bound. -/
public theorem normalizedAdd_le {left right :
  Fraction.Rational} {bound : Nat}
    (leftBound : coordinateMagnitude left ≤ bound)
    (rightBound : coordinateMagnitude right ≤ bound) :
    coordinateMagnitude (Fraction.Arithmetic.normalizedAdd left right) ≤
      Field.Resource.Magnitude.grow rationalModel bound 1 := by
  unfold coordinateMagnitude
  rw [Fraction.Arithmetic.ofRational_normalizedAdd]
  exact Fraction.Resource.Model.rationalModel.add_le leftBound rightBound

/-- One resource-envelope step bounds normalized subtraction of coordinates whose magnitudes satisfy the common input
bound. -/
public theorem normalizedSub_le {left right :
  Fraction.Rational} {bound : Nat}
    (leftBound : coordinateMagnitude left ≤ bound)
    (rightBound : coordinateMagnitude right ≤ bound) :
    coordinateMagnitude (Fraction.Arithmetic.normalizedSub left right) ≤
      Field.Resource.Magnitude.grow rationalModel bound 1 := by
  unfold coordinateMagnitude
  rw [Fraction.Arithmetic.ofRational_normalizedSub]
  exact Fraction.Resource.Model.rationalModel.sub_le leftBound rightBound

/-- One resource-envelope step bounds normalized multiplication of coordinates whose magnitudes satisfy the common input
bound. -/
public theorem normalizedMul_le {left right :
  Fraction.Rational} {bound : Nat}
    (leftBound : coordinateMagnitude left ≤ bound)
    (rightBound : coordinateMagnitude right ≤ bound) :
    coordinateMagnitude (Fraction.Arithmetic.normalizedMul left right) ≤
      Field.Resource.Magnitude.grow rationalModel bound 1 := by
  unfold coordinateMagnitude
  rw [Fraction.Arithmetic.ofRational_normalizedMul]
  exact Fraction.Resource.Model.rationalModel.mul_le leftBound rightBound

/-- One resource-envelope step bounds normalized division of coordinates whose magnitudes satisfy the common input
bound. -/
public theorem normalizedDiv_le {left right :
  Fraction.Rational} {bound : Nat}
    (leftBound : coordinateMagnitude left ≤ bound)
    (rightBound : coordinateMagnitude right ≤ bound) :
    coordinateMagnitude (Fraction.Arithmetic.normalizedDiv left right) ≤
      Field.Resource.Magnitude.grow rationalModel bound 1 := by
  unfold coordinateMagnitude
  rw [Fraction.Arithmetic.ofRational_normalizedDiv]
  exact Fraction.Resource.Model.rationalModel.div_le leftBound rightBound

end Purelib.Data.Rat.Fraction.Resource.Model
