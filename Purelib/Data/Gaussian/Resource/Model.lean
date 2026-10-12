module
import Purelib.Data.Nat.Order

import Purelib.Algebra.Field.ExplicitField
public import Purelib.Algebra.Field.Resource.Magnitude
import Purelib.Data.Gaussian.Basic
public import Purelib.Data.Gaussian.Resource

import Purelib.Data.Gaussian.Field
public import Mathlib.Order.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Order.MinMax

open Purelib.Data Purelib.Data.Gaussian Purelib.Algebra.Field.Resource

@[expose] public section

namespace Purelib.Data.Gaussian.Resource.Model

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K] [DecidableEq K]

/-- Retain the input bound and the envelopes for each Gaussian arithmetic operation.

The nested maximum keeps the original addition, multiplication, inversion and
division bounds alongside the input magnitude. -/
def gaussianOperationEnvelope (bound : Nat) : Nat :=
  max bound (max
    (Resource.addMagnitudeEnvelope bound bound)
    (max (Resource.mulMagnitudeEnvelope bound bound)
      (max (Resource.invMagnitudeEnvelope bound)
        (Resource.divMagnitudeEnvelope bound bound))))

/-- Increasing the input magnitude cannot decrease its Gaussian operation envelope.

Each retained arithmetic envelope is monotone in its original inputs, and
the nested natural maxima preserve those bounds. -/
theorem gaussianOperationEnvelope_mono {left right : Nat}
    (order : left ≤ right) :
    Resource.Model.gaussianOperationEnvelope left ≤ Resource.Model.gaussianOperationEnvelope right := by
  unfold Resource.Model.gaussianOperationEnvelope
  exact Nat.Order.max_le_max order (Nat.Order.max_le_max
    (Resource.addMagnitudeEnvelope_mono order order)
    (Nat.Order.max_le_max (Resource.mulMagnitudeEnvelope_mono order order)
      (Nat.Order.max_le_max (Resource.invMagnitudeEnvelope_mono order)
        (Resource.divMagnitudeEnvelope_mono order order))))

/-- Component magnitudes bound the actual Gaussian arithmetic operations.

The model retains the original coefficient magnitude and operation envelope.
Its certificates account for the same rational coordinate operations and
squared-norm denominator used by Gaussian arithmetic. -/
def gaussianModel : Magnitude.MagnitudeModel Basic.Number where
  magnitude := Resource.GaussianNormalized.componentMagnitude
  operationEnvelope := Resource.Model.gaussianOperationEnvelope
  expansive := fun bound => Nat.Order.le_max_left _ _
  monotone := Resource.Model.gaussianOperationEnvelope_mono
  add_le := by
    intro left right bound leftLe rightLe
    exact (Resource.componentMagnitude_add_le left right).trans
      ((Resource.addMagnitudeEnvelope_mono leftLe rightLe).trans
        ((Nat.Order.le_max_left _ _).trans (Nat.Order.le_max_right _ _)))
  neg_le := by
    intro source bound sourceLe
    exact (Resource.componentMagnitude_neg_le source).trans
      (sourceLe.trans (Nat.Order.le_max_left _ _))
  sub_le := by
    intro left right bound leftLe rightLe
    exact (Resource.componentMagnitude_sub_le left right).trans
      ((Resource.addMagnitudeEnvelope_mono leftLe rightLe).trans
        ((Nat.Order.le_max_left _ _).trans (Nat.Order.le_max_right _ _)))
  mul_le := by
    intro left right bound leftLe rightLe
    exact (Resource.componentMagnitude_mul_le left right).trans
      ((Resource.mulMagnitudeEnvelope_mono leftLe rightLe).trans
        ((Nat.Order.le_max_left _ _).trans ((Nat.Order.le_max_right _ _).trans (Nat.Order.le_max_right _ _))))
  inv_le := by
    intro source bound sourceLe
    exact (Resource.componentMagnitude_inv_le source).trans
      ((Resource.invMagnitudeEnvelope_mono sourceLe).trans
        ((Nat.Order.le_max_left _ _).trans ((Nat.Order.le_max_right _ _).trans
          ((Nat.Order.le_max_right _ _).trans (Nat.Order.le_max_right _ _)))))
  div_le := by
    intro left right bound leftLe rightLe
    exact (Resource.componentMagnitude_div_le left right).trans
      ((Resource.divMagnitudeEnvelope_mono leftLe rightLe).trans
        ((Nat.Order.le_max_right _ _).trans ((Nat.Order.le_max_right _ _).trans
          ((Nat.Order.le_max_right _ _).trans (Nat.Order.le_max_right _ _)))))

end Purelib.Data.Gaussian.Resource.Model
