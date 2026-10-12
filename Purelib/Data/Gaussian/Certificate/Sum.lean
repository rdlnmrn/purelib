module
public import Purelib.Algebra.FiniteSum.Fin
import Purelib.Data.Gaussian.Basic
public import Purelib.Data.Gaussian.Certificate.Raw

open Purelib.Algebra.FiniteSum

open Purelib.Data

open Purelib.Data.Gaussian.Certificate

open Purelib.Data.Gaussian.Certificate.Raw

/-!
# Ordered finite sums of displayed Gaussian fractions

Four-term and eight-term sums retain the increasing input order and original
right-associated additions. Exact readback identifies each displayed aggregate
with the finite sum of those same canonical Gaussian values.
-/

@[expose] public section

namespace Purelib.Data.Gaussian.Certificate.Sum

/-- Add eight displayed Gaussian fractions in increasing index order.

The right-associated expression retains every original displayed coordinate fraction
and performs exact fraction addition without changing the input order. -/
def sumEight
    (values : Fin 8 ->
      GaussianData) :
    GaussianData :=
  (values 0).add ((values 1).add ((values 2).add ((values 3).add
    ((values 4).add ((values 5).add ((values 6).add (values 7)))))))

/-- Reading the displayed eight-term aggregate gives the finite sum of the original
canonical Gaussian values.

The retained eight readings keep their increasing index order, with the same nested Gaussian additions as the finite
sum. -/
theorem sumEight_toGaussian
    (values : Fin 8 ->
      GaussianData) :
    (sumEight values).toGaussian =
      Fin.sumFin
        (fun index => (values index).toGaussian) := by
  rw [Fin.sumFin_succ,
    Fin.sumFin_succ,
    Fin.sumFin_succ,
    Fin.sumFin_succ,
    Fin.sumFin_succ,
    Fin.sumFin_succ,
    Fin.sumFin_succ,
    Fin.sumFin_succ]
  change (sumEight values).toGaussian =
    (values 0).toGaussian + ((values 1).toGaussian +
      ((values 2).toGaussian + ((values 3).toGaussian +
        ((values 4).toGaussian + ((values 5).toGaussian +
          ((values 6).toGaussian + ((values 7).toGaussian + 0)))))))
  unfold sumEight
  simp only [
    GaussianData.add_toGaussian,
    Gaussian.Basic.add_zero, -eq_self, -iff_self]
  rfl

/-- Add four displayed Gaussian fractions in increasing index order.

The right-associated expression retains every original displayed coordinate fraction
and performs exact fraction addition without changing the input order. -/
def
  sumFour
    (values : Fin 4 → GaussianData) : GaussianData :=
  (values 0).add ((values 1).add ((values 2).add (values 3)))

/-- Reading the displayed four-term aggregate gives the finite sum of the original
canonical Gaussian values.

The retained four readings keep their increasing index order, with the same nested Gaussian additions as the finite sum.
-/
theorem
  sumFour_toGaussian
    (values : Fin 4 → GaussianData) :
    (sumFour values).toGaussian =
      Fin.sumFin
        (fun index => (values index).toGaussian) := by
  rw [Fin.sumFin_succ,
    Fin.sumFin_succ,
    Fin.sumFin_succ,
    Fin.sumFin_succ]
  change (sumFour values).toGaussian =
    (values 0).toGaussian + ((values 1).toGaussian +
      ((values 2).toGaussian + ((values 3).toGaussian + 0)))
  unfold sumFour
  simp only [GaussianData.add_toGaussian,
    Gaussian.Basic.add_zero, -eq_self, -iff_self]
  rfl

end Purelib.Data.Gaussian.Certificate.Sum
