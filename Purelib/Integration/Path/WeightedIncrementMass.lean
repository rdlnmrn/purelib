module
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Data.Rat.Fraction.Compatibility
public import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.Riemann.Readings.AffineBasisEnergy
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Vector.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Gaussian.Basic
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

@[expose] public section

/-! Homogeneous mass bounds for coefficient-weighted increments on one
ordered mesh. Summing row masses preserves nonuniform refinement charges. -/
namespace Purelib.Integration.Path.WeightedIncrementMass

open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Data.Rat.Fraction.Compatibility
open Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianNormSqSum)
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_zero sumFin_add sumFin_congr sumFin_mul_left sumFin_sub)

open Purelib.Algebra in
open Purelib.Data.Gaussian in
open Purelib.LinearAlgebra.Gaussian in
open Purelib.Riemann.Normalization in
open Purelib.Riemann.Readings in
/-- The retained coefficient squared-norm sum is nonnegative. -/
private theorem coefficient_nonnegative {count : Nat} (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector
  count) :
    0 ≤ PreparedObservationCoercivity.coefficientNormSq coefficients := FiniteSum.Fin.sumFin_zero.symm.trans_le
  (FiniteSum.Rational.Order.Positivity.sumFin_mono (fun _ => (0 : InverseRootPolynomial.Coordinate)) _ (fun row =>
    Basic.Canonical.normSq_nonneg (coefficients row)))

open Purelib.Algebra in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.LinearAlgebra.Gaussian in
open Purelib.Riemann.Normalization in
open Purelib.Riemann.Readings in
/-- Bound the original weighted readings' norm mass by coefficient energy, basis count and separate row masses.

The same original entry list and coefficient family appear on both sides, preserving row ownership and finite order. -/
private theorem weighted_sum_bound {α : Type} {count : Nat} (entries : List α)
    (values : α → Fin count → InverseRootPolynomial.Gaussian) (coefficients :
      LinearAlgebra.Gaussian.Energy.GaussianVector count) :
    Norm.Sum.Basic.gaussianNormSqSum (entries.map (fun entry => FiniteSum.Fin.sumFin (fun row => coefficients row *
      values entry row))) ≤
      PreparedObservationCoercivity.coefficientNormSq coefficients * (count : InverseRootPolynomial.Coordinate) *
        FiniteSum.Fin.sumFin (fun row => Norm.Sum.Basic.gaussianNormSqSum (entries.map (fun entry => values entry row)))
          := by
  induction entries with
  | nil =>
      change (0 : InverseRootPolynomial.Coordinate) ≤ PreparedObservationCoercivity.coefficientNormSq coefficients *
        (count : InverseRootPolynomial.Coordinate) * FiniteSum.Fin.sumFin (fun _ : Fin count => (0 :
        InverseRootPolynomial.Coordinate))
      rw [FiniteSum.Fin.sumFin_zero, Fraction.Field.mul_zero_direct]
  | cons entry entries ih =>
      have head := (AffineBasisEnergy.WeightedNormBudget.build (values entry)).bound coefficients
      rw [(AffineBasisEnergy.WeightedNormBudget.build (values entry)).scale_eq] at head
      have entryNorms : sumFin (fun row => Data.Gaussian.Norm.Basic.normSq (values entry row)) =
          sumFin (fun row => normSq (values entry row)) :=
        sumFin_congr (fun row => Norm.Basic.normSq_eq_canonical (values entry row))
      rw [Norm.Basic.normSq_eq_canonical, entryNorms] at head
      have total := Fraction.Order.Arithmetic.add_le_add_direct head ih
      have split : FiniteSum.Fin.sumFin (fun row => Norm.Sum.Basic.gaussianNormSqSum ((entry :: entries).map (fun entry
        => values entry row))) =
          sumFin (fun row => normSq (values entry row)) +
            FiniteSum.Fin.sumFin (fun row => Norm.Sum.Basic.gaussianNormSqSum (entries.map (fun entry => values entry
              row))) := by
        calc
          _ = sumFin (fun row => normSq (values entry row) +
              gaussianNormSqSum (entries.map (fun remaining => values remaining row))) :=
            sumFin_congr (fun row => rfl)
          _ = _ := sumFin_add _ _
      change normSq _ + Norm.Sum.Basic.gaussianNormSqSum _ ≤ _
      rw [split]
      exact total.trans_eq (by ring1)

open Purelib.Algebra in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Integration.Path in
open Purelib.LinearAlgebra.Gaussian in
open Purelib.Riemann.Normalization in
open Purelib.Riemann.Readings in
/-- Original row mass budgets bound the count-weighted mass of their coefficient-weighted readings.

The original entry count remains in each mass, and the coefficient norm factor multiplies the retained basis count times
the row-budget sum. -/
theorem weighted_increment_mass {α : Type} {count : Nat} (entries : List α)
    (values : α → Fin count → InverseRootPolynomial.Gaussian) (coefficients :
      LinearAlgebra.Gaussian.Energy.GaussianVector count)
    (bounds : Fin count → InverseRootPolynomial.Coordinate)
    (bounded : ∀ row, (entries.length : InverseRootPolynomial.Coordinate) *
      Norm.Sum.Basic.gaussianNormSqSum (entries.map (fun entry => values entry row)) ≤ bounds row) :
    (entries.length : InverseRootPolynomial.Coordinate) *
        Norm.Sum.Basic.gaussianNormSqSum (entries.map (fun entry => FiniteSum.Fin.sumFin (fun row => coefficients row *
          values entry row))) ≤
      PreparedObservationCoercivity.coefficientNormSq coefficients * ((count : InverseRootPolynomial.Coordinate) *
        FiniteSum.Fin.sumFin bounds) := by
  have mass := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (WeightedIncrementMass.weighted_sum_bound
    entries values coefficients)
    (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le entries.length))
  have rows := FiniteSum.Rational.Order.Positivity.sumFin_mono _ _ bounded
  rw [FiniteSum.Fin.sumFin_mul_left] at rows
  have paid := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct rows
    (Fraction.Order.Arithmetic.mul_nonneg_direct (WeightedIncrementMass.coefficient_nonnegative coefficients)
      (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le count)))
  exact mass.trans ((show (entries.length : InverseRootPolynomial.Coordinate) *
    (PreparedObservationCoercivity.coefficientNormSq coefficients * (count : InverseRootPolynomial.Coordinate) *
      FiniteSum.Fin.sumFin (fun row => Norm.Sum.Basic.gaussianNormSqSum (entries.map (fun entry => values entry row))))
        =
      (PreparedObservationCoercivity.coefficientNormSq coefficients * (count : InverseRootPolynomial.Coordinate)) *
        ((entries.length : InverseRootPolynomial.Coordinate) * FiniteSum.Fin.sumFin (fun row =>
          Norm.Sum.Basic.gaussianNormSqSum (entries.map (fun entry => values entry row)))) by ring1).trans_le
    (paid.trans_eq (by ring1)))

end Purelib.Integration.Path.WeightedIncrementMass
