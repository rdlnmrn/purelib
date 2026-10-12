module
import Purelib.Data.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Decomposition
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Power
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Positive
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Decomposition.Basic
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Build
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Part

open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Polynomial.Dense.Gaussian.Multiplicity (Basis)
open Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Positive (PositiveEntry)
open Purelib.Polynomial.Dense.Gaussian.Squarefree (Decomposition)

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Polynomial

section
@[expose] public section

/-!
# Residual bounds for finite multiplicity bases

The exact multiplicity basis gives two complementary finite statements.
First, a sufficiently small residual of the original polynomial selects at
least one displayed squarefree basis factor with small residual.  Second, for
a preselected factor, an explicit positive lower bound on the remaining
unit/cofactor product transfers its residual bound back to the original
polynomial in an integer-power form.

No rational root, real exponent, root collection, or completed value occurs:
all powers are natural powers of displayed rational quadrances.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Multiplicity.Residual.Basic

/-- Total number of displayed squarefree occurrences, counting positive
multiplicity. -/
def multiplicityCount : List
  PositiveEntry → Nat
  | [] => 0
  | entry :: entries => entry.multiplicity +
    multiplicityCount entries

/-- Squared norm of the finite weighted product is the product of the
displayed factor residual quadrances. -/
theorem normSq_positiveValue : ∀ (entries : List
  PositiveEntry)
    (point : Gaussian.Basic.Canonical),
    Data.Gaussian.Norm.Basic.normSq (Basis.Positive.positiveValue entries point) =
      match entries with
      | [] => 1
      | entry :: tail =>
          Data.Gaussian.Norm.Basic.normSq (entry.part.polynomial.eval point) ^ entry.multiplicity *
            Data.Gaussian.Norm.Basic.normSq (Basis.Positive.positiveValue tail point)
  | [], point => by
      simp only [-eq_self, -iff_self, Basis.Positive.positiveValue,
        Gaussian.Norm.Basic.normSq_one]
      rfl
  | entry :: entries, point => by
      rw [Basis.Positive.positiveValue, Gaussian.Norm.Basic.normSq_mul,
        Purelib.Data.Gaussian.Power.normSq_pow]

/-- If every displayed factor residual is at least `delta`, the whole finite
weighted product is at least `delta` to the total multiplicity. -/
theorem power_le_normSq_positiveValue_of_all
    (delta : Fraction.Rational) (deltaNonnegative : 0 ≤ delta) :
    ∀ (entries : List PositiveEntry) (point : Gaussian.Basic.Canonical),
      (∀ entry ∈ entries,
        delta ≤ Data.Gaussian.Norm.Basic.normSq (entry.part.polynomial.eval point)) →
      delta ^ multiplicityCount entries ≤
        Data.Gaussian.Norm.Basic.normSq (Basis.Positive.positiveValue entries point)
  | [], point, _ => by
      simp only [multiplicityCount, pow_zero,
        Basis.Positive.positiveValue, Gaussian.Norm.Basic.normSq_one]
      exact le_rfl
  | entry :: entries, point, lower => by
      have headLower := lower entry (List.mem_cons_self)
      have headPower : delta ^ entry.multiplicity ≤
          Data.Gaussian.Norm.Basic.normSq (entry.part.polynomial.eval point) ^ entry.multiplicity :=
        Fraction.Order.Arithmetic.pow_le_pow_direct deltaNonnegative
          headLower entry.multiplicity
      have tailLower :=
        power_le_normSq_positiveValue_of_all delta
        deltaNonnegative entries point (fun tail member =>
          lower tail (List.mem_cons_of_mem entry member))
      rw [multiplicityCount, pow_add,
        normSq_positiveValue]
      exact Fraction.Order.Arithmetic.mul_le_mul_direct headPower tailLower
        (Fraction.Order.Arithmetic.pow_nonneg_direct deltaNonnegative
          (multiplicityCount entries))
        (Fraction.Order.Arithmetic.pow_nonneg_direct
          (Gaussian.Norm.Basic.normSq_nonneg (entry.part.polynomial.eval point))
          entry.multiplicity)

/-- Squared norm of the omitted degree-zero unit. -/
def unitQuadrance {p :
  CoefficientPolynomial}
    (decomposition : Decomposition p) : Fraction.Rational :=
  Data.Gaussian.Norm.Basic.normSq (Basis.Positive.unitValue
    decomposition.multiplicityBasis.entries)

/-- The squared norm of the retained nonzero scalar unit is strictly positive. -/
theorem unitQuadrance_pos {p :
  CoefficientPolynomial}
    (decomposition : Decomposition p) :
    0 < unitQuadrance decomposition :=
  Gaussian.Norm.Basic.normSq_pos decomposition.multiplicityUnit_ne_zero

/-- Exact residual product identity for the displayed multiplicity basis. -/
theorem residual_product_identity
    {p : CoefficientPolynomial} (decomposition :
      Decomposition p)
    (point : Gaussian.Basic.Canonical) :
    Data.Gaussian.Norm.Basic.normSq (p.eval point) = unitQuadrance
      decomposition *
      Data.Gaussian.Norm.Basic.normSq (Basis.Positive.positiveValue
        decomposition.positiveMultiplicityEntries
        point) := by
  rw [decomposition.eval_positiveMultiplicityEntries point, Gaussian.Norm.Basic.normSq_mul]
  rfl
end Purelib.Polynomial.Dense.Gaussian.Multiplicity.Residual.Basic

end
