module

import Purelib.Polynomial.Dense.Gaussian.Interpolation
import Purelib.Polynomial.Dense.Leading
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic

/-!
# Original synthetic interpolation regressions

Two displayed separated nodes bound an affine polynomial throughout the
rational unit disk. The same materialized expansion retains both original
synthetic quotients in their actual order.
-/

namespace TestPurelib.Polynomial.Dense.Gaussian.Interpolation

open Purelib
open Data.Gaussian.Basic (Canonical)
open Polynomial.Dense.Gaussian
open Basic.CanonicalCoefficients (CoefficientPolynomial)
open Data.Rat.Fraction (Rational)
open Data.Rat.Fraction.Order

/-- The original descending affine coefficient table. -/
private def polynomial : CoefficientPolynomial := ⟨[1, -1]⟩

/-- Two distinct ordered rational Gaussian nodes. -/
private def nodes : List Canonical := [0, 2]

/-- The actual first synthetic division retains the original leading coefficient. -/
private theorem first_quotient : (Interpolation.Expansion.prepare polynomial nodes).first.quotient.coeffs = [1] := by
  decide +kernel

/-- The stored second division consumes that same retained constant quotient. -/
private theorem second_remainder : (Interpolation.Expansion.prepare polynomial nodes).next.first.remainder = 1 := by
  decide +kernel

/-- The exact finite amplification is computed from both original node bounds. -/
private theorem amplification_two : Interpolation.amplification 4 4 2 = 42 := by decide +kernel

/-- Equal original quadratic leading terms cancel before the interpolation slot count is read. -/
private theorem cancellation_slots :
    ((⟨[1, 2, 3]⟩ : Basic.CanonicalCoefficients.CoefficientPolynomial) - ⟨[1, 4, 5]⟩).degreeCount ≤ 2 := by
  exact (Polynomial.Dense.Leading.LeadingTerm.sub_same
    (p := (⟨[1, 2, 3]⟩ : Basic.CanonicalCoefficients.CoefficientPolynomial))
    (q := (⟨[1, 4, 5]⟩ : Basic.CanonicalCoefficients.CoefficientPolynomial))
    (degree := 2) (coefficient := 1)
    ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩
    ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩).count_le

/-- The original two-node sample residuals control every rational point in the unit disk. -/
private theorem disk_bound (point : Canonical) (unitDisk : Data.Gaussian.Norm.Basic.normSq point ≤ 1) :
    Data.Gaussian.Norm.Basic.normSq (polynomial.eval point) ≤
      (1 : Data.Rat.Fraction.Rational) * Interpolation.amplification 4 4 2 := by
  apply Interpolation.Expansion.normSq_eval_le (Interpolation.Expansion.prepare polynomial nodes)
    (by decide) (by decide) (by decide) (by decide)
  · intro node member
    cases member with
    | head => decide +kernel
    | tail _ member =>
        cases member with
        | head => decide +kernel
        | tail _ impossible => nomatch impossible
  · apply List.Pairwise.cons
    · intro node member
      cases member with
      | head => decide +kernel
      | tail _ impossible => nomatch impossible
    · exact List.Pairwise.cons (fun _ impossible => nomatch impossible) List.Pairwise.nil
  · intro node member
    cases member with
    | head => decide +kernel
    | tail _ member =>
        cases member with
        | head => decide +kernel
        | tail _ impossible => nomatch impossible
  · exact unitDisk

/-- Every actual retained first quotient has the same sufficient tail residual budget without a replacement scan. -/
private theorem retained_tail_residual {source : CoefficientPolynomial}
    {head : Canonical} {remaining : List Canonical}
    (expansion : Interpolation.Expansion source (head :: remaining))
    {separation residual : Rational} (positive : 0 < separation)
    (separated : (head :: remaining).Pairwise (fun left right =>
      separation ≤ Data.Gaussian.Norm.Basic.normSq (left - right)))
    (samples : ∀ point ∈ head :: remaining, Data.Gaussian.Norm.Basic.normSq (source.eval point) ≤ residual) :
    ∀ point ∈ remaining,
      Data.Gaussian.Norm.Basic.normSq (expansion.first.quotient.eval point) ≤ 4 * residual / separation :=
  expansion.next_samples_le positive separated samples

end TestPurelib.Polynomial.Dense.Gaussian.Interpolation
