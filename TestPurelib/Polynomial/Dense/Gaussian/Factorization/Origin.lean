module

public import Purelib.Polynomial.Dense.Gaussian.Factorization.Origin
import Purelib.Polynomial.Dense.Gaussian.Bounds.Origin
import Purelib.Approximation.Gaussian.Sequence.Equivalence.Power
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Data.Gaussian.Power
import Purelib.Data.Gaussian.Field
import Purelib.System.IO

/-! # Exact origin-power data and original finite comparison requests -/

namespace TestPurelib.Polynomial.Dense.Gaussian.Factorization.Origin

open Purelib
open Purelib.Polynomial
open Purelib.Polynomial.Dense.Gaussian
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Approximation.Gaussian

/-- The same exact zero sample program meets every positive natural power bound at all finite indices. -/
private theorem zeroPowerBound (degree : Nat) (positive : 0 < degree) (index : Nat) :
    normSq ((Sequence.Constant.constantApproximation 0).sample index - 0) ^ degree ≤
      Approximation.Rational.Geometric.Basic.quarterRadius 0 index := by
  change normSq ((0 : Canonical) - 0) ^ degree ≤ _
  rw [Purelib.Data.Gaussian.Basic.sub_self, Purelib.Data.Gaussian.Norm.Basic.normSq_zero,
    zero_pow (Nat.ne_of_gt positive)]
  exact Approximation.Rational.Geometric.Basic.quarterRadius_nonneg (by decide) index

/-- Execute the original independent starts three and seven at squared tolerance one sixteenth. -/
private def checkPower : IO Unit := do
  let source := Sequence.Constant.constantApproximation 0
  let equivalent := Sequence.Equivalence.Power.constant_after source 0 3 (by decide) 2 0 (by decide)
    (fun index _ => zeroPowerBound 3 (by decide) index)
  let compared := equivalent.compare 3 7 (1/16) (by decide)
  unless 3 ≤ compared.leftIndex && 7 ≤ compared.rightIndex do
    throw (IO.userError "power comparison changed an original independent starting index")
  unless normSq (source.sample compared.leftIndex - 0) < (1/16 : Rational) do
    throw (IO.userError "power comparison did not pay its actual original request")
  System.IO.println s!"power comparison: starts3/7 target1/16 returned{compared.leftIndex}/{compared.rightIndex}"
  (← IO.getStdout).flush

/-- Check complete original coefficient factorization and retained near-origin floors in native code. -/
public def profile (polynomial : CoefficientPolynomial) (nonzero : polynomial.isZero = false) : IO Unit := do
  let factorization := Factorization.Origin.prepare polynomial nonzero
  let neighborhood := Bounds.Origin.prepare factorization.cofactor factorization.originNonzero
  for point in [(0 : Canonical), 1, ⟨0, 1⟩, ⟨1/16, 0⟩] do
    unless polynomial.eval point = factorization.cofactor.eval point * point ^ factorization.order do
      throw (IO.userError "origin factorization changed an original polynomial evaluation")
    if normSq point ≤ neighborhood.radiusSq then
      unless neighborhood.lower ≤ normSq (factorization.cofactor.eval point) do
        throw (IO.userError "origin neighborhood failed its same-cofactor norm floor")
  System.IO.println s!"origin data: originalDegree={polynomial.natDegree} order={factorization.order} \
    cofactorDegree={factorization.cofactor.natDegree}; exact evaluations and retained floor agree"
  (← IO.getStdout).flush
  checkPower

end TestPurelib.Polynomial.Dense.Gaussian.Factorization.Origin
